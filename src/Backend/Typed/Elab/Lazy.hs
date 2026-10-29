-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Lazy values under evaluation as cells (right after elaboration, before `OrderFields`).

  Koka evaluates a lazy type `T` (`Kind.Infer`) with private functions that pass the lazy
  value under evaluation `@lazy : T⟨B̄⟩*` around:
  - `T/lazy-eval-locked(@lazy, recurse)` matches on `@lazy` and passes it on to `T/lazy-C`
    in the branch of each lazy constructor `C` other than the indirection;
  - `T/lazy-C(@lazy, recurse, fields)` starts with `memoize-target(@lazy, size, scan)` and
    ends every branch in `memoize(@lazy, v)` or, where Koka's sizes allow it, in a call
    `T/lazy-C'(@lazy, recurse, fields')`.
  Here the lazy value becomes a cell (`[lock]`): `lazy-eval-locked` locks it in the branch
  of each such constructor, and every `lazy-C` takes it as a cell `cell_‖V_C‖⟨T⟨ā⟩⟩`. An
  expression in the scope of a cell `c : cell_n⟨T⟨B̄⟩⟩` must consume it:
  - `memoize-target(c, …)` is deleted;
  - `memoize(c, K(v))` writes K over the cell (`[memoize]`) if K is a box with `|V_K| ≤ n`,
    and otherwise, like `memoize(c, v)` of any other value, it becomes an indirection to the
    value (`indirect`);
  - a call `lazy-C'(c, recurse, v̄)` passes the cell on if `‖V_C'‖ ≤ n` (by our sizes, which
    may differ from Koka's), and otherwise becomes an indirection to a new thunk `C'(v̄)`,
    which `lazy-whnf` goes on to evaluate;
  - a jump passes the cell on, and the parameter of the join point becomes a cell of the
    smallest size passed (Koka inlines `lazy-C` into `lazy-eval-locked` as a join point);
  - a branch without the cell is a lazy constructor in a match on a forced value, which ends
    in `unreachable` (`[unreachable]` consumes the cell).
  Any other use of a cell, and any other use of `memoize`, is an error. The functions are
  found by `Kind.Infer`'s naming (`lazyName`).

  Afterwards, `lazy-eval`, `lazy-eval-locked` and the `lazy-C` functions are specialised to
  their parameter `recurse`: each gets a WHNF copy (`recurse = True`) and a step copy
  (`False`) without the parameter, and a call with a literal `recurse` goes to its copy. In a
  copy, `recurse` is a literal, also in the parameters of join points to which Koka's match
  passes it, and the tests of it are cases of a known value (`Simplify`).
  Only `lazy-eval`, which other modules may call, remains, and dispatches to its copies. The binders of a lock have the names that
  `[lock]` requires before `Paths`: the box `y.roll.injⱼ` of the lazy value `y`, and its
  contents `y.roll.injⱼ.contents`, which the lock renames to `y.roll.injⱼ.taken`.

  Finally, forced values get the type `whnf(τ)*` (`whnfProgram`), so that their matches
  have no lazy alternatives.
-}
module Backend.Typed.Elab.Lazy( lazyProgram, lazyCopies ) where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Common.NameMap as NM
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Common.Name
import Common.NamePrim( nameLazyMemoize, nameLazyMemoizeTarget, nameLazyIsWhnf, nameLazyPtrIsWhnf )
import Kind.Newtypes
import Type.Type( lazyName, conInfoName )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Pretty( ppr )
import Backend.Typed.Query( Env(..), envOf, unrollT, reuseSize, lazySize, lazyTags, hasWhnf )

-- The `lazy-C` functions with the tag of their constructor and the size of its cell, the
-- `lazy-eval-locked` functions, the `lazy-eval` functions, the `lazy-whnf` and `lazy-force`
-- functions, and the tag of the indirection ι of each lazy type.
data Lazies = Lazies{ lzCons :: M.Map Name (Int,Int), lzLocked :: S.Set Name, lzEval :: S.Set Name, lzForce :: S.Set Name
                    , lzIndirect :: M.Map Name Int }

-- the lazy value of `lazy-eval-locked` and its type
data LEnv = LEnv{ leEnv :: Env, leLazies :: Lazies, leLocked :: Maybe (Path,AType) }

-- fresh names, and the smallest cell passed to each parameter of a join point
type L a = M LEnv (NameSupply, M.Map Name (M.Map Int Int)) a

-- the cells that an expression consumes, with their size and type
type Cells = M.Map Path (Int,AType)

fresh :: String -> L Path
fresh s = state (\(ns,js) -> let (x,ns') = freshPathFrom ("lz" ++ s) ns in (x,(ns',js)))

lazyProgram :: Newtypes -> Program -> (Program,[String])
lazyProgram nt prog
  = let lazies = lazyFuns nt (progTypes prog)
        env    = envOf prog
        run d  = case evalM (lazyDef d) (LEnv env lazies Nothing) (freshFor d, M.empty) of
                   Right d' -> (d', [])
                   Left err -> (d, [show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs prog))
        cells  = M.fromList [(f,c) | DefFun f _ ((_,_,c@VCell{}):_) _ _ <- defs]
    in (whnfProgram lazies (specialise lazies prog{ progDefs = defs, progSigs = M.mapWithKey (withCell cells) (progSigs prog) }), concat errs)
  where
    withCell cells f sig
      = case (M.lookup f cells, sig) of
          (Just c, SigFun tvs ((m,_):ps) r) -> SigFun tvs ((m,c):ps) r
          _ -> sig

lazyFuns :: Newtypes -> TypeDefs -> Lazies
lazyFuns nt tdefs
  = Lazies (M.fromList [(funName info (show (unqualify (conInfoName con))), (tag,n))
                       | (info,lz,alts) <- infos, (tag,con) <- cons info
                       , tag `elem` lz, not (isLazyIndirectConName (conInfoName con))
                       , Just (ABox s) <- [lookup tag alts], Right n <- [lazySize s]])
           (S.fromList [funName info "eval-locked" | (info,_,_) <- infos])
           (S.fromList [funName info "eval" | (info,_,_) <- infos])
           (S.fromList [funName info stem | (info,_,_) <- infos, stem <- ["whnf","force"]])
           (M.fromList [(dataInfoName info, tag) | (info,_,_) <- infos, (tag,con) <- cons info, isLazyIndirectConName (conInfoName con)])
  where
    env = Env tdefs M.empty
    cons info = zip [1..] (dataInfoConstrs info)   -- tags start at 1
    infos = [(info,lz,alts) | (_,info) <- NM.toList (newtypesTypeDefs nt)
                            , Just TypeDef{ tdefParams = tvs } <- [M.lookup (dataInfoName info) tdefs]
                            , let t = ACon (dataInfoName info) (map AVar tvs)
                            , let lz = lazyTags env t, not (null lz)
                            , Right (ASum alts) <- [unrollT env t]]
    funName info stem = qualify (qualifier (dataInfoName info)) (lazyName info stem)

-- the functions with a parameter `recurse`
recursing :: Lazies -> [Name]
recursing lazies = M.keys (lzCons lazies) ++ S.toList (lzLocked lazies) ++ S.toList (lzEval lazies)

-- the copy of a function for a value of `recurse`
copyName :: Bool -> Name -> Name
copyName recurse = makeHiddenName (if recurse then "whnf" else "step")

-- the copies of the functions with a parameter `recurse`, with their original and the value
-- of `recurse`
lazyCopies :: Newtypes -> TypeDefs -> [(Name,(Name,Bool))]
lazyCopies nt tdefs = [(copyName b f,(f,b)) | f <- recursing (lazyFuns nt tdefs), b <- [False,True]]

-- the first parameter of a `lazy-C` function is the cell of its constructor, and the first
-- parameter of `lazy-eval-locked` is the lazy value that it locks
lazyDef :: Def -> L Def
lazyDef def
  = do lazies <- asks leLazies
       case def of
         DefFun f tvs ((x,m,t):ps) res body
           | Just (_,n) <- M.lookup f (lzCons lazies)
           -> case t of
                VPtr a | targets x body -> DefFun f tvs ((x,m,VCell n a):ps) res <$> cellE (M.singleton x (n,a)) body
                _ -> fail ("a lazy constructor function without a memoization target: " ++ show x)
           | S.member f (lzLocked lazies), VPtr a <- t
           -> DefFun f tvs ((x,m,t):ps) res <$> local (\le -> le{ leLocked = Just (x,a) }) (cellE M.empty body)
         _ -> (\body -> def{ defBody = body }) <$> cellE M.empty (defBody def)
  where
    targets x body = case body of
                       Let _ _ (Call g _ (Var y : _)) _ -> g == nameLazyMemoizeTarget && y == x
                       _ -> False

-- An expression that consumes the cells `cs` (see the top).
cellE :: Cells -> VExpr -> L VExpr
cellE _ expr@Unreachable{}
  = return expr
cellE cs expr
  | (c:_) <- [c | c <- M.keys cs, S.notMember c (fvE expr)]
  = fail ("the cell " ++ show c ++ " is not filled")
cellE cs expr
  = do locked <- asks leLocked
       cons <- asks (lzCons . leLazies)
       case expr of
         Deref m (Var x) y (Unroll m' y' z (CaseA m'' z' alts def))
           | Just (x',a) <- locked, x == x', y' == y, z' == z, M.null cs
           -> do (lz,ind) <- lazyOf a
                 shapes <- altsOf a
                 let r = child y SRoll
                     lockAlt (i,b,e)
                       | i `elem` lz, i /= ind, Just (ABox s) <- lookup i shapes
                       = do n <- liftE (lazySize s)
                            c <- fresh "cell"
                            (,,) i (child r (SInjA i)) <$> lock (x,c,n,a) (child r (SInjA i)) b e
                       | otherwise = (,,) i b <$> cellE cs e
                 alts' <- mapM lockAlt alts
                 def' <- traverse (\(d,e) -> (,) d <$> cellE cs e) def
                 return (Deref m (Var x) y (Unroll m' y r (CaseA m'' r alts' def')))
         Let _ _ (Call f _ (Var c : _)) e
           | f == nameLazyMemoizeTarget, M.member c cs -> cellE cs e
         Call f _ [Var c, v]
           | f == nameLazyMemoize, Just (n,a) <- M.lookup c cs, M.size cs == 1, S.notMember c (fvV v)
           -> cellV v >>= memoize c n a
         Call f ts (Var c : vs)
           | Just (k,m) <- M.lookup f cons, Just (n,a) <- M.lookup c cs, M.size cs == 1, S.notMember c (S.unions (map fvV vs))
           -> do vs' <- mapM cellV vs
                 if m <= n then return (Call f ts (Var c : vs'))
                   else do con <- conValue a k (drop 1 vs')   -- without `recurse`
                           indirect c a con
         Call f _ _
           | f == nameLazyMemoize || f == nameLazyMemoizeTarget -> fail "memoization of a value that is not under evaluation"
         Jump j ts vs
           -> do let passed = [(i,c) | (i,Var c) <- zip [0..] vs, M.member c cs]
                 if length passed /= M.size cs || not (S.disjoint (M.keysSet cs) (S.unions [fvV v | (i,v) <- zip [0..] vs, i `notElem` map fst passed]))
                   then fail ("jump to " ++ show j ++ " with a cell that is not a parameter")
                   else do modify (\(ns,js) -> (ns, M.insertWith (M.unionWith min) j (M.fromList [(i,fst (cs M.! c)) | (i,c) <- passed]) js))
                           Jump j ts <$> mapM cellV vs
         Let x t e1 e2
           -> let (cs1,cs2) = M.partitionWithKey (\c _ -> S.member c (fvE e1)) cs
              in Let x t <$> cellE cs1 e1 <*> cellE cs2 e2
         LetYield x t e1 e2 e3
           -> LetYield x t <$> cellE cs e1 <*> cellE M.empty e2 <*> cellE M.empty e3
         -- the jumps come first, and give the parameters that are cells
         Join j tvs ps e1 e2
           -> do e2' <- cellE cs e2
                 sizes <- gets (M.findWithDefault M.empty j . snd)
                 ps' <- mapM (\(i,(x,m,t)) -> case (M.lookup i sizes, t) of
                                               (Nothing,_) -> return (x,m,t)
                                               (Just n,VPtr a) -> return (x,m,VCell n a)
                                               (Just _,_) -> fail ("a cell passed to a parameter of " ++ show j ++ " that is not a pointer"))
                             (zip [0 :: Int ..] ps)
                 e1' <- cellE (M.fromList [(x,(n,a)) | (x,_,VCell n a) <- ps']) e1
                 return (Join j tvs ps' e1' e2')
         _ | not (S.disjoint (M.keysSet cs) (operands expr)) -> fail ("unexpected use of a cell in " ++ ppr expr)
           | otherwise -> descendE pure cellV (\_ e -> cellE cs e) expr
  where
    operands e = getConst (descendE (Const . S.singleton) (Const . fvV) (\_ _ -> Const S.empty) e)

-- Lock the box `z` (the binder `b`) of a lazy alternative of the lazy value `x` in `e`, whose
-- uses of `x`, `b` and the contents of `b` become uses of the cell, `z` and `z.taken`.
lock :: (Path,Path,Int,AType) -> Path -> Path -> VExpr -> L VExpr
lock (x,c,n,a) z b e
  = do let (contents,body) = case e of
                               Unbox _ b' p e' | b' == b -> ([(p,child z STaken)],e')
                               _ -> ([],e)
       body' <- cellE (M.singleton c (n,a)) (renameUses (M.fromList ((x,c) : (b,z) : contents)) body)
       return (Unbox Borrowed z (child z SContents) (Lock z c body'))

-- the lambdas in a value have no cells
cellV :: VVal -> L VVal
cellV = descendV cellA cellV

cellA :: AVal -> L AVal
cellA val
  = case val of
      Lam ps r e -> Lam ps r <$> cellE M.empty e
      _ -> descendA pure cellA cellV val

-- `memoize(c, v)`: write the constructor of `v` over the cell if it fits
memoize :: Path -> Int -> AType -> VVal -> L VExpr
memoize c n a v
  = do shapes <- altsOf a
       case v of
         Ptr _ (Roll _ (InjA k _ (Box w))) | Just (ABox s) <- lookup k shapes, Right m <- reuseSize s, m <= n
           -> return (Ret (Memoize (Var c) k w))
         _ -> indirect c a v

-- `indirect c v`: free the cell if it is unique, and otherwise write an indirection to `v` over it
indirect :: Path -> AType -> VVal -> L VExpr
indirect c a v
  = do i <- snd <$> lazyOf a
       r <- fresh "r"
       p <- fresh "p"
       return (Let r (VPtr a) (Ret v)
                (IsUnique c (Free c (Ret (Var r)))
                            (Let p (VPtr a) (Ret (Memoize (Var c) i (Var r))) (Ret (Var r)))))

-- the lazy constructor with tag k and fields v̄ at the type of a cell
conValue :: AType -> Int -> [VVal] -> L VVal
conValue a k vs
  = do shapes <- altsOf a
       case lookup k shapes of
         Just (ABox VExists{}) -> fail ("a lazy constructor with existential fields: " ++ ppr (A a))
         Just (ABox _) -> return (Ptr a (Roll a (InjA k (ASum shapes) (Box (prodVal vs)))))
         _ -> fail ("no lazy constructor " ++ show k ++ " in " ++ ppr (A a))

altsOf :: AType -> L [(Int,AType)]
altsOf a
  = do env <- asks leEnv
       b <- liftE (unrollT env a)
       case b of
         ASum shapes -> return shapes
         _ -> fail ("a lazy type that is not a sum: " ++ ppr (A a))

-- the lazy tags of a lazy type, and the tag of its indirection
lazyOf :: AType -> L ([Int],Int)
lazyOf a
  = do env <- asks leEnv
       inds <- asks (lzIndirect . leLazies)
       case a of
         ACon n _ | Just i <- M.lookup n inds -> return (lazyTags env a, i)
         _ -> fail ("not a lazy type: " ++ ppr (A a))

-- Specialise the functions of this module with a parameter `recurse` (the second, a `bool`)
-- to its value (see the top).
specialise :: Lazies -> Program -> Program
specialise lazies prog
  = prog{ progDefs = concatMap copies (progDefs prog), progSigs = M.foldrWithKey sigs (progSigs prog) (progSigs prog) }
  where
    funs = S.fromList (recursing lazies) `S.intersection` S.fromList [f | DefFun{ defName = f } <- progDefs prog]
    copies def
      = case def of
          DefFun f tvs (x:(r,m,t):ps) res body | S.member f funs
            -> [DefFun (copyName b f) tvs (x:ps) res (callsE (knownJoins (replaceE (M.singleton r (boolV t b)) body))) | b <- [False,True]]
               ++ [DefFun f tvs (x:(r,m,t):ps) res (dispatch f tvs r (x:ps)) | S.member f (lzEval lazies)]
          _ -> [def{ defBody = callsE (defBody def) }]
    sigs f sig ss
      = case sig of
          SigFun tvs (p:_:ps) res | S.member f funs
            -> (if S.member f (lzEval lazies) then id else M.delete f)
               (foldr (\b -> M.insert (copyName b f) (SigFun tvs (p:ps) res)) ss [False,True])
          _ -> ss
    boolV t b = Inj (if b then 1 else 0) t UnitV
    dispatch f tvs r ps
      = CaseV Owned (Var r) [(i, child r (SInjV i), Call (copyName b f) (map AVar tvs) [Var x | (x,_,_) <- ps]) | (i,b) <- [(0,False),(1,True)]]
    callsE expr
      = case expr of
          Call f ts (v : Inj i _ UnitV : vs) | S.member f funs -> Call (copyName (i == 1) f) ts (v:vs)
          _ -> runIdentity (descendE Identity (Identity . callsV) (\_ -> Identity . callsE) expr)
    callsV = mapV callsA callsV
    callsA a = case a of
                 Lam ps r e -> Lam ps r (callsE e)
                 _ -> mapA id callsA callsV a

-- Values in WHNF (`[if-whnf]`). A test of WHNF on a lazy value, `datatype-(ptr-)is-whnf`
-- followed by a case on its result, narrows the value in its first branch. `lazy-whnf` and
-- `lazy-force` (also those of other modules) return `whnf(T)*`, and so does a `let` whose bound
-- expression does: it is a forced value, and its matches lose their lazy alternatives, which are
-- `unreachable`. A shape that is not recognised is not narrowed.
whnfProgram :: Lazies -> Program -> Program
whnfProgram lazies prog
  = prog{ progDefs = map def (progDefs prog), progSigs = sigs }
  where
    env = envOf prog
    narrow t = case t of
                 VPtr a | hasWhnf env a -> Just (VPtr (AWhnf a))
                 _ -> Nothing
    sigs = M.mapWithKey (\f sig -> case sig of
                                     SigFun tvs ps r | S.member f (lzForce lazies), Just r' <- narrow r -> SigFun tvs ps r'
                                     _ -> sig)
                        (progSigs prog)
    def d = case d of
              DefFun f tvs ps r body | S.member f (lzForce lazies), Just r' <- narrow r -> DefFun f tvs ps r' (whnfE S.empty body)
              _ -> d{ defBody = whnfE S.empty (defBody d) }
    -- Koka's match puts join points between the test and the case on its result. The test
    -- of a value `ws` that is known to be in WHNF is its first branch.
    whnfE ws expr
      = case expr of
          Let b _ e body
            | Just (x,a,pre) <- whnfTest e, Just _ <- narrow (VPtr a)
            , Just (joins,CaseV _ (Var b') alts) <- joinsTo ws body, b == b', [e0,e1] <- altBodies alts
            , let expr' = pre (joins (if S.member x ws then whnfE ws e1
                                      else IfWhnf x (whnfE (S.insert x ws) e1) (whnfE ws e0)))
            , S.notMember b (fvE expr')
            -> expr'
          Let m t e1 e2
            | Just t'@(VPtr w) <- narrow t, let e1' = whnfE ws e1, forced ws S.empty e1'
            , Right (ASum alts) <- unrollT env w
            -> Let m t' e1' (strictMatches (map fst alts) m (whnfE (S.insert m ws) e2))
          _ -> deepE (whnfE ws) expr
    -- the test of `x`, after the lets of its tag argument
    whnfTest e
      = case e of
          Call f [a] [Var x, _] | f == nameLazyIsWhnf || f == nameLazyPtrIsWhnf -> Just (x,a,id)
          Let y t e1 e2 -> (\(x,a,pre) -> (x,a,Let y t e1 . pre)) <$> whnfTest e2
          _ -> Nothing
    joinsTo ws e
      = case e of
          Join j tvs ps e1 e2 -> (\(js,c) -> (Join j tvs ps (whnfE ws e1) . js,c)) <$> joinsTo ws e2
          CaseV{} -> Just (id,e)
          _ -> Nothing
    -- whether an expression returns a value in WHNF, given the values narrowed by a test and
    -- the join points that do
    forced xs js expr
      = case expr of
          Ret (Var x) -> S.member x xs
          Call f _ _ | Just (SigFun _ _ (VPtr (AWhnf _))) <- M.lookup f sigs -> True
          Jump j _ _ -> S.member j js
          IfWhnf x e1 e2 -> forced (S.insert x xs) js e1 && forced xs js e2
          Unreachable _ -> True
          Let _ _ _ e -> forced xs js e
          Join j _ _ e1 e2 -> forced xs (if forced xs js e1 then S.insert j js else js) e2
          CaseV _ _ alts -> all (forced xs js) (altBodies alts)
          _ -> False

-- The matches on a value `m` in WHNF, whose sum has the tags `strict`, keep the alternatives
-- of those tags, and a default only if it has any.
strictMatches :: [Int] -> Path -> VExpr -> VExpr
strictMatches strict m = go S.empty S.empty
  where
    go ds rs expr
      = case expr of
          Deref q (Var y) d e | y == m -> Deref q (Var y) d (go (S.insert d ds) rs e)
          Unroll q y r e | S.member y ds -> Unroll q y r (go ds (S.insert r rs) e)
          CaseA q r alts def | S.member r rs
            -> let alts' = [(i,x,go ds rs e) | (i,x,e) <- alts, i `elem` strict]
                   def' = if all (`elem` [i | (i,_,_) <- alts']) strict then Nothing
                          else fmap (\(d,e) -> (d,go ds rs e)) def
               in CaseA q r alts' def'
          _ -> deepE (go ds rs) expr

-- apply a function to the subexpressions of an expression, also in lambdas
deepE :: (VExpr -> VExpr) -> VExpr -> VExpr
deepE f = runIdentity . descendE Identity (Identity . deepV) (\_ -> Identity . f)
  where
    deepV = mapV deepA deepV
    deepA a = case a of
                Lam ps r e -> Lam ps r (f e)
                _ -> mapA id deepA deepV a

-- substitute the parameters of join points to which every jump passes the same constant of a
-- sum of units (such as `recurse`)
knownJoins :: VExpr -> VExpr
knownJoins expr
  = case expr of
      Join j tvs ps e1 e2
        -> let e2' = knownJoins e2
               args = jumpArgs j e2'
               known = M.fromList [(x,v) | (i,(x,_,_)) <- zip [0..] ps, (v@(Inj _ _ UnitV):vs) <- [map (!! i) args], all (== v) vs]
           in Join j tvs ps (knownJoins (replaceE known e1)) e2'
      _ -> runIdentity (descendE Identity Identity (\_ -> Identity . knownJoins) expr)

-- Rename the uses of roots and their parts. The binders of elaborated code are roots, and the
-- renamed ones are not bound again.
renameUses :: M.Map Path Path -> VExpr -> VExpr
renameUses ren = goE
  where
    goE = runIdentity . descendE (Identity . goP) (Identity . goV) (\_ -> Identity . goE)
    goV v = case v of
              Var x -> Var (goP x)
              _ -> mapV goA goV v
    goA a = case a of
              Lam ps r e -> Lam ps r (goE e)
              _ -> mapA goP goA goV a
    goP x@(Path n ss) = maybe x (\y -> foldl child y ss) (M.lookup (root n) ren)
