-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Lazy values under evaluation as cells (right after elaboration, before `Paths`).

  Koka evaluates a lazy type `T` (`Kind.Infer`) with private functions that pass the lazy
  value under evaluation `@lazy : T⟨B̄⟩*` around:
  - `T/lazy-eval-locked(@lazy, recurse)` matches on `@lazy` and passes it on to `T/lazy-C`
    in the branch of each lazy constructor `C` other than the indirection;
  - `T/lazy-C(@lazy, recurse, fields)` starts with `memoize-target(@lazy, size, scan)` and
    ends every branch in `memoize(@lazy, v)` or, where Koka's sizes allow it, in a call
    `T/lazy-C'(@lazy, recurse, fields')`.
  Here the lazy value becomes a cell (`[lock]`): `lazy-eval-locked` locks it in the branch
  of each such constructor (on the `delay` side of its match, see `FromCore.lazyCase`), and
  every `lazy-C` takes it as a cell `cell_|V_C|⟨T⟨ā⟩⟩`. An
  expression in the scope of a cell `c : cell_n⟨T⟨B̄⟩⟩` must consume it:
  - `memoize-target(c, …)` is deleted;
  - `memoize(c, K(v))` writes K over the cell (`[memoize]`, on its side of the lazy sum) if K
    is a box with `|V_K| ≤ n`,
    and otherwise, like `memoize(c, v)` of any other value, it becomes an indirection to the
    value (`indirect`);
  - a call `lazy-C'(c, recurse, v̄)` passes the cell on if `|V_C'| ≤ n` (by our sizes, which
    may differ from Koka's), and otherwise becomes an indirection to a new thunk `C'(v̄)`,
    which `lazy-whnf` goes on to evaluate;
  - a jump passes the cell on, and the parameter of the join point becomes a cell of the
    smallest size passed (Koka inlines `lazy-C` into `lazy-eval-locked` as a join point);
  - a branch without the cell is the thunks of a match on a forced value, which are
    `unreachable` (`[unreachable]` consumes the cell).
  Any other use of a cell, and any other use of `memoize`, is an error. The functions are
  found by `Kind.Infer`'s naming (`lazyName`). The binders of a lock have the names that
  `[lock]` requires before `Paths`: the box `y.roll.delay.injⱼ` of the lazy value `y`, and its
  contents `y.roll.delay.injⱼ.contents`.

  Before all of this, Koka's tests of WHNF become `[if-whnf]` (`whnfE`).
-}
module Backend.Typed.Elab.Lazy( lazyProgram ) where

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
import Backend.Typed.Query( Env(..), envOf, unrollT, reuseSize, lazySides )
import Backend.Typed.Elab.TypeInfo( conFieldTypes, padFields )

-- The `lazy-C` functions with the tag of their constructor, the size of its cell and its
-- fields (with the padding, see `TypeInfo.conFieldTypes`), the
-- `lazy-eval-locked` functions, and the tag of the indirection ι of each lazy type.
data Lazies = Lazies{ lzCons :: M.Map Name (Int,Int,[VType]), lzLocked :: S.Set Name
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
        run d  = case evalM (whnfDef d >>= lazyDef) (LEnv env lazies Nothing) (freshFor d, M.empty) of
                   Right d' -> (d', [])
                   Left err -> (d, [show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs prog))
        cells  = M.fromList [(f,c) | DefFun f _ ((_,_,c@VCell{}):_) _ _ <- defs]
    in (prog{ progDefs = defs, progSigs = M.mapWithKey (withCell cells) (progSigs prog) }, concat errs)
  where
    withCell cells f sig
      = case (M.lookup f cells, sig) of
          (Just c, SigFun tvs ((m,_):ps) r) -> SigFun tvs ((m,c):ps) r
          _ -> sig

lazyFuns :: Newtypes -> TypeDefs -> Lazies
lazyFuns nt tdefs
  = Lazies (M.fromList [(funName info (show (unqualify (conInfoName con))), (tag,n,fs))
                       | (info,tvs,thunks) <- infos, (tag,con) <- cons info
                       , not (isLazyIndirectConName (conInfoName con))
                       , Just (ABox s) <- [lookup tag thunks], Right n <- [reuseSize s]
                       , Right fs <- [conFieldTypes nt (map AVar tvs) con]])
           (S.fromList [funName info "eval-locked" | (info,_,_) <- infos])
           (M.fromList [(dataInfoName info, tag) | (info,_,_) <- infos, (tag,con) <- cons info, isLazyIndirectConName (conInfoName con)])
  where
    env = Env tdefs M.empty
    cons info = zip [1..] (dataInfoConstrs info)   -- tags start at 1
    infos = [(info,tvs,thunks) | (_,info) <- NM.toList (newtypesTypeDefs nt)
                               , Just TypeDef{ tdefParams = tvs } <- [M.lookup (dataInfoName info) tdefs]
                               , Right (thunks,_) <- [lazySides env (ACon (dataInfoName info) (map AVar tvs))]]
    funName info stem = qualify (qualifier (dataInfoName info)) (lazyName info stem)

-- the first parameter of a `lazy-C` function is the cell of its constructor, and the first
-- parameter of `lazy-eval-locked` is the lazy value that it locks
lazyDef :: Def -> L Def
lazyDef def
  = do lazies <- asks leLazies
       case def of
         DefFun f tvs ((x,m,t):ps) res body
           | Just (_,n,_) <- M.lookup f (lzCons lazies)
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
         Deref m (Var x) y (Unroll m' y' z (IfWhnf m1 z' (s,e1) (l,CaseA m'' l' alts def)))
           | Just (x',a) <- locked, x == x', y' == y, z' == z, l' == l, M.null cs
           -> do ind <- indirectOf a
                 (thunks,_) <- sidesOf a
                 let r = child y SRoll
                     d = child r SDelay
                     lockAlt (i,b,e)
                       | i /= ind, Just (ABox w) <- lookup i thunks
                       = do n <- liftE (reuseSize w)
                            c <- fresh "cell"
                            let y = child d (injAStep i b)
                            (,,) i y <$> lock (x,c,n,a) y b e
                       | otherwise = (,,) i b <$> cellE cs e
                 e1' <- cellE cs e1
                 alts' <- mapM lockAlt alts
                 def' <- traverse (\(u,e) -> (,) u <$> cellE cs e) def
                 return (Deref m (Var x) y (Unroll m' y r (IfWhnf m1 r (s,e1') (d,CaseA m'' d alts' def'))))
         Let _ _ (Call f _ (Var c : _)) e
           | f == nameLazyMemoizeTarget, M.member c cs -> cellE cs e
         Call f _ [Var c, v]
           | f == nameLazyMemoize, Just (n,a) <- M.lookup c cs, M.size cs == 1, S.notMember c (fvV v)
           -> cellV v >>= memoize c n a
         Call f ts (Var c : vs)
           | Just (k,m,fs) <- M.lookup f cons, Just (n,a) <- M.lookup c cs, M.size cs == 1, S.notMember c (S.unions (map fvV vs))
           -> do vs' <- mapM cellV vs
                 if m <= n then return (Call f ts (Var c : vs'))
                   else do con <- conValue a k (padFields fs (drop 1 vs'))   -- without `recurse`
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
-- uses of `x`, `b` and the contents of `b` become uses of the cell, `z` and `z.contents`.
lock :: (Path,Path,Int,AType) -> Path -> Path -> VExpr -> L VExpr
lock (x,c,n,a) z b e
  = do let (contents,body) = case e of
                               Unbox _ b' p e' | b' == b -> ([(p,child z SContents)],e')
                               _ -> ([],e)
       body' <- cellE (M.singleton c (n,a)) (renameE (M.fromList ((x,c) : (b,z) : contents)) body)
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
  = do (thunks,strict) <- sidesOf a
       case v of
         Ptr _ (Roll _ (InjLazy d _ (InjA k _ (Box w))))
           | Just (ABox s) <- lookup k (case d of Whnf -> strict; Delay -> thunks), Right m <- reuseSize s, m <= n
           -> return (Ret (Memoize (Var c) d k w))
         _ -> indirect c a v

-- `indirect c v`: free the cell if it is unique, and otherwise write an indirection to `v` over it
indirect :: Path -> AType -> VVal -> L VExpr
indirect c a v
  = do i <- indirectOf a
       r <- fresh "r"
       p <- fresh "p"
       return (Let r (VPtr a) (Ret v)
                (IsUnique c (Free c (Ret (Var r)))
                            (Let p (VPtr a) (Ret (Memoize (Var c) Delay i (Var r))) (Ret (Var r)))))

-- the lazy constructor with tag k and fields v̄ at the type of a cell
conValue :: AType -> Int -> [VVal] -> L VVal
conValue a k vs
  = do env <- asks leEnv
       b <- liftE (unrollT env a)
       (thunks,_) <- sidesOf a
       case lookup k thunks of
         Just (ABox VExists{}) -> fail ("a lazy constructor with existential fields: " ++ ppr (A a))
         Just (ABox _) -> return (Ptr a (Roll a (InjLazy Delay b (InjA k (ASum thunks) (Box (prodVal vs))))))
         _ -> fail ("no lazy constructor " ++ show k ++ " in " ++ ppr (A a))

-- the thunks and the strict alternatives of a lazy type
sidesOf :: AType -> L ([(Int,AType)],[(Int,AType)])
sidesOf a
  = do env <- asks leEnv
       liftE (lazySides env a)

-- the tag of the indirection of a lazy type
indirectOf :: AType -> L Int
indirectOf a
  = do inds <- asks (lzIndirect . leLazies)
       case a of
         ACon n _ | Just i <- M.lookup n inds -> return i
         _ -> fail ("not a lazy type: " ++ ppr (A a))

-- Tests of WHNF (`[if-whnf]`). Koka tests a lazy value `x` with `datatype-(ptr-)is-whnf(x, tag)`,
-- after the lets of its tag argument, and a case on the result, with the join points of its
-- match in between. The test becomes `[if-whnf]` on `x`. In its first branch, `x` is in WHNF
-- with the strict alternatives `s` (`ws`): a match on `x` there is a match on `s`, and another
-- test of `x` is its first branch.
whnfDef :: Def -> L Def
whnfDef def = (\body -> def{ defBody = body }) <$> whnfE M.empty (defBody def)

whnfE :: M.Map Path Path -> VExpr -> L VExpr
whnfE ws expr
  = case expr of
      Let b _ e body
        | Just (x,pre) <- whnfTest e
        , Just (joins,b',alts) <- joinsTo body, b == b', [e0,e1] <- altBodies alts
        -> do test <- case M.lookup x ws of
                        Just _ -> whnfE ws e1
                        Nothing -> do d <- fresh "d"
                                      r <- fresh "r"
                                      s <- fresh "whnf"
                                      l <- fresh "delay"
                                      e1' <- whnfE (M.insert x s ws) e1
                                      e0' <- whnfE ws e0
                                      return (Deref Owned (Var x) d (Unroll Owned d r (IfWhnf Owned r (s,e1') (l,e0'))))
              joins' <- mapM (\(j,tvs,ps,e2) -> Join j tvs ps <$> whnfE ws e2) joins
              let expr' = pre (foldr ($) test joins')
              if S.member b (fvE expr') then descend else return expr'
      Deref _ (Var x) d (Unroll _ d' r (IfWhnf _ r' (s',e1) _))
        | Just s <- M.lookup x ws, d == d', r == r'
        -> whnfE ws (renameUses (M.singleton s' s) e1)
      _ -> descend
  where
    descend = descendE pure whnfV (\_ -> whnfE ws) expr
    whnfV = descendV whnfA whnfV
    whnfA a = case a of
                Lam ps r e -> Lam ps r <$> whnfE ws e
                _ -> descendA pure whnfA whnfV a
    -- the test of `x`, after the lets of its tag argument
    whnfTest e
      = case e of
          Call f [_] [Var x, _] | f == nameLazyIsWhnf || f == nameLazyPtrIsWhnf -> Just (x,id)
          Let y t e1 e2 -> (\(x,pre) -> (x,Let y t e1 . pre)) <$> whnfTest e2
          _ -> Nothing
    -- the join points before the case on the result of the test
    joinsTo e
      = case e of
          Join j tvs ps e1 e2 -> (\(js,y,alts) -> ((j,tvs,ps,e1) : js,y,alts)) <$> joinsTo e2
          CaseV _ (Var y) alts -> Just ([],y,alts)
          _ -> Nothing

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
