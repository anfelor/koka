-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Lazy values under evaluation as cells (right after `Paths`).

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
  found by `Kind.Infer`'s naming (`lazyName`). `Paths` has already named the binders of a lock
  as `[lock]` requires: the box `y.roll.delay.injⱼ` of the lazy value `y`, and its contents
  `y.roll.delay.injⱼ.contents`. Elaboration has made Koka's tests of WHNF `[if-whnf]`
  (`Elab.Lazy.whnfTests`).
-}
module Backend.Typed.Passes.Lazy( lazyProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Common.Name
import Common.NamePrim( nameLazyMemoize, nameLazyMemoizeTarget )
import Backend.Typed.Syntax
import Backend.Typed.Build( prodVal, padFields )
import Backend.Typed.Lazies( Lazies(..) )
import Backend.Typed.Passes.Common( NameSupply, freshFor, freshPathFrom, perDef, substE )
import Backend.Typed.Traversal( child, descendE, fvE, fvV, lamsV )
import Backend.Typed.Pretty( ppr )
import Backend.Typed.Env( Env(..), envOf, unrollT, reuseSize, lazySides, M, asks, evalM, gets, liftE, local, modify, state )

-- the lazy value of `lazy-eval-locked` and its type
data LEnv = LEnv{ leEnv :: Env, leLazies :: Lazies, leLocked :: Maybe (Path,AType) }

-- fresh names, and the smallest cell passed to each parameter of a join point
type L a = M LEnv (NameSupply, M.Map Name (M.Map Int Int)) a

-- the cells that an expression consumes, with their size and type
type Cells = M.Map Path (Int,AType)

fresh :: String -> L Path
fresh s = state (\(ns,js) -> let (x,ns') = freshPathFrom ("lz" ++ s) ns in (x,(ns',js)))

lazyProgram :: Lazies -> Program -> (Program,[String])
lazyProgram lazies prog
  = let (prog',errs) = perDef (\d -> evalM (lazyDef d) (LEnv (envOf prog) lazies Nothing) (freshFor d, M.empty)) prog
        cells = M.fromList [(f,c) | DefFun f _ ((_,_,c@VCell{}):_) _ _ _ <- progDefs prog']
    in (prog'{ progSigs = M.mapWithKey (withCell cells) (progSigs prog) }, errs)
  where
    withCell cells f sig
      = case (M.lookup f cells, sig) of
          (Just c, SigFun tvs ((m,_):ps) q r) -> SigFun tvs ((m,c):ps) q r
          _ -> sig

-- the first parameter of a `lazy-C` function is the cell of its constructor, and the first
-- parameter of `lazy-eval-locked` is the lazy value that it locks
lazyDef :: Def -> L Def
lazyDef def
  = do lazies <- asks leLazies
       case def of
         DefFun{ defName = f, defArgs = (x,m,t):ps, defBody = body }
           | Just (_,n,_) <- M.lookup f (lzCons lazies)
           -> case t of
                VPtr a | targets x body -> (\body' -> def{ defArgs = (x,m,VCell n a):ps, defBody = body' }) <$> cellE (M.singleton x (n,a)) body
                _ -> fail ("a lazy constructor function without a memoization target: " ++ show x)
           | S.member f (lzLocked lazies), VPtr a <- t
           -> (\body' -> def{ defBody = body' }) <$> local (\le -> le{ leLocked = Just (x,a) }) (cellE M.empty body)
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
         Deref (Var x) y (Unroll y' z (IfWhnf z' (s,e1) (l,CaseA l' alts def)))
           | Just (x',a) <- locked, x == x', y' == y, z' == z, l' == l, M.null cs
           -> do ind <- indirectOf a
                 (thunks,_) <- sidesOf a
                 let lockAlt (i,b,e)
                       | i /= ind, Just (ABox w) <- lookup i thunks
                       = do n <- liftE (reuseSize w)
                            (,,) i b <$> lock (x,n,a) b e
                       | otherwise = (,,) i b <$> cellE cs e
                 e1' <- cellE cs e1
                 alts' <- mapM lockAlt alts
                 def' <- traverse (\(u,e) -> (,) u <$> cellE cs e) def
                 return (Deref (Var x) y (Unroll y z (IfWhnf z (s,e1') (l,CaseA l alts' def'))))
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
         Join r j tvs ps e1 e2
           -> do e2' <- cellE cs e2
                 sizes <- gets (M.findWithDefault M.empty j . snd)
                 ps' <- mapM (\(i,(x,m,t)) -> case (M.lookup i sizes, t) of
                                               (Nothing,_) -> return (x,m,t)
                                               (Just n,VPtr a) -> return (x,m,VCell n a)
                                               (Just _,_) -> fail ("a cell passed to a parameter of " ++ show j ++ " that is not a pointer"))
                             (zip [0 :: Int ..] ps)
                 e1' <- cellE (M.fromList [(x,(n,a)) | (x,_,VCell n a) <- ps']) e1
                 return (Join r j tvs ps' e1' e2')
         _ | not (S.disjoint (M.keysSet cs) (operands expr)) -> fail ("unexpected use of a cell in " ++ ppr expr)
           | otherwise -> descendE pure cellV (\_ e -> cellE cs e) expr
  where
    operands e = getConst (descendE (Const . S.singleton) (Const . fvV) (\_ _ -> Const S.empty) e)

-- Lock the box `b` of a lazy alternative of the lazy value `x` in `e`, whose uses of `x` become
-- uses of the cell `b.credit`. The box is a part of `x`, so only `x` itself is renamed.
lock :: (Path,Int,AType) -> Path -> VExpr -> L VExpr
lock (x,n,a) b e
  = do let c = child b SCredit
           body = case e of
                    Unbox b' _ e' | b' == b -> e'
                    _ -> e
       body' <- cellE (M.singleton c (n,a)) (substE (\y -> if y == x then Just (Var c) else Nothing) body)
       return (Unbox b (child b SContents) (Lock b body'))

-- the lambdas in a value have no cells
cellV :: VVal -> L VVal
cellV = lamsV (\_ _ -> cellE M.empty)

-- `memoize(c, v)`: write the constructor of `v` over the cell if it fits
memoize :: Path -> Int -> AType -> VVal -> L VExpr
memoize c n a v
  = do (thunks,strict) <- sidesOf a
       case v of
         Ptr _ (Roll _ (InjLazy d _ (InjA k _ (Box w))))
           | Just (ABox s) <- lookup k (case d of Whnf -> strict; Delay -> thunks), Right m <- reuseSize s, m <= n
           -> return (Memoize (Var c) d k w)
         _ -> indirect c a v

-- `indirect c v`: free the cell if it is unique, and otherwise write an indirection to `v` over it
indirect :: Path -> AType -> VVal -> L VExpr
indirect c a v
  = do i <- indirectOf a
       r <- fresh "r"
       p <- fresh "p"
       return (Let r (VPtr a) (Ret v)
                (IsUnique c (Free c (Ret (Var r)))
                            (Let p (VPtr a) (Memoize (Var c) Delay i (Var r)) (Ret (Var r)))))

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
