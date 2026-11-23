-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Fewer tests for a yield (after Simplify, before Perceus).

  Elaboration tests the result of every call that may yield where it needs it, which is
  correct but often tests twice, or tests a value that cannot be a dummy. A test of the
  result `r : U? ⊗ KCtx` of `e₁` binds its fields and tests the token (`[if-yielding]`):

    T(e₁; k₃.e₃; k₂.e₂)  ≜  let r = e₁ in let r₀ = r.0 in let k = r.1 in
                            if-yielding k of { yield k₃ -> e₃; k₂ -> e₂ }

  Each rule preserves the types:

  - A bound expression whose results are all `(v, k)` with v not the dummy, and that calls
    nothing that may yield, cannot yield, so it needs no test. (A call whose result is cast
    without a test, such as one under a type abstraction that Koka tests only afterwards, may
    leave the flag set although the results are not the dummy.)

      T(K[ret (v, k')]; k₃.e₃; k₂.e₂)   ~>   let r = K[ret (v, k')] in ... e₂[k₂ := k]

  - A coercion `c` of the result `q` of a call, tested inside the bound expression of another
    test, moves into the continuation, so that one test remains:

      T(K[T(e; j₃.ret (null, j₃); j₂.c)]; k₃.e₃; k₂.e₂)
        ~>   T(K[e]; j₃.e₃[k₃ := j₃]; j₂.let r = c in let r₀ = r.0 in let k = r.1 in e₂[k₂ := k])

    where `c` only uses `q` and its token `j₂`, and cannot yield (as in the first rule).

  - A bound expression whose results are all `some` needs no null test:

      let x : V? = K[ret (some v)] in is-null x of { null -> e₃; x.some -> e₂ }
        ~>   let x : V = K[ret v] in e₂[x.some := x]

    and likewise for `x : V? ⊗ KCtx`, results `(some v, k)`, and the null test of `x.0`.

  - A value that is unboxed only to be boxed again is the boxed value itself. Where the boxed
    value is the untested result of a call (that elaboration only tested because of the
    unboxing, as in the inlined `local-var`, whose `prompt-local-var` tests the flag itself),
    the test goes away, and the result is passed on with a cast, as by Koka's C backend:

      let x : V = T(e; k₃.drop k₃; cast-ev[V?, V] ret null;
                       k₂.drop k₂; is-null r₀ of { null -> unreachable; r₀.some -> unbox r₀.some }) in B[box x]
        ~>   let x : U = cast-ev[U? ⊗ KCtx, U] e in B[x]
-}
module Lidar.Passes.Yields( yieldsProgram ) where

import Data.Functor.Identity( Identity(..) )
import Data.Maybe( isJust )
import Lidar.Syntax
import Lidar.Build( isYielded )
import Lidar.Traversal( descendE, destructAOf, destructVOf, dsAlts, dsBuild, dsScrut, fvE, lamsV, mapA, mapV, subexprs, within )
import Lidar.Types( Types(..), alphaEq, inst, withToken, yields )
import Lidar.Passes.Common( renamePath )

yieldsProgram :: Program -> Program
yieldsProgram prog = prog{ progDefs = [d{ defBody = yE (result d) (defBody d) } | d <- progDefs prog] }
  where
    result d = case d of
                 DefFun{ defRes = t } -> t
                 DefVal{ defType = t } -> t

-- A test of the result `r : U` of `e` for a yield, as elaboration builds it: the fields `r.0`
-- and `r.1` are bound, and the token `r.1` is tested.
data Test = Test{ tRes :: Path, tType :: VType, tExpr :: VExpr, tVal :: Path, tToken :: Path
                , tYielding :: (Path,VExpr), tCont :: (Path,VExpr) }

testOf :: VExpr -> Maybe Test
testOf expr
  = case expr of
      Let r u e (Proj (Var r1) 0 r0 (Proj (Var r2) 1 k (IfYielding (Var k') y c)))
        | r1 == r, r2 == r, k' == k -> Just (Test r u e r0 k y c)
      _ -> Nothing

-- the test, or its body `b` in place of the test
fromTest :: Test -> VExpr
fromTest t = withFields t (IfYielding (Var (tToken t)) (tYielding t) (tCont t))

withFields :: Test -> VExpr -> VExpr
withFields t b = Let (tRes t) (tType t) (tExpr t) (Proj (Var (tRes t)) 0 (tVal t) (Proj (Var (tRes t)) 1 (tToken t) b))

-- an expression with its result type `w`
yE :: VType -> VExpr -> VExpr
yE w expr
  = case expr of
      Let r u e (Let x _ c body) | Just boxedAs <- reboxed r u x c body -> yE w (Let r u e (boxedAs r))
      _ | Just t <- testOf expr
        -> test w t{ tExpr = yE (tType t) (tExpr t), tYielding = fmap (yE w) (tYielding t), tCont = fmap (yE w) (tCont t) }
      Let x t e1 e2 -> nonNull (Let x t (yE t e1) (yE w e2))
      CastEv u t e -> CastEv u t (yE u e)
      Total k e -> Total k (yE (withToken w) e)
      Gen tvs e -> case w of
                     VPtr (AForall bs a) -> Gen tvs (yE (VPtr (inst bs (map AVar tvs) a)) e)
                     _ -> expr
      _ -> runIdentity (descendE pure (Identity . yV) (\_ e -> Identity (yE w e)) expr)

yV :: VVal -> VVal
yV = runIdentity . lamsV (\_ r e -> Identity (yE r e))

-- a test whose subexpressions are done
test :: VType -> Test -> VExpr
test w t
  | cannotYield (tExpr t) = nonNull (withFields t (renamePath k2 (tToken t) e2))
  | Just (inner,c) <- coerced t, cannotYield c
  = let (j2,_) = tCont inner
        (j3,_) = tYielding inner
        x = tRes t
    in test w inner{ tYielding = (j3, renamePath k3 j3 e3)
                   , tCont = (j2, nonNull (Let x (tType t) c (Proj (Var x) 0 (tVal t) (Proj (Var x) 1 (tToken t) (renamePath k2 (tToken t) e2))))) }
  | otherwise = fromTest t
  where
    (k2,e2) = tCont t
    (k3,e3) = tYielding t

-- An expression that cannot yield: its results are not the dummy, and it calls nothing that
-- may yield (`mayYield`).
cannotYield :: VExpr -> Bool
cannotYield expr = not (mayYield expr) && isJust (unwrap valid Just expr)
  where
    valid v = case v of
                Null _ -> Nothing
                Tuple [Null _, _] -> Nothing   -- with the token
                _ -> Just v

-- `let x : V? = e₁ in is-null x of { null -> e₃; x.some -> e₂ }`, where the results of e₁ are
-- all `some`, as `let x : V = e₁' in e₂[x.some := x]`, and likewise for `x : V? ⊗ KCtx` and
-- the null test of `x.0`
nonNull :: VExpr -> VExpr
nonNull expr
  = case expr of
      Let x t e1 body
        | Just (t',fields,x0,(y,e2)) <- nullTest x t body
        , all (\z -> z `within` y || not (z `within` x0 || x0 `within` z)) (fvE e2)
        , Just e1' <- unwrap someVal nonNullType e1
        -> Let x t' e1' (fields (renamePath y x0 e2))
      _ -> expr
  where
    someVal v = case v of
                  Some w -> Just w
                  Tuple [Some w, k] -> Just (Tuple [w,k])
                  _ -> Nothing
    nonNullType s = case s of
                      VOrNull u -> Just u
                      VProd [(f,VOrNull u),tok] -> Just (VProd [(f,u),tok])
                      _ -> Nothing
    nullTest x t body
      = case (t,body) of
          (VOrNull u, IsNull (Var x') _ alt) | x' == x -> Just (u,id,x,alt)
          (VProd [(f,VOrNull u),tok], Proj (Var x1) 0 x0 (Proj (Var x2) 1 k (IsNull (Var x0') _ alt)))
            | x1 == x, x2 == x, x0' == x0 -> Just (VProd [(f,u),tok], Proj (Var x) 0 x0 . Proj (Var x) 1 k, x0, alt)
          _ -> Nothing

-- Whether an expression calls something that may yield: a test, or a cast that removes the `?`
-- of a result without a test (such as of a call that Koka tests only after an enclosing type
-- abstraction). The flag may then be set although the results are not the dummy. Lambdas do
-- not run here.
mayYield :: VExpr -> Bool
mayYield expr
  = case expr of
      IfYielding{} -> True
      CastEv u _ _ | yields u -> True
      _ -> any mayYield (subexprs expr)

-- The results of an expression unwrapped by `val`, and the types of its `unreachable`s by `ty`.
-- Jumps go to join points within the expression (a bound expression has no joins in scope),
-- whose bodies are unwrapped as well.
unwrap :: (VVal -> Maybe VVal) -> (VType -> Maybe VType) -> VExpr -> Maybe VExpr
unwrap val ty expr
  = case expr of
      Ret v -> Ret <$> val v
      Unreachable t -> Unreachable <$> ty t
      Jump{} -> Just expr
      Let x t e1 e2 -> Let x t e1 <$> go e2
      Join j tvs ps e1 e2 -> Join j tvs ps <$> go e1 <*> go e2
      CaseLit v alts def -> CaseLit v <$> traverse (traverse go) alts <*> go def
      IfYielding v (k3,e3) (k2,e2) -> (\e3' e2' -> IfYielding v (k3,e3') (k2,e2')) <$> go e3 <*> go e2
      _ | Just ds <- destructAOf expr -> dsBuild ds (dsScrut ds) <$> traverse (go . snd) (dsAlts ds)
        | Just ds <- destructVOf expr -> dsBuild ds (dsScrut ds) <$> traverse (go . snd) (dsAlts ds)
        | otherwise -> Nothing
  where
    go = unwrap val ty

-- The test of a result inside the bound expression of the test `t`, whose yielding branch
-- passes on the dummy and whose continuation `c` only uses the result and its token: the
-- inner test with `K[e]` as its bound expression, and `c`. The yielding branch of `t` does
-- not use the result of `t`.
coerced :: Test -> Maybe (Test,VExpr)
coerced t
  | not (any (`within` tRes t) (fvE (snd (tYielding t)))) = inside (tExpr t)
  | otherwise = Nothing
  where
    inside expr
      = case expr of
          _ | Just i <- testOf expr, (j3,d) <- tYielding i, (j2,c) <- tCont i
            , isYielded d, all (== Var j3) (dummyToken d)
            , all (\z -> z `within` tRes i || z == j2) (fvE c)
            -> Just (i,c)
          Let y s a b -> under (Let y s a) b
          _ | Just ds <- destructAOf expr, [(_,b)] <- dsAlts ds -> under (\b' -> dsBuild ds (dsScrut ds) [b']) b
            | Just ds <- destructVOf expr, [(_,b)] <- dsAlts ds
            -> case expr of
                 -- the type of the result must not mention the unpacked type variables
                 Unpack _ tvs _ _ -> do res@(i,_) <- under (\b' -> dsBuild ds (dsScrut ds) [b']) b
                                        if any (`elem` tvs) (ftv (tType i)) then Nothing else Just res
                 _ -> under (\b' -> dsBuild ds (dsScrut ds) [b']) b
            | otherwise -> Nothing
    under k b = (\(i,c) -> (i{ tExpr = k (tExpr i) },c)) <$> inside b
    dummyToken d = case d of
                     Ret (Tuple [_,k]) -> [k]
                     CastEv _ _ (Ret (Tuple [_,k])) -> [k]
                     _ -> [UnitV]

-- Where `c` unboxes `r : U` to `x`, and `body` uses `x` only boxed: `body` with a variable
-- `z : U` for `box x`.
reboxed :: Path -> VType -> Path -> VExpr -> VExpr -> Maybe (Path -> VExpr)
reboxed r u x c body
  | Deref (Var r') d (Unbox d' y (Ret (Var y'))) <- c, r' == r, d' == d, y' == y
  , not (any (`within` x) (fvE (boxedAs r))) = Just boxedAs
  | otherwise = Nothing
  where
    boxedAs z = replaceE body
      where
        replaceE = runIdentity . descendE Identity (Identity . replaceV) (\_ b -> Identity (replaceE b))
        replaceV v = case v of
                       Ptr a (Box (Var x')) | x' == x, alphaEq (VPtr a) u -> Var z
                       _ -> mapV replaceA replaceV v
        replaceA a = case a of
                       Lam ps t b -> Lam ps t (replaceE b)
                       _ -> mapA id replaceA replaceV a
