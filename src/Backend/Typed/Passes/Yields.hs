-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Fewer tests for a yield (after Simplify, before Perceus).

  Elaboration tests the result of every call that may yield where it needs it (`[let-yield]`),
  which is correct but often tests twice, or tests a value that cannot be a dummy. Each rule
  preserves the types:

  - A bound expression whose results are all `pure`, and that calls nothing that may yield,
    cannot yield, so it needs no test. (A call whose result is cast without a test, such as
    one under a type abstraction that Koka tests only afterwards, may leave the flag set
    although the results are `pure`.)

      let x : V = K[ret (pure v)] yielding e₃ in e₂   ~>   let x : V = K[ret v] in e₂

  - A coercion `c` of the result `r` of a call, tested inside the bound expression of another
    test, moves into the continuation, so that one test remains:

      let x : V = K[let r : U = e yielding yielded in c] yielding e₃ in e₂
        ~>   let r : U = K[e] yielding e₃ in let x : V = c' in e₂

    where `c'` is `c` with its results unwrapped from `pure` (`c` cannot yield, as in the
    first rule).

  - `yield-extend` and `yield-cont` return while the effect still yields, so the continuation
    of their test is dead: `unreachable`.

  - A value that is unboxed only to be boxed again is the boxed value itself. Where the boxed
    value is the untested result of a call (that elaboration only tested because of the
    unboxing, as in the inlined `local-var`, whose `prompt-local-var` tests the flag itself),
    the test goes away, and the result is passed on with a cast, as by Koka's C backend:

      let x : V = (let r : U = e yielding (let d = yielded in cast-ev[V] d) in unbox r) in B[box x]
        ~>   let r : Y U = e in let x : U = cast-ev[U] r in B[x]
-}
module Backend.Typed.Passes.Yields( yieldsProgram ) where

import Data.Functor.Identity( Identity(..) )
import Common.Name
import Common.NamePrim( nameYieldExtend, nameCoreHnd )
import Backend.Typed.Syntax
import Backend.Typed.Traversal( descendE, destructAOf, destructVOf, dsAlts, dsBuild, dsScrut, fvE, lamsV, mapA, mapV, subexprs, within )
import Backend.Typed.Types( Types(..), alphaEq, inst )

yieldsProgram :: Program -> Program
yieldsProgram prog = prog{ progDefs = [d{ defBody = yE (result d) (defBody d) } | d <- progDefs prog] }
  where
    result d = case d of
                 DefFun{ defRes = t } -> t
                 DefVal{ defType = t } -> t

-- an expression with its result type `w`
yE :: VType -> VExpr -> VExpr
yE w expr
  = case expr of
      Let r u e (Let x _ c body) | Just boxedAs <- reboxed r u x c body -> yE w (Let r u e (boxedAs r))
      Let x _ (LetYield r u e c d) body | dummy d, Just boxedAs <- reboxed r u x c body
        -> Let r (VYield u) (yE (VYield u) e) (Let x u (CastEv u (Var r)) (yE w (boxedAs x)))
      Let x t e1 e2 -> Let x t (yE t e1) (yE w e2)
      LetYield x t e1 e2 e3 -> letYield w x t (yE (VYield t) e1) (yE w e2) (yE w e3)
      Gen tvs e -> case w of
                     VPtr (AForall bs a) -> Gen tvs (yE (VPtr (inst bs (map AVar tvs) a)) e)
                     _ -> expr
      _ -> runIdentity (descendE pure (Identity . yV) (\_ e -> Identity (yE w e)) expr)

yV :: VVal -> VVal
yV = runIdentity . lamsV (\_ r e -> Identity (yE r e))

-- a test whose subexpressions are done
letYield :: VType -> Path -> VType -> VExpr -> VExpr -> VExpr -> VExpr
letYield w x t e1 e2 e3
  | stillYields e1 = LetYield x t e1 (Unreachable w) e3
  | Just e1' <- unpure e1 = Let x t e1' e2
  | Just (e,r,u,c) <- coerced e1, Just c' <- unpure c = letYield w r u e (Let x t c' e2) e3
  | otherwise = LetYield x t e1 e2 e3

-- An expression that cannot yield: its results are all `pure`, with these results unwrapped,
-- and it calls nothing that may yield (`mayYield`). Jumps go to join points within the
-- expression (a bound expression has no joins in scope), whose bodies are unwrapped as well.
unpure :: VExpr -> Maybe VExpr
unpure expr
  | mayYield expr = Nothing
  | otherwise = unwrap expr

-- Whether an expression calls something that may yield: a test, or a result of a type `Y U`
-- that is bound (to be cast without a test, such as a call that Koka tests only after an
-- enclosing type abstraction). The flag may then be set although the results are `pure`.
-- Lambdas do not run here.
mayYield :: VExpr -> Bool
mayYield expr
  = case expr of
      LetYield{} -> True
      Let _ VYield{} _ _ -> True
      _ -> any mayYield (subexprs expr)

unwrap :: VExpr -> Maybe VExpr
unwrap expr
  = case expr of
      Ret (Pure v) -> Just (Ret v)
      Unreachable (VYield t) -> Just (Unreachable t)
      Jump{} -> Just expr
      Let x t e1 e2 -> Let x t e1 <$> unwrap e2
      Join NonRec j tvs ps e1 e2 -> Join NonRec j tvs ps <$> unwrap e1 <*> unwrap e2
      CaseLit v alts def -> CaseLit v <$> traverse (traverse unwrap) alts <*> unwrap def
      _ | Just ds <- destructAOf expr -> dsBuild ds (dsScrut ds) <$> traverse (unwrap . snd) (dsAlts ds)
        | Just ds <- destructVOf expr -> dsBuild ds (dsScrut ds) <$> traverse (unwrap . snd) (dsAlts ds)
        | otherwise -> Nothing

-- `K[let r : U = e yielding yielded in c]` as `K[e]`, `r`, `U` and `c`, where `c` only uses `r`
coerced :: VExpr -> Maybe (VExpr,Path,VType,VExpr)
coerced expr
  = case expr of
      LetYield r u e c Yielded{} | all (`within` r) (fvE c) -> Just (e,r,u,c)
      Let y s a b -> under (Let y s a) b
      _ | Just ds <- destructAOf expr, [(_,b)] <- dsAlts ds -> under (\b' -> dsBuild ds (dsScrut ds) [b']) b
        | Just ds <- destructVOf expr, [(_,b)] <- dsAlts ds
        -> case expr of
             -- the type of `r` must not mention the unpacked type variables
             Unpack _ tvs _ _ -> do res@(_,_,u,_) <- under (\b' -> dsBuild ds (dsScrut ds) [b']) b
                                    if any (`elem` tvs) (ftv u) then Nothing else Just res
             _ -> under (\b' -> dsBuild ds (dsScrut ds) [b']) b
        | otherwise -> Nothing
  where
    under k b = (\(b',r,u,c) -> (k b',r,u,c)) <$> coerced b

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

-- the dummy of the type of a result that elaboration tested only to coerce it
dummy :: VExpr -> Bool
dummy expr
  = case expr of
      Let d _ (Yielded _) (CastEv _ (Var d')) -> d' == d
      _ -> False

-- a call to `yield-extend` or `yield-cont`, which return while the effect still yields
stillYields :: VExpr -> Bool
stillYields expr
  = case expr of
      Call f _ _ -> f == nameYieldExtend || f == nameYieldCont
      Let _ _ _ b -> stillYields b
      _ -> False
  where
    nameYieldCont = qualify nameCoreHnd (newName "yield-cont")
