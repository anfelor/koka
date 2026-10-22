-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Effect yields (before Perceus).

  Koka's monadic translation tests for a yield after a call that may yield an effect:

    let x : V = e₁ in let y = yielding() in case y of { inj0 _ -> e₂; inj1 _ -> e₃ }

  While an effect yields, `e₁` returns a dummy value, and elaboration has coerced the result
  of its last call inside `e₁`, before the test. The test becomes a `[let-yield]` (a test
  without such a `let` binds `y : 𝟙`), and a coercion `c` that only takes apart the result
  `r` of the last call moves into `e₂`:

    e₁ = K[let r : U = e in c]   ~>   let r : U = K[e] yielding e₃ in let x : V = c in e₂

  A call whose coerced result is the result of a definition is not tested by Koka (its dummy
  is the dummy of the definition), so the coercion gets a test of its own, whose yielding
  branch is `[yielded]`.

  The same holds if the coercion is a `let` of its own, `let r = e in let x = c in <test>`.
  A dummy may also be passed on without a test, to a function that tests for it (such as
  `prompt-local-var`): a value that is unboxed only to be boxed again, `let x = unbox r`
  where `x` only occurs as `box x`, is `r` itself.

  Where the test is the bound expression of a `let` whose body only coerces its result (as
  after inlining `yield-bind`), the body is copied into both branches first (with fresh
  roots in the yielding branch).

  In the yielding branch, a coercion of the result of `yield-extend` or `yield-cont` (which
  return while the effect still yields) becomes `[yielded]` where the result may be a dummy
  (`⊢ʸ`, see `[yielded]`): then the result is a dummy as well. Other calls in that branch may
  handle the yield (as in `std/core/hnd`), so their results are kept.
-}
module Backend.Typed.Passes.Yields( yieldsProgram ) where

import qualified Data.Set as S
import Control.Monad.State
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Data.Monoid( All(..) )
import Common.Name
import Common.NamePrim( nameYielding, nameYieldExtend, nameCoreHnd )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Types( Types(..), inst )

type Y a = State NameSupply a

yieldsProgram :: Program -> Program
yieldsProgram prog = prog{ progDefs = [d{ defBody = evalState (yE (result d) True (defBody d)) (freshFor d) } | d <- progDefs prog] }
  where
    result d = case d of
                 DefFun{ defRes = t } -> t
                 DefVal{ defType = t } -> t

-- an expression with its result type `w`, where `dummy` if its result may be a dummy (`⊢ʸ`)
yE :: VType -> Bool -> VExpr -> Y VExpr
yE w dummy expr
  = case expr of
      Let r u e (Let x t c body)
        | Just body' <- reboxed r x c body -> yE w dummy (Let r u e body')
        | coercion r c, Just (_,e2,e3) <- yieldTest body, not (any (\z -> z `within` r || z `within` x) (fvE (fst e3)))
        -> LetYield r u <$> yE u True e <*> (Let x t c <$> yE w dummy e2) <*> branch e3
      Let x t e1 e2 | Just (y,e2',e3) <- yieldTest e2
        -> letYield x t <$> yE t True e1 <*> yE w dummy e2' <*> branch e3 <*> pure y
      -- a coerced result of a call, where the result may be a dummy, is tested first
      Let r u e c | dummy, calls e, coercion r c
        -> LetYield r u <$> yE u True e <*> yE w dummy c <*> pure (Yielded w)
      _ | Just (y,e2,e3) <- yieldTest expr
        -> LetYield y VUnit (Ret UnitV) <$> yE w dummy e2 <*> branch e3
      Let x t e1 e2 -> Let x t <$> yE t False e1 <*> yE w dummy e2
      Gen tvs e -> case w of
                     VPtr (AForall bs a) -> Gen tvs <$> yE (VPtr (inst bs (map AVar tvs) a)) False e
                     _ -> return expr
      _ -> descendE pure yV (\_ e -> yE w dummy e) expr
  where
    branch (e3,copy) = do e3' <- if copy then cloneE (state (freshPathFrom "y")) e3 else return e3
                          (if dummy then yielded w else id) <$> yE w dummy e3'

yV :: VVal -> Y VVal
yV = descendV yA yV

yA :: AVal -> Y AVal
yA val
  = case val of
      Lam ps r e -> Lam ps r <$> yE r True e
      _ -> descendA pure yA yV val

-- `let y = yielding() in case y of { inj0 _ -> e₂; inj1 _ -> e₃ }`: the test, its
-- continuation, and its yielding branch, with whether it is a copy (that needs fresh roots).
-- A coercion `c` of the result of the case, `let z = case y of { ... } in c`, is copied into
-- both branches.
yieldTest :: VExpr -> Maybe (Path,VExpr,(VExpr,Bool))
yieldTest expr
  = case expr of
      Let y _ (Call f [] []) body | f == nameYielding
        -> case body of
             CaseV _ (Var y') [(_,e2),(_,e3)] | y' == y -> test y e2 (e3,False)
             Let z t (CaseV _ (Var y') [(_,e2),(_,e3)]) c | y' == y, coercion z c -> test y (Let z t e2 c) (Let z t e3 c,True)
             _ -> Nothing
      _ -> Nothing
  where
    test y e2 (e3,copy) = if any (`within` y) (S.union (fvE e2) (fvE e3)) then Nothing else Just (y,e2,(e3,copy))

-- The test of a yield after `let x = e1`, where `y` is the variable of the test. A coercion of
-- the result of the last call of `e1` moves into the continuation.
letYield :: Path -> VType -> VExpr -> VExpr -> VExpr -> Path -> VExpr
letYield x t e1 e2 e3 y
  | any (`within` x) (fvE e3) = Let x t e1 (LetYield y VUnit (Ret UnitV) e2 e3)
  | Just (e1',r,u,c) <- coerced e1 = LetYield r u e1' (Let x t c e2) e3
  | otherwise = LetYield x t e1 e2 e3

-- `K[let r : U = e in c]` as `K[e]`, `r`, `U` and the coercion `c`
coerced :: VExpr -> Maybe (VExpr,Path,VType,VExpr)
coerced expr
  = case expr of
      Let r u e c | coercion r c -> Just (e,r,u,c)
      Let y s a b -> under (Let y s a) b
      _ | Just ds <- destructAOf expr, [(_,b)] <- dsAlts ds -> under (\b' -> dsBuild ds (dsMode ds) (dsScrut ds) [b']) b
        | Just ds <- destructVOf expr, [(_,b)] <- dsAlts ds
        -> case expr of
             -- the type of `r` must not mention the unpacked type variables
             Unpack _ _ tvs _ _ -> do res@(_,_,u,_) <- under (\b' -> dsBuild ds (dsMode ds) (dsScrut ds) [b']) b
                                      if any (`elem` tvs) (ftv u) then Nothing else Just res
             _ -> under (\b' -> dsBuild ds (dsMode ds) (dsScrut ds) [b']) b
        | otherwise -> Nothing
  where
    under k b = (\(b',r,u,c) -> (k b',r,u,c)) <$> coerced b

-- `e` without `let x = c` where `c` unboxes `r` and `e` only boxes `x` again (as `r`)
reboxed :: Path -> Path -> VExpr -> VExpr -> Maybe VExpr
reboxed r x c e
  | Deref _ (Var r') d (Unbox _ d' y (Ret (Var y'))) <- c, r' == r, d' == d, y' == y
  , let e' = replaceE e, not (any (`within` x) (fvE e')) = Just e'
  | otherwise = Nothing
  where
    replaceE = runIdentity . descendE Identity (Identity . replaceV) (\_ b -> Identity (replaceE b))
    replaceV v = case v of
                   Ptr _ (Box (Var x')) | x' == x -> Var r
                   _ -> mapV replaceA replaceV v
    replaceA a = case a of
                   Lam ps t b -> Lam ps t (replaceE b)
                   _ -> mapA id replaceA replaceV a

-- an expression that only takes apart `r` and builds a value from its parts
coercion :: Path -> VExpr -> Bool
coercion r c = c /= Ret (Var r) && all (`within` r) (fvE c) && noCalls c
  where
    noCalls e = case e of
                  Call{} -> False
                  App{} -> False
                  Jump{} -> False
                  _ -> getAll (getConst (descendE (const (Const (All True))) (const (Const (All True)))
                                                  (\_ b -> Const (All (noCalls b))) e))

-- In the yielding branch, the coercion of a dummy is the dummy `[yielded]`.
yielded :: VType -> VExpr -> VExpr
yielded w expr
  = case expr of
      Let r u e c | stillYields e, coercion r c -> Let r u e (Yielded w)
      -- a coercion of a coercion is a coercion (roots are bound once)
      Let z t (Let r u e c) k -> yielded w (Let r u e (Let z t c k))
      Let y s a b -> Let y s a (yielded w b)
      LetYield x t e1 e2 e3 -> LetYield x t e1 (yielded w e2) (yielded w e3)
      Join j ps e1 e2 -> Join j ps (yielded w e1) (yielded w e2)
      Gen{} -> expr
      _ -> runIdentity (descendE Identity Identity (\_ e -> Identity (yielded w e)) expr)

-- the result of a call (or application), which may yield
calls :: VExpr -> Bool
calls expr
  = case expr of
      Call{} -> True
      App{} -> True
      Let _ _ _ b -> calls b
      _ | Just ds <- destructAOf expr, [(_,b)] <- dsAlts ds -> calls b
        | Just ds <- destructVOf expr, [(_,b)] <- dsAlts ds -> calls b
        | otherwise -> False

-- a call to `yield-extend` or `yield-cont`, which return while the effect still yields
stillYields :: VExpr -> Bool
stillYields expr
  = case expr of
      Call f _ _ -> f == nameYieldExtend || f == nameYieldCont
      Let _ _ _ b -> stillYields b
      _ -> False
  where
    nameYieldCont = qualify nameCoreHnd (newName "yield-cont")
