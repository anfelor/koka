-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Builders for typed IR expressions and values.
module Backend.Typed.Build where

import Backend.Typed.Syntax
import Backend.Typed.Types( alphaEq, orNull, unNull, unYield )

-- A continuation that wraps an expression.
type K = VExpr -> VExpr

compose :: [K] -> K
compose = foldr (.) id

-- The dummy of a yield at the type `W`, such as in the yielding branch of a `[let-yield]`:
-- `ret (pure null) : Y (V?)`, where `W` is `Y V` or `V`, cast to `W` if that is not `Y (V?)`.
yielded :: VType -> VExpr
yielded w
  | alphaEq w (VYield (orNull v)) = dummy
  | otherwise = CastEv (VYield (orNull v)) w dummy
  where
    v = fst (unYield w)
    dummy = Ret (Pure (Null (unNull v)))

-- the dummy of a yield, as `yielded` builds it
isYielded :: VExpr -> Bool
isYielded e
  = case e of
      Ret (Pure (Null _)) -> True
      CastEv _ _ (Ret (Pure (Null _))) -> True
      _ -> False

-- the product of values (`Types.prodV`)
prodVal :: [VVal] -> VVal
prodVal []  = UnitV
prodVal [v] = v
prodVal vs  = Tuple vs

-- the values of the fields of a constructor `fields`, followed by those of its padding
padFields :: [VType] -> [VVal] -> [VVal]
padFields fields vs = vs ++ map zero (drop (length vs) fields)
  where
    zero (VRaw RFloat64) = Lit (LitFloat 0)
    zero _ = Lit (LitChar '\0')
