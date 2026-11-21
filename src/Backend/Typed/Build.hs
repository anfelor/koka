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
import Backend.Typed.Types( alphaEq, orNull, unNull, unToken, withToken )

-- A continuation that wraps an expression.
type K = VExpr -> VExpr

compose :: [K] -> K
compose = foldr (.) id

-- The dummy of a yield with the token `k` at the type `W`, the result of a token-threaded
-- function: `ret (null, k) : V? ⊗ KCtx`, where `W` is `V? ⊗ KCtx` or `V ⊗ KCtx`, cast to `W`
-- if that is not `V? ⊗ KCtx`.
yieldedWith :: VType -> VVal -> VExpr
yieldedWith w k
  | alphaEq w u = dummy
  | otherwise = CastEv u w dummy
  where
    v = unNull (maybe w id (unToken w))
    u = withToken (orNull v)
    dummy = Ret (Tuple [Null v, k])

-- the dummy of a yield, as `yieldedWith` builds it
isYielded :: VExpr -> Bool
isYielded e
  = case e of
      Ret v -> dummy v
      CastEv _ _ (Ret v) -> dummy v
      _ -> False
  where
    dummy v = case v of
                Null _ -> True
                Tuple [Null _, _] -> True
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
