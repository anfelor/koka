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

-- A continuation that wraps an expression.
type K = VExpr -> VExpr

compose :: [K] -> K
compose = foldr (.) id

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
