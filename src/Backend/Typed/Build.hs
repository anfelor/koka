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
import Backend.Typed.Types( alphaEq, orNull, unNull, unYield, unToken, withToken )

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

-- The dummy of a yield with the token `k` at the type `W`, the result of a token-threaded
-- function: `ret (pure (null, k)) : Y (V? ⊗ KCtx)`, where `W` is `Y (V ⊗ KCtx)` or
-- `V ⊗ KCtx`, cast to `W` if that is not `Y (V? ⊗ KCtx)`.
yieldedWith :: VType -> VVal -> VExpr
yieldedWith w k
  | alphaEq w u = dummy
  | otherwise = CastEv u w dummy
  where
    v = unNull (fst (unYield (maybe w id (unToken w))))
    u = VYield (withToken (orNull v))
    dummy = Ret (Pure (Tuple [Null v, k]))

-- the dummy of a yield, as `yielded` or `yieldedWith` builds it
isYielded :: VExpr -> Bool
isYielded e
  = case e of
      Ret v -> dummy v
      CastEv _ _ (Ret v) -> dummy v
      _ -> False
  where
    dummy v = case v of
                Pure (Null _) -> True
                Pure (Tuple [Null _, _]) -> True
                _ -> False

-- the result `v` of a token-threaded function with the token `k`, inside `[pure]`
withTokenVal :: VVal -> VVal -> VVal
withTokenVal v k
  = case v of
      Pure w -> Pure (withTokenVal w k)
      _ -> Tuple [v,k]

-- `let k : KCtx = cast-ev[𝟙, KCtx] ret ()`: a token where there is none (see "The effect
-- token" in `Syntax`)
makeToken :: Path -> K
makeToken k = Let k VToken (CastEv VUnit VToken (Ret UnitV))

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
