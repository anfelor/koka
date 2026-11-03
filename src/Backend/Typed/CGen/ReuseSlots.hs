-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Reuse-slot analysis for described credits in typed C code generation.
module Backend.Typed.CGen.ReuseSlots( keptLeaves ) where

import Backend.Typed.Syntax
import Backend.Typed.Sources( Sources, sameBits )
import Backend.Typed.Traversal( child, fieldsAt, mapV )
import Backend.Typed.Types( collapse, leaves )
import Backend.Typed.Layout( layout, scanOf )
import Backend.Typed.CGen.Layout( leafSlots )

sameBitsV :: Sources -> VVal -> VVal
sameBitsV src v
  = case v of
      Var x -> Var (sameBits src x)
      _ -> mapV id (sameBitsV src) v

-- The tag and the scan size that the description of a credit records for its block, and for
-- each leaf of the new payload whether its C slot already holds its bits: the old payload has
-- a leaf at the same offset, with the same layout and the same value (`Inline` makes equal
-- values syntactically equal, so the payload names the variables of the description or their
-- copies, `sameBits`).
-- Payloads of different types can thus share slots. A dup preserves a field's bits, but its
-- reference-count effect must still run.
keptLeaves :: Sources -> Ty -> VType -> VVal -> Maybe (Maybe Int, Int, [Bool])
keptLeaves src rt t v
  = case rt of
      V (VReuse _ _ (Just (Contents k old ot)))
        -> let slots s w = zip (leafSlots (layout s)) (leafValues s w)
               kept = slots ot old
           in Just (k, scanOf (layout ot), [leaf `elem` kept | leaf <- slots t (sameBitsV src v)])
      _ -> Nothing

-- The value of each leaf of a value of type `t`, as a value in normal form (`collapse`) and
-- the index of a leaf in it: equal descriptions have equal bits. A variable of a product or
-- existential type is expanded into the variables at its parts. Sums stay whole fields, so
-- their inactive slots are kept safe.
leafValues :: VType -> VVal -> [(VVal,Int)]
leafValues t v
  = case (t,v) of
      (VProd fs, Tuple ws) -> concat (zipWith leafValues (map snd fs) ws)
      (VProd _, Var x) -> concat [leafValues s (Var y) | (y,_,s) <- fieldsAt x t]
      (VExists _ s, Pack _ _ w) -> leafValues s w
      (VExists _ s, Var x) -> leafValues s (Var (child x SPack))
      _ -> [(collapse v,i) | i <- [0 .. length (leaves t) - 1]]
