-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
-- Licensed under the Apache License, Version 2.0.
-----------------------------------------------------------------------------

-- Group the dups of a local at its first dup in a straight-line block.
-- Run after DropSpec and reuse, which depend on the placement of individual dups.
module Lidar.Passes.CoalesceRC( coalesceRCProgram ) where

import qualified Data.Map.Strict as M
import Lidar.Syntax
import Lidar.Passes.Common( mapAll, mapLams )

coalesceRCProgram :: Program -> Program
coalesceRCProgram prog = prog{ progDefs = [d{ defBody = block (defBody d) } | d <- progDefs prog] }
  where
    block = snd . scan M.empty

    -- Accumulate counts going forward. On the way back, only the first dup of
    -- each path reads its total. Paths are bound once in a scope (Paths).
    scan counts expr = case expr of
      Dup n x e
        | n <= maxBound - old ->
          let (totals,body) = scan (M.insert x (old + n) counts) e
          in (totals, if old == 0 then Dup (totals M.! x) x body else body)
        | otherwise -> (counts, block expr)
        where old = M.findWithDefault 0 x counts
      Let x t rhs e | straight rhs -> next (Let x t (nested rhs)) e
      LetGlob x g ts e -> next (LetGlob x g ts) e
      Proj v i x e   -> next (Proj (value v) i x) e
      Deref v x e    -> next (Deref (value v) x) e
      LetCast v t x e -> next (LetCast (value v) t x) e
      Unpack v ts x e -> next (Unpack (value v) ts x) e
      Unbox z x e    -> next (Unbox z x) e
      Unroll z x e   -> next (Unroll z x) e
      Unscalar z x e -> next (Unscalar z x) e
      Drop x e       -> next (Drop x) e
      Free r e       -> next (Free r) e
      _              -> (counts, nested expr)
      where
        next wrap e = let (totals,body) = scan counts e in (totals,wrap body)

    nested = mapAll (const block)
    value = mapLams (\_ _ -> block)

    -- A later dup keeps a reference alive across a call. If the callee
    -- receives another owned reference to that object, it already sees it
    -- shared. A borrowed argument can alias the sole surviving reference,
    -- so end the block there. Closure applications take owned arguments.
    straight rhs = case rhs of
      Ret{} -> True
      App{} -> True
      Call f _ _ | Just (SigFun _ ps _ _) <- M.lookup f (progSigs prog) ->
        all ((== Owned) . fst) ps
      _ -> False
