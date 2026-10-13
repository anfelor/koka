-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Drop specialization (after Perceus, before reuse).

  Perceus destructures a box that is still needed by borrowing its contents,
  duplicating them and then dropping the box:

    let^ box p = z in let y = dup p in drop z; e

  If the box is unique, the dup and the drop cancel out: its contents are taken
  without reference counting and its block becomes a reuse credit:

    let (y, r) = if-unique z then let box p @ r' = z in ret (p, r')
                             else let^ box p = z in let y' = dup p in drop z; ret (y', no-reuse n)
    in free r; e

  The shared branch is the original code. Freeing the credit releases the block, unless
  `Reuse` uses it for an allocation in `e`.
-}
module Backend.Typed.DropSpec( dropSpecProgram ) where

import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Monad
import Backend.Typed.Check( reuseSize )

type D a = State Int a

fresh :: String -> D Name
fresh s = state (\n -> (newHiddenName ("ds" ++ s ++ show n), n+1))

dropSpecProgram :: Program -> Program
dropSpecProgram prog
  = prog{ progDefs = [d{ defBody = evalState (dsE (defBody d)) 0 } | d <- progDefs prog] }

dsE :: VExpr -> D VExpr
dsE (Unbox Borrowed z p (Let y s (Ret (DupV (Var p'))) (Drop z' e)))
  | p == p', z == z', Right n <- reuseSize s
  = do q  <- fresh "q"
       y' <- fresh "y"
       r  <- fresh "r"
       r' <- fresh "r"
       e' <- dsE e
       let shared = Unbox Borrowed z p (Let y' s (Ret (DupV (Var p))) (Drop z (Ret (Pair (Var y') (NoReuse n)))))
       return (Let q (VProd s (VReuse n))
                 (IsUnique z (UnboxRu z p r' (Ret (Pair (Var p) (Var r')))) shared)
                 (Unpair Owned (Var q) y r (Free r e')))
dsE expr = descendE pure dsV (\_ e -> dsE e) expr

dsV :: VVal -> D VVal
dsV = descendV dsA dsV

dsA :: AVal -> D AVal
dsA (Lam ps r e) = Lam ps r <$> dsE e
dsA v = descendA pure dsA dsV v
