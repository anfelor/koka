-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Loads of case scrutinees (before Perceus).

  `[case]` only scrutinises a loaded value, never a sum in the contents of a box (a place).
  A case on a place `x` becomes a case on its copy:

    case_q x of { injᵢ x.injᵢ -> eᵢ }  ~>  let^ load x.load = x in case_q x.load of { injᵢ x.load.injᵢ -> eᵢ' }

  where eᵢ' uses `x.load` for `x`. Perceus then treats the copy as a part of `x`, borrowed
  from the box like `x`, and does not load it again.
-}
module Backend.Typed.Passes.Loads( loadsProgram ) where

import Data.Maybe( isJust )
import Data.Functor.Identity( Identity(..) )
import Backend.Typed.Syntax
import Backend.Typed.Common

loadsProgram :: Program -> Program
loadsProgram prog = prog{ progDefs = [d{ defBody = loadE (defBody d) } | d <- progDefs prog] }

loadE :: VExpr -> VExpr
loadE expr
  = case expr of
      CaseV _ (Var x) _ | isJust (boxOf x)
        -> let y = child x SLoad in Load x y (loadE (renamePath x y expr))
      _ -> runIdentity (descendE Identity (Identity . loadV) (\_ e -> Identity (loadE e)) expr)

loadV :: VVal -> VVal
loadV = mapV loadA loadV

loadA :: AVal -> AVal
loadA val
  = case val of
      Lam ps r e -> Lam ps r (loadE e)
      _ -> mapA id loadA loadV val
