-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-- Reassociate nested lets. Roots are unique throughout a definition, so moving a
-- let out of its bound computation cannot capture a variable in its continuation.
module Backend.Typed.Passes.Anf( anfProgram ) where

import Data.Functor.Identity( Identity(..) )
import Backend.Typed.Syntax
import Backend.Typed.Common

anfProgram :: Program -> Program
anfProgram prog = prog{ progDefs = [d{ defBody = anfE (defBody d) } | d <- progDefs prog] }

anfE :: VExpr -> VExpr
anfE expr = case expr of
  Let x t e1 e2 -> bind x t (anfE e1) (anfE e2)
  _ -> runIdentity (descendE Identity (Identity . anfV) (\_ -> Identity . anfE) expr)

bind :: Path -> VType -> VExpr -> VExpr -> VExpr
bind x t (Let y s e1 e2) body = Let y s e1 (bind x t e2 body)
bind x t e body = Let x t e body

anfV :: VVal -> VVal
anfV = mapV anfA anfV

anfA :: AVal -> AVal
anfA (Lam ps r e) = Lam ps r (anfE e)
anfA a = mapA id anfA anfV a
