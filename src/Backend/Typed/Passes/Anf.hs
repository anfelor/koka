-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-- The IR already separates computations from values. Normalize sequencing by
-- reassociating nested let bindings; freshen lifted binders to avoid capture.
module Backend.Typed.Passes.Anf( anfProgram ) where

import qualified Data.Map as M
import Control.Monad.State
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common

anfProgram :: Program -> Program
anfProgram prog = prog{ progDefs = map run (progDefs prog) }
  where
    run def = def{ defBody = evalState (anfE (defBody def)) 0 }

fresh :: State Int Name
fresh = state (\n -> (newHiddenName ("anf" ++ show n),n+1))

anfE :: VExpr -> State Int VExpr
anfE expr
  = case expr of
      Let x t e1 e2 -> do e1' <- anfE e1
                          e2' <- anfE e2
                          bind x t e1' e2'
      _ -> descendE pure anfV (\_ -> anfE) expr

bind :: Name -> VType -> VExpr -> VExpr -> State Int VExpr
bind x t (Let y s e1 e2) body
  = do z <- fresh
       rest <- bind x t (renameE (M.singleton y z) e2) body
       return (Let z s e1 rest)
bind x t e body = return (Let x t e body)

anfV :: VVal -> State Int VVal
anfV = descendV anfA anfV

anfA :: AVal -> State Int AVal
anfA (Lam ps r e) = Lam ps r <$> anfE e
anfA a = descendA pure anfA anfV a
