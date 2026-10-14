-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Whole-program type validation; Query implements the typing rules.
module Backend.Typed.Check( checkProgram ) where

import qualified Data.Map as M
import Backend.Typed.Syntax
import Backend.Typed.Query( Env, envOf, checkE )

checkProgram :: Program -> [String]
checkProgram prog
  = [show (defName d) ++ ": " ++ err | d <- progDefs prog, Left err <- [checkDef (envOf prog) d]]

checkDef :: Env -> Def -> Either String ()
checkDef env def
  = case def of
      DefFun _ _ args res body -> checkE env (M.fromList [(x,V t) | (x,_,t) <- args]) M.empty body res
      DefVal _ _ t body        -> checkE env M.empty M.empty body t
