-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- The typed C driver: runs the `Typed` pipeline on a module and generates its C (`CGen`),
-- which is compiled in place of its regular C (`Backend.C.FromCore`).
module Backend.Typed.CFromCore( typedCFromCore, cgenMain ) where

import Data.List( intercalate )
import Lib.PPrint( Doc, (<.>), linebreak, string )
import Common.Syntax( BuildType )
import Kind.Newtypes( Newtypes )
import qualified Core.Core as C
import Backend.Typed.Typed( typedFromCore )
import Backend.Typed.Elab.Foreign( foreignOf )
import Backend.Typed.Pretty( prettyProgram )
import Common.Name( Name )
import Backend.Typed.LidarName( toLidar )
import Backend.Typed.CGen.CGen( CEnv(..), cgenModule )
import qualified Backend.Typed.CGen.CGen as CGen

-- Returns the final IR (for debugging), the diagnostics, and either an error or the header
-- and source.
typedCFromCore :: BuildType -> FilePath -> Bool -> Newtypes -> [C.Core] -> C.Core -> (Doc,[String],Either String (String,String))
typedCFromCore buildType sourceDir enableReuse newtypes imports core
  = (string (show (prettyProgram tprog)) <.> linebreak, map diagnostic (errors ++ warnings), result)
  where
    modName                 = C.coreProgName core
    (tprog,errors,warnings) = typedFromCore enableReuse newtypes (foreignOf buildType sourceDir core) imports 1000000 core
    diagnostic (phase,msg)  = "typed " ++ phase ++ ": " ++ msg

    -- Warnings (such as FIP diagnostics) are advisory, like the frontend's FIP warnings.
    -- Errors invalidate the lowering boundary.
    result
      | not (null errors) = Left "typed backend validation failed; C generation stopped"
      | not (null errs)   = Left ("typed C generation failed: " ++ intercalate "\n" errs)
      | otherwise         = Right (hdr,csrc)
    (hdr,csrc,errs) = cgenModule cenv tprog

    cenv    = CEnv (toLidar modName) (map (toLidar . C.coreProgName) imports)

-- the entry point of a typed program (`CGen.cgenMain`)
cgenMain :: String -> Int -> Name -> Name -> String
cgenMain mainName stackSize progName entryName
  = CGen.cgenMain mainName stackSize (toLidar progName) (toLidar entryName)
