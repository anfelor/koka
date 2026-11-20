-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- The typed C driver: runs the `Typed` pipeline on a module and generates its C (`CGen`).
-- The typed C of a module includes its regular C (`Backend.C.FromCore`) and
-- is compiled in its place.
module Backend.Typed.CFromCore( typedCFromCore, cgenMain, ktFileName ) where

import Data.List( intercalate )
import qualified Data.Map as M
import qualified Data.Set as S
import Lib.PPrint( Doc, (<.>), linebreak )
import Common.Name
import Common.Syntax( DefInline(..) )
import qualified Common.NameMap as NM
import Kind.Newtypes( Newtypes, newtypesTypeDefs )
import qualified Core.Core as C
import Backend.Typed.Typed( typedFromCore )
import Backend.Typed.Pretty( prettyProgram )
import Backend.Typed.CGen.CGen( CEnv(..), External(..), cgenModule, cgenMain, ktInitName, ktFileName )

-- Returns the final IR (for debugging), the diagnostics, and either an error or the header
-- and source. `coreC` is the Core that the C backend compiles; its
-- definitions decide which functions are inlined from the header, as for the C backend.
typedCFromCore :: Bool -> Newtypes -> [C.Core] -> C.Core -> C.Core -> (Doc,[String],Either String (String,String))
typedCFromCore enableReuse newtypes imports coreC core
  = (prettyProgram tprog <.> linebreak, map diagnostic (errors ++ warnings), result)
  where
    modName                 = C.coreProgName core
    (tprog,errors,warnings) = typedFromCore enableReuse newtypes imports 1000000 core
    diagnostic (phase,msg)  = "typed " ++ phase ++ ": " ++ msg

    -- Warnings (such as FIP diagnostics) are advisory, like the frontend's FIP warnings.
    -- Errors invalidate the lowering boundary.
    result
      | not (null errors) = Left "typed backend validation failed; C generation stopped"
      | not (null errs)   = Left ("typed C generation failed: " ++ intercalate "\n" errs)
      | otherwise         = Right (hdr,csrc)
    (hdr,csrc,errs) = cgenModule cenv tprog

    cores   = core : imports
    importNames = map C.coreProgName imports
    externs = M.fromList [(C.externalName x, External (C.externalFormat x) (C.externalType x)) | c <- cores, x@(C.External{}) <- C.coreProgExternals c]
    cenv    = CEnv modName
                   ([moduleNameToPath modName ++ ".h"] ++ [ktFileName m ++ ".h" | m <- importNames])
                   (map ktInitName importNames)
                   externs newtypes (map snd (NM.toList (newtypesTypeDefs newtypes)) ++ [info | c <- cores, C.TypeDefGroup tds <- C.coreProgTypeDefs c, C.Data info <- tds])
                   -- as the C backend (`Backend.C.FromCore.genTopGroup`)
                   (S.fromList [C.defName d | C.DefNonRec d <- C.coreProgDefs coreC,
                                              C.defInline d == InlineAlways || C.isInlineable 5 d])
