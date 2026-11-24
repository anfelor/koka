-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

module Backend.Typed.Typed( typedFromCore ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List( isPrefixOf )
import Common.Failure( assertion )
import Common.Unique
import Common.NamePrim( nameCoreDebug )
import qualified Common.Syntax as Syntax
import Kind.Newtypes
import qualified Core.Core as C
import Lidar( Name, Program(..), Foreign, Fip(..), FipAlloc(..), Options(..), checkTypes, lowerProgram )
import Backend.Typed.LidarName( toLidar, lidarNamesAgree )
import Backend.Typed.Elab.Match( matchCore )
import Backend.Typed.Elab.FromCore( elabProgram )
import Backend.Typed.Elab.Lazy( lazyFuns )

-- returns the lowered program, its errors and its warnings, labeled by the phase that produced them
typedFromCore :: Bool -> Bool -> Newtypes -> Foreign -> [C.Core] -> Int -> C.Core -> (Program,[(String,String)],[(String,String)])
typedFromCore enableReuse checkAll nt ffi imports uniq core
  = assertion "Backend.Typed.Typed: lidar names differ from Koka's" lidarNamesAgree $
    let (acore,_)              = runUnique uniq (matchCore nt core)
        (eprog,elabErrs,notes) = elabProgram nt ffi imports acore
        opts                   = Options{ optReuse     = enableReuse
                                        , optPeephole  = null elabErrs
                                        , optLazies    = lazyFuns nt (progTypes eprog)
                                        , optFips      = fipsOf (core:imports)
                                        , optRecGroups = groupsOf core
                                        , optCheckBetween = checkAll }
        -- Elaboration does not name paths (Paths does), so only its types are checked.
        typeErrs               = label "check after elab" (checkTypes eprog)
        (final,errs,warnings)  = if null typeErrs then lowerProgram opts eprog else (eprog,typeErrs,[])
    in (final, label "elab" elabErrs ++ errs, filter (not . trusted) warnings ++ label "note" notes)
  where
    label l msgs = [(l,msg) | msg <- msgs]
    -- as in Koka's own checker, the FIP annotations of `std/core/debug` are trusted
    trusted (l,_) = C.coreProgName core == nameCoreDebug && "fip " `isPrefixOf` l

-- the FIP annotations of the functions
fipsOf :: [C.Core] -> M.Map Name Fip
fipsOf cores
  = M.fromList ([(toLidar (C.defName d), elabFip fip) | c <- cores, d <- C.flattenDefGroups (C.coreProgDefs c), Syntax.DefFun _ fip <- [C.defSort d]]
                ++ [(toLidar (C.externalName x), elabFip (C.externalFip x)) | c <- cores, x@(C.External{}) <- C.coreProgExternals c])

elabFip :: Syntax.Fip -> Fip
elabFip fip
  = case fip of
      Syntax.Fip n    -> Fip (alloc n)
      Syntax.Fbip n t -> Fbip (alloc n) t
      Syntax.NoFip t  -> NoFip t
  where
    alloc n = case n of
                Syntax.AllocAtMost i  -> AllocAtMost i
                Syntax.AllocFinitely  -> AllocFinitely
                Syntax.AllocUnlimited -> AllocUnlimited

-- the recursive groups of the module
groupsOf :: C.Core -> [S.Set Name]
groupsOf core
  = [S.fromList (map (toLidar . C.defName) ds) | C.DefRec ds <- C.coreProgDefs core]
