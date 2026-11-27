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
import Common.Name( isHiddenName, newModuleName )
import Common.NamePrim( nameCoreDebug, nameCoreHnd )
import qualified Common.Syntax as Syntax
import Kind.Newtypes
import Type.Type( splitFunScheme, splitFunType, expandSyn, isTypeTotal )
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
        extractable            = extractableOf (core:imports)
        opts                   = Options{ optReuse     = enableReuse
                                        , optPeephole  = null elabErrs
                                        , optLazies    = lazyFuns nt (progTypes eprog)
                                        , optFips      = fipsOf (core:imports)
                                        , optRecGroups = groupsOf core
                                        , optCheckBetween = checkAll
                                        , optFoldable  = const False
                                        , optExtractable = (`S.member` extractable) }
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

-- The functions whose calls `Passes.Closed` can initialise on demand: those whose type is total
-- (not `div`), with total function parameters, unlike `unsafe-total` and `delay`, which run
-- an effectful argument under a total type. Some primitives have a total type but read the
-- context or the identity of their arguments (`@evv-at`, `fresh-marker`, `yielding`,
-- `unsafe-ptr-eq`, the primitives of `std/core/lazy`, `@cctx-hole-create`): the modules of the
-- runtime are excluded, and so are the externals with internal names. The top-level values that
-- closed values can read: those of the same modules (total, as Koka's top-level values are).
extractableOf :: [C.Core] -> S.Set Name
extractableOf cores
  = S.fromList ([toLidar (C.defName d) | c <- cores, ordinary c, d <- C.flattenDefGroups (C.coreProgDefs c), pureFun (C.defType d) || isVal (C.defSort d)]
                ++ [toLidar (C.externalName x) | c <- cores, ordinary c, x@(C.External{}) <- C.coreProgExternals c
                                               , not (isHiddenName (C.externalName x)), pureFun (C.externalType x)])
  where
    ordinary c = C.coreProgName c `notElem` (nameCoreHnd : map newModuleName ["std/core/undiv","std/core/unsafe","std/core/lazy"])
    pureFun tp = case splitFunScheme tp of
                   Just (_,pars,eff,_) -> total eff && all (totalArg . snd) pars
                   Nothing -> False
    totalArg tp = maybe True (\(_,eff,_) -> total eff) (splitFunType (expandSyn tp))
    total eff = isTypeTotal (expandSyn eff)
    isVal sort = case sort of
                   Syntax.DefVal -> True
                   _ -> False

-- the recursive groups of the module
groupsOf :: C.Core -> [S.Set Name]
groupsOf core
  = [S.fromList (map (toLidar . C.defName) ds) | C.DefRec ds <- C.coreProgDefs core]
