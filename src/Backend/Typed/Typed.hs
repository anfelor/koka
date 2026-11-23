-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

module Backend.Typed.Typed( typedFromCore ) where

import Data.List( nubBy )
import Data.Function( on )
import qualified Data.Map as M
import qualified Data.Set as S
import Common.Failure( assertion )
import Common.Unique
import qualified Common.Syntax as Syntax
import Lidar.Name( Name )
import Kind.Newtypes
import qualified Core.Core as C
import Lidar.Syntax
import Backend.Typed.LidarName( toLidar, lidarNamesAgree )
import Lidar.Passes.Contify( contifyProgram )
import Backend.Typed.Elab.Match( matchCore )
import Lidar.Passes.Anf( anfProgram )
import Backend.Typed.Elab.FromCore( elabProgram )
import Backend.Typed.Elab.Lazy( lazyFuns )
import Lidar.Passes.Lazy( lazyProgram )
import Lidar.Passes.CheckTypes( checkProgram, checkTypes )
import Lidar.Passes.Simplify( simplifyProgram )
import Lidar.Passes.Yields( yieldsProgram )
import Lidar.Passes.Perceus( perceusProgram )
import Lidar.Passes.TailRec( tailRecProgram, loopWorkerName )
import Lidar.Passes.UniqueJoins( uniqueJoinsProgram )
import Lidar.Passes.Reuse( reuseProgram )
import Lidar.Passes.ExpandReuse( expandReuseProgram )
import Lidar.Passes.FillCredits( fillCreditsProgram )
import Lidar.Passes.DropSpec( dropSpecProgram )
import Lidar.Passes.Match( matchProgram )
import Lidar.Passes.SinkJoins( sinkJoinsProgram )
import Lidar.Passes.JoinArgs( joinArgsProgram )
import Lidar.Passes.Inline( inlineProgram )
import Lidar.Passes.Paths( pathsProgram )
import Lidar.Passes.Peephole( peepholeProgram )
import Lidar.Passes.CheckLinear( checkLinear )
import Lidar.Passes.CheckFip( checkFip )

-- returns the lowered program, its errors and its warnings, labeled by the phase that produced them
typedFromCore :: Bool -> Newtypes -> Foreign -> [C.Core] -> Int -> C.Core -> (Program,[(String,String)],[(String,String)])
typedFromCore enableReuse nt ffi imports uniq core
  = assertion "Backend.Typed.Typed: lidar names differ from Koka's" lidarNamesAgree $
    let (acore,_)              = runUnique uniq (matchCore nt core)
        (eprog,elabErrs,notes) = elabProgram nt ffi imports acore
        lazies                 = lazyFuns nt (progTypes eprog)
        pipeline               =
          [ Require "check" checkProgram
          , purePass "paths" pathsProgram
          , Pass "lazy" (lazyProgram lazies)
          , Pass "contify" contifyProgram
          , Pass "anf" anfProgram
          , purePass "simplify" simplifyProgram
          , purePass "yields" yieldsProgram
          , Require "linear" checkLinear
          , Pass "perceus" perceusProgram
          , purePass "tailrec" (tailRecProgram (fipsOf (core:imports)))
          , purePass "uniquejoins" uniqueJoinsProgram
          , Pass "dropspec" dropSpecProgram
          ]
          -- Without reuse every constructor allocates, so FIP is checked only with reuse.
          ++ whenReuse
             [ Advise "fip" (checkFip (fipsOf (core:imports)) (groupsOf core))
             , Pass "reuse" reuseProgram
             ]
          ++ [ Pass "match" matchProgram
             , purePass "sinkjoins" sinkJoinsProgram
             , purePass "joinargs" joinArgsProgram
             ]
          ++ whenReuse
             [ purePass "fillcredits" fillCreditsProgram
             , purePass "expandreuse" expandReuseProgram
             ]
          ++ [Pass "inline" inlineProgram]
          ++ [Pass "peephole" peepholeProgram | null elabErrs]
        -- Elaboration does not name paths (Paths does), so only its types are checked.
        typeErrs               = label "check after elab" (checkTypes eprog)
        (final,errs,warnings)  = if null typeErrs then runPipeline eprog pipeline else (eprog,typeErrs,[])
    in (final, label "elab" elabErrs ++ errs, warnings ++ label "note" notes)
  where
    purePass name pass = Pass name (\prog -> (pass prog,[]))
    whenReuse steps = if enableReuse then steps else []

-- the FIP annotations of the functions and their tail-recursive workers
fipsOf :: [C.Core] -> M.Map Name Fip
fipsOf cores
  = withWorkers $ M.fromList ([(toLidar (C.defName d), elabFip fip) | c <- cores, d <- C.flattenDefGroups (C.coreProgDefs c), Syntax.DefFun _ fip <- [C.defSort d]]
                ++ [(toLidar (C.externalName x), elabFip (C.externalFip x)) | c <- cores, x@(C.External{}) <- C.coreProgExternals c])
  where
    withWorkers fips = M.union fips (M.mapKeys loopWorkerName fips)

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

-- the recursive group of each recursive definition
groupsOf :: C.Core -> M.Map Name (S.Set Name)
groupsOf core
  = M.fromList [(n, names) | C.DefRec ds <- C.coreProgDefs core, let names = S.fromList (map (toLidar . C.defName) ds), d <- ds
                            , let f = toLidar (C.defName d), n <- [f, loopWorkerName f]]

type Checker = Program -> [String]

-- Require and Advise add a check to the result of every subsequent pass:
-- a required check reports errors, an advisory check warnings.
data PipelineStep = Pass String (Program -> (Program,[String]))
                  | Require String Checker
                  | Advise String Checker

-- Stop at the first failing pass or required check, so that the errors identify the pass
-- responsible. Report each warning only after the first pass where it appears.
runPipeline :: Program -> [PipelineStep] -> (Program,[(String,String)],[(String,String)])
runPipeline prog0 steps0
  = let (final,errs,warnings) = go [] [] prog0 steps0
    in (final,errs,nubBy ((==) `on` snd) warnings)
  where
    go _ _ prog [] = (prog,[],[])
    go required advisory prog (Require name check:steps)
      = go (required ++ [(name,check)]) advisory prog steps
    go required advisory prog (Advise name check:steps)
      = go required (advisory ++ [(name,check)]) prog steps
    go required advisory prog (Pass name pass:steps)
      = let (prog',errs) = pass prog
            checkAfter (kind,check) = label (kind ++ " after " ++ name) (check prog')
        in case dropWhile null (label name errs : map checkAfter required) of
             firstErrs:_ -> (prog',firstErrs,[])
             [] -> let (final,errors,warnings) = go required advisory prog' steps
                   in (final,errors,concatMap checkAfter advisory ++ warnings)

label :: String -> [String] -> [(String,String)]
label l msgs = [(l,msg) | msg <- msgs]
