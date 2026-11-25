-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- The typed intermediate representation of Koka's typed backend, and its passes.

  The public API for clients: the IR and its names, printing and reading printed IR back,
  `checkTypes`, which checks a program before lowering, and `lowerProgram`, which runs the passes. Clients that build or
  analyse IR also import the helper modules (`Lidar.Types`, `Lidar.Traversal`, `Lidar.Layout`,
  `Lidar.Build`, `Lidar.Env`, `Lidar.Query`) directly.
-}
module Lidar
  ( -- * The IR
    module Lidar.Name
  , module Lidar.Syntax
    -- * Printing and parsing
  , ppr, prettyProgram
  , parseProgram, unknownA, unknownV
  , annotateProgram
    -- * Checking and lowering
  , checkTypes
  , Options(..), Lazies(..)
  , lowerProgram, lowerProgramTimed
  ) where

import Control.Exception( evaluate )
import Data.Functor.Identity( runIdentity )
import Data.IORef( newIORef, modifyIORef, readIORef )
import GHC.Clock( getMonotonicTime )

import Data.List( nubBy )
import Data.Function( on )
import qualified Data.Map as M
import qualified Data.Set as S
import Lidar.Name
import Lidar.Syntax
import Lidar.Env( Lazies(..) )
import Lidar.Force( rnf )
import Lidar.Pretty( ppr, prettyProgram )
import Lidar.Parse( parseProgram, unknownA, unknownV )
import Lidar.Annotate( annotateProgram )
import Lidar.Passes.Anf( anfProgram )
import Lidar.Passes.CheckFip( checkFip )
import Lidar.Passes.CheckLinear( checkLinear )
import Lidar.Passes.CheckTypes( checkProgram, checkTypes )
import Lidar.Passes.Closed( closedProgram )
import Lidar.Passes.Contify( contifyProgram )
import Lidar.Passes.DropSpec( dropSpecProgram )
import Lidar.Passes.ExpandReuse( expandReuseProgram )
import Lidar.Passes.FillCredits( fillCreditsProgram )
import Lidar.Passes.Inline( inlineProgram )
import Lidar.Passes.JoinArgs( joinArgsProgram )
import Lidar.Passes.Lazy( lazyProgram )
import Lidar.Passes.Match( matchProgram )
import Lidar.Passes.Paths( pathsProgram )
import Lidar.Passes.Peephole( peepholeProgram )
import Lidar.Passes.Perceus( perceusProgram )
import Lidar.Passes.Reuse( reuseProgram )
import Lidar.Passes.Simplify( simplifyProgram )
import Lidar.Passes.SinkJoins( sinkJoinsProgram )
import Lidar.Passes.TailRec( tailRecProgram, loopWorkerName )
import Lidar.Passes.UniqueJoins( uniqueJoinsProgram )
import Lidar.Passes.Yields( yieldsProgram )

-- what the client tells the passes about the program
data Options = Options
  { optReuse     :: Bool                -- ^ reuse memory (and check FIP annotations)
  , optPeephole  :: Bool                -- ^ run the final peephole pass
  , optLazies    :: Lazies              -- ^ the lazy constructors (`Passes.Lazy`)
  , optFips      :: M.Map Name Fip      -- ^ the FIP annotations of functions, incl. imported ones
  , optRecGroups :: [S.Set Name]        -- ^ the recursive groups of the module (for `CheckFip`)
  , optCheckBetween :: Bool             -- ^ run the required checks after every pass, not only
                                        --   after the last one (to find the pass that breaks them)
  , optFoldable  :: Name -> Bool        -- ^ the functions whose calls with ground arguments the
                                        --   client folds at compile time (`Passes.Closed`)
  , optFresh     :: Name -> Bool        -- ^ the datatypes whose values are built afresh every
                                        --   time, never extracted as closed values (`Passes.Closed`)
  }

type Lowered = (Program,[(String,String)],[(String,String)])

-- lowers a program for which `checkTypes` reports no errors; returns the lowered program,
-- its errors and its warnings, labeled by the pass that produced them
lowerProgram :: Options -> Program -> Lowered
lowerProgram opts prog = runIdentity (runPipeline (\_ _ -> return ()) opts prog)

-- `lowerProgram`, also returning the time in seconds of each pass and check, in the order they ran
lowerProgramTimed :: Options -> Program -> IO (Lowered,[(String,Double)])
lowerProgramTimed opts prog
  = do ref <- newIORef []
       let tick name work = do t0 <- getMonotonicTime
                               _ <- evaluate work
                               t1 <- getMonotonicTime
                               modifyIORef ref ((name,t1 - t0):)
       lowered <- runPipeline tick opts prog
       times <- readIORef ref
       return (lowered,reverse times)

pipeline :: Options -> [PipelineStep]
pipeline opts
  = [ Require "check" checkProgram
    , purePass "paths" pathsProgram
    , Pass "lazy" (lazyProgram (optLazies opts))
    , Pass "contify" contifyProgram
    , Pass "anf" anfProgram
    , Pass "simplify" simplifyProgram
    , purePass "yields" yieldsProgram
    , purePass "closed" (closedProgram (optFoldable opts) (optFresh opts))
    , Require "linear" checkLinear
    , Pass "perceus" perceusProgram
    , purePass "tailrec" (tailRecProgram fips)
    , purePass "uniquejoins" uniqueJoinsProgram
    , Pass "dropspec" dropSpecProgram
    ]
    -- Without reuse every constructor allocates, so FIP is checked only with reuse.
    ++ whenReuse
       [ Advise "fip" (checkFip fips groups)
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
    ++ [Pass "peephole" peepholeProgram | optPeephole opts]
  where
    purePass name pass = Pass name (\p -> (pass p,[]))
    whenReuse steps = if optReuse opts then steps else []
    -- the tail-recursive workers of `TailRec` share the annotation and group of their function
    fips = M.union (optFips opts) (M.mapKeys loopWorkerName (optFips opts))
    groups = M.fromList [(n, group) | group <- optRecGroups opts, f <- S.toList group, n <- [f, loopWorkerName f]]

type Checker = Program -> [String]

-- Require and Advise add a check to the result of every subsequent pass:
-- a required check reports errors, an advisory check warnings.
data PipelineStep = Pass String (Program -> (Program,[String]))
                  | Require String Checker
                  | Advise String Checker

-- Stop at the first failing pass or required check, so that the errors identify the pass
-- responsible. Report each warning only after the first pass where it appears.
-- Unless `optCheckBetween`, the required checks run only after the last pass.
-- `tick name work` is called with the full evaluation of each pass and check, in order.
runPipeline :: Monad m => (String -> () -> m ()) -> Options -> Program -> m Lowered
runPipeline tick opts prog0
  = do (final,errs,warnings) <- go [] [] prog0 (pipeline opts)
       return (final,errs,nubBy ((==) `on` snd) warnings)
  where
    go required _ prog []
      | optCheckBetween opts = return (prog,[],[])
      | otherwise = do errss <- mapM (runCheck "all passes" prog) required
                       return (prog,firstErrors errss,[])
    go required advisory prog (Require name check:steps)
      = go (required ++ [(name,check)]) advisory prog steps
    go required advisory prog (Advise name check:steps)
      = go required (advisory ++ [(name,check)]) prog steps
    go required advisory prog (Pass name pass:steps)
      = do let (prog',errs) = pass prog
               passErrs = label name errs
           tick name (rnf prog' `seq` rnf passErrs)
           errss <- if optCheckBetween opts then mapM (runCheck name prog') required else return []
           case firstErrors (passErrs : errss) of
             [] -> do warningss <- mapM (runCheck name prog') advisory
                      (final,errors,warnings) <- go required advisory prog' steps
                      return (final,errors,concat warningss ++ warnings)
             firstErrs -> return (prog',firstErrs,[])

    runCheck after prog (kind,check)
      = do let msgs = label (kind ++ " after " ++ after) (check prog)
           tick (kind ++ " after " ++ after) (rnf msgs)
           return msgs
    firstErrors errss = case dropWhile null errss of
                          errs:_ -> errs
                          []     -> []

label :: String -> [String] -> [(String,String)]
label l msgs = [(l,msg) | msg <- msgs]
