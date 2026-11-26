------------------------------------------------------------------------------
-- Copyright 2026, Anton Lorenzen
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-|
@lidar-lean@: Lean's client of lidar. It reads the dumps that Lean's @leanir@ writes (see
"Lidar.Lean.Dump"), elaborates their declarations into lidar's IR, lowers it, and writes C
against Lean's runtime (see "Lidar.Lean.CGen").
-}
module Main( main ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Exception( evaluate )
import Control.Monad( unless )
import GHC.Clock( getMonotonicTime )
import Text.Printf( hPrintf )
import System.Environment( getArgs )
import System.Exit( exitFailure )
import System.IO( hPutStrLn, stderr )
import Lidar
import Lidar.Force( NFData, rnf )
import Lidar.Lean.Dump
import Lidar.Lean.Elab
import Lidar.Lean.CGen
import Lidar.Lean.CGen.Ground( foldable )

usage :: String
usage = unlines
  [ "usage: lidar-lean [--check-all] [--timings] (--print-dump | --print-ir | --check | --print-lowered) <dump>"
  , "       lidar-lean [--check-all] [--timings] --emit-c <dump> -o <out.c>"
  , "  --print-dump     read the dump and print it back"
  , "  --print-ir       elaborate the dump and print the IR"
  , "  --check          elaborate the dump, check it and lower it, and report the errors"
  , "  --print-lowered  as --check, and print the lowered IR"
  , "  --emit-c         as --check, and write the C file against Lean's runtime"
  , "  --check-all      check the IR after every pass, not only after the last one"
  , "  --timings        print the time of each phase, pass and check to stderr" ]

data Flags = Flags{ checkAll :: Bool, timings :: Bool }

main :: IO ()
main = do
  args0 <- getArgs
  let flags = Flags{ checkAll = "--check-all" `elem` args0, timings = "--timings" `elem` args0 }
      args = filter (`notElem` ["--check-all","--timings"]) args0
      lower = lowerDump flags
  case args of
    ["--print-dump", file] -> readFileDump file >>= putStr . showDump
    ["--print-ir", file] -> do
      (prog,errs) <- timed flags "elab" . elabDump =<< readFileDump file
      putStrLn (ppr (prettyProgram (printable prog)))
      report [("elab",err) | err <- errs]
    ["--check", file] -> do
      (_,errs) <- lower =<< readFileDump file
      report errs
    ["--print-lowered", file] -> do
      (prog,errs) <- lower =<< readFileDump file
      putStrLn (ppr (prettyProgram (printable prog)))
      report errs
    ["--emit-c", file, "-o", out] -> do
      d <- readFileDump file
      (prog,errs) <- lower d
      report errs
      cgen <- timed flags "cgen" (cgenModule d prog)
      case cgen of
        Left cerrs -> report [("cgen",err) | err <- cerrs]
        Right c -> writeFile out c
    _ -> do hPutStrLn stderr usage; exitFailure

-- prints the errors, labeled by the phase that produced them, and fails if there are any
report :: [(String,String)] -> IO ()
report errs = do
  mapM_ (\(l,err) -> hPutStrLn stderr (l ++ ": " ++ err)) errs
  unless (null errs) exitFailure

readFileDump :: FilePath -> IO Dump
readFileDump file = do
  src <- readFile file
  case readDump file src of
    Left err -> do hPutStrLn stderr (file ++ ": " ++ err); exitFailure
    Right d  -> return d

-- The lowered program and the errors, labeled by the phase that produced them: elaboration,
-- the check after it, and lowering. Lean has no lazy constructors, no FIP annotations and so
-- no recursive groups to check them in.
lowerDump :: Flags -> Dump -> IO (Program,[(String,String)])
lowerDump flags d = do
  (prog,elabErrs) <- timed flags "elab" (elabDump d)
  typeErrs <- timed flags "check after elab" [("check after elab",err) | err <- checkTypes prog]
  (final,errs) <- if not (null typeErrs) then return (prog,typeErrs) else lowerProgram' prog
  return (final, [("elab",err) | err <- elabErrs] ++ errs)
  where
    opts = Options{ optReuse = True, optPeephole = True, optLazies = Lazies M.empty S.empty M.empty
                  , optFips = M.empty, optRecGroups = [], optCheckBetween = checkAll flags
                  , optFoldable = foldable, optExtractable = const False }
    lowerProgram' prog
      | timings flags = do ((final,errs,_),times) <- lowerProgramTimed opts prog
                           mapM_ (uncurry printTime) times
                           return (final,errs)
      | otherwise     = let (final,errs,_) = lowerProgram opts prog in return (final,errs)

-- evaluates a phase, and prints its time with `--timings`
timed :: NFData a => Flags -> String -> a -> IO a
timed flags name x
  | timings flags = do t0 <- getMonotonicTime
                       _ <- evaluate (rnf x)
                       t1 <- getMonotonicTime
                       printTime name (t1 - t0)
                       return x
  | otherwise     = return x

printTime :: String -> Double -> IO ()
printTime name t = hPrintf stderr "%-28s %8.3f s\n" name t

-- lidar prints the datatypes and signatures of the names that the module qualifies. Lean's
-- names are not qualified by their module, so print all of them.
printable :: Program -> Program
printable prog = prog{ progName = newModuleName "" }
