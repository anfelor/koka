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
import Control.Monad( unless )
import System.Environment( getArgs )
import System.Exit( exitFailure )
import System.IO( hPutStrLn, stderr )
import Lidar
import Lidar.Lean.Dump
import Lidar.Lean.Elab
import Lidar.Lean.CGen

usage :: String
usage = unlines
  [ "usage: lidar-lean (--print-dump | --print-ir | --check | --print-lowered) <dump>"
  , "       lidar-lean --emit-c <dump> -o <out.c>"
  , "  --print-dump     read the dump and print it back"
  , "  --print-ir       elaborate the dump and print the IR"
  , "  --check          elaborate the dump, check it and lower it, and report the errors"
  , "  --print-lowered  as --check, and print the lowered IR"
  , "  --emit-c         as --check, and write the C file against Lean's runtime" ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--print-dump", file] -> readFileDump file >>= putStr . showDump
    ["--print-ir", file] -> do
      (prog,errs) <- elabDump <$> readFileDump file
      putStrLn (ppr (prettyProgram (printable prog)))
      report [("elab",err) | err <- errs]
    ["--check", file] -> do
      (_,errs) <- lower <$> readFileDump file
      report errs
    ["--print-lowered", file] -> do
      (prog,errs) <- lower <$> readFileDump file
      putStrLn (ppr (prettyProgram (printable prog)))
      report errs
    ["--emit-c", file, "-o", out] -> do
      d <- readFileDump file
      let (prog,errs) = lower d
      report errs
      case cgenModule d prog of
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
lower :: Dump -> (Program,[(String,String)])
lower d
  = (final, [("elab",err) | err <- elabErrs] ++ errs)
  where
    (prog,elabErrs) = elabDump d
    opts = Options{ optReuse = True, optPeephole = True, optLazies = Lazies M.empty S.empty M.empty
                  , optFips = M.empty, optRecGroups = [] }
    typeErrs = [("check after elab",err) | err <- checkTypes prog]
    (final,errs) = if null typeErrs then (\(p,es,_) -> (p,es)) (lowerProgram opts prog) else (prog,typeErrs)

-- lidar prints the datatypes and signatures of the names that the module qualifies. Lean's
-- names are not qualified by their module, so print all of them.
printable :: Program -> Program
printable prog = prog{ progName = newModuleName "" }
