------------------------------------------------------------------------------
-- Copyright 2026, Anton Lorenzen
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-|
@lidar-lean@: Lean's client of lidar. It reads the dumps that Lean's @leanir@ writes (see
"Lidar.Lean.Dump") and elaborates their declarations into lidar's IR.
-}
module Main( main ) where

import qualified Data.Map as M
import System.Environment( getArgs )
import System.Exit( exitFailure )
import System.IO( hPutStrLn, stderr )
import Lidar
import Lidar.Lean.Dump
import Lidar.Lean.Decls

usage :: String
usage = unlines
  [ "usage: lidar-lean (--print-dump | --print-ir) <dump>"
  , "  --print-dump   read the dump and print it back"
  , "  --print-ir     print the datatypes and signatures of the dump in lidar's IR" ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--print-dump", file] -> readFileDump file >>= putStr . showDump
    ["--print-ir", file] -> readFileDump file >>= putStrLn . ppr . prettyProgram . printable . program
    _ -> do hPutStrLn stderr usage; exitFailure

readFileDump :: FilePath -> IO Dump
readFileDump file = do
  src <- readFile file
  case readDump file src of
    Left err -> do hPutStrLn stderr (file ++ ": " ++ err); exitFailure
    Right d  -> return d

program :: Dump -> Program
program d
  = Program (newModuleName (dumpModule d)) (dTypes ds) (dSigs ds) M.empty (Foreign [] [] []) []
  where ds = declsOf d

-- lidar prints the datatypes and signatures of the names that the module qualifies. Lean's
-- names are not qualified by their module, so print all of them.
printable :: Program -> Program
printable prog = prog{ progName = newModuleName "" }
