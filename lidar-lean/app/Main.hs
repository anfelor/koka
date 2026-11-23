------------------------------------------------------------------------------
-- Copyright 2026, Anton Lorenzen
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-|
@lidar-lean@: Lean's client of lidar. For now it only reads the dumps that Lean's @leanir@
writes (see "Lidar.Lean.Dump").
-}
module Main( main ) where

import System.Environment( getArgs )
import System.Exit( exitFailure )
import System.IO( hPutStrLn, stderr )
import Lidar.Lean.Dump

usage :: String
usage = unlines
  [ "usage: lidar-lean --print-dump <dump>"
  , "  --print-dump   read the dump and print it back" ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--print-dump", file] -> do
      src <- readFile file
      case readDump file src of
        Left err -> do hPutStrLn stderr (file ++ ": " ++ err); exitFailure
        Right d  -> putStr (showDump d)
    _ -> do hPutStrLn stderr usage; exitFailure
