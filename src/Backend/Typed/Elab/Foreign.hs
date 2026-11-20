-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- The C code of a module's `extern include` and `extern import` declarations, as the C backend
-- includes it (`Backend.C.FromCore.genModule`).
module Backend.Typed.Elab.Foreign( foreignOf ) where

import Data.Char( isSpace )
import Common.File( normalizeWith )
import Common.Syntax( BuildType )
import qualified Core.Core as C
import Backend.Typed.Syntax

foreignOf :: BuildType -> FilePath -> C.Core -> Foreign
foreignOf buildType sourceDir core
  = Foreign{ forHeader    = concatMap (inline "header-include-inline") exts
           , forHeaderEnd = concatMap (inline "header-end-include-inline") exts
           , forSource    = concatMap include exts ++ concatMap (inline "include-inline") exts }
  where
    exts = C.coreProgExternals core

    inline key ext
      = case C.externalImportLookup buildType key ext of
          Just content -> [dropWhile isSpace content]
          Nothing -> []

    include ext
      = case C.externalImportLookup buildType "include" ext of
          Just path@('<':_) -> ["#include " ++ path]
          Just path | null sourceDir -> ["#include \"" ++ path ++ "\""]
                    | otherwise -> ["#include \"" ++ normalizeWith '/' sourceDir ++ "/" ++ path ++ "\""]
          Nothing -> []
