-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{- The names of Koka's runtime that the typed IR and its passes recognise.

  Each is defined exactly as in Koka's `Common.NamePrim`.
-}
module Lidar.Prim
  ( nameCoreHnd
  , nameTpInt, nameTpString
  , nameYieldExtend
  , nameLazyMemoize, nameLazyMemoizeTarget
  ) where

import Lidar.Name

nameCoreHnd, nameCoreTypes :: Name
nameCoreHnd   = newModuleName "std/core/hnd"
nameCoreTypes = newModuleName "std/core/types"

coreTypesName, coreHndName :: String -> Name
coreTypesName s = qualify nameCoreTypes (newName s)
coreHndName s   = qualify nameCoreHnd (newName s)

nameTpInt, nameTpString :: Name
nameTpInt    = coreTypesName "int"
nameTpString = coreTypesName "string"

nameYieldExtend :: Name
nameYieldExtend = coreHndName "yield-extend"

nameLazyMemoize, nameLazyMemoizeTarget :: Name
nameLazyMemoize       = newQualified "std/core/lazy" "memoize"
nameLazyMemoizeTarget = newQualified "std/core/lazy" "memoize-target"
