-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{- Conversion between Koka's names and the names of the lidar IR.

  Both have the same fields and hash, so conversion preserves equality and order.
  `lidarNamesAgree` checks this on lidar's primitive names and its name functions.
-}
module Backend.Typed.LidarName( toLidar, fromLidar, lidarNamesAgree ) where

import Common.Name
import qualified Common.NamePrim as K
import qualified Lidar.Name as L
import qualified Lidar.Prim as L

toLidar :: Name -> L.Name
toLidar name = L.newLocallyQualified (nameModule name) (nameLocalQual name) (nameStem name)

fromLidar :: L.Name -> Name
fromLidar name = newLocallyQualified (L.nameModule name) (L.nameLocalQual name) (L.nameStem name)

-- | Pairs of names that Koka and lidar each construct themselves.
namePairs :: [(Name,L.Name)]
namePairs
  = [ (K.nameCoreHnd, L.nameCoreHnd)
    , (K.nameTpInt, L.nameTpInt)
    , (K.nameTpString, L.nameTpString)
    , (K.nameYieldExtend, L.nameYieldExtend)
    , (K.namePatternMatchError, L.namePatternMatchError)
    , (K.nameLazyMemoize, L.nameLazyMemoize)
    , (K.nameLazyMemoizeTarget, L.nameLazyMemoizeTarget)
    , (newHiddenName "x", L.newHiddenName "x")
    , (makeHiddenName "loop" (newName "f"), L.makeHiddenName "loop" (L.newName "f"))
    , (newLocallyQualified "std/core" "int" "+", L.newLocallyQualified "std/core" "int" "+")
    , (newName "Abc", L.newName "Abc")
    ]

-- | Whether converted names show, compare and parse as in Koka.
lidarNamesAgree :: Bool
lidarNamesAgree
  = and [ toLidar k == l && show k == show l && fromLidar l == k
          && L.readQualifiedName (show l) == toLidar (readQualifiedName (show k))
        | (k,l) <- namePairs ]
    && and [ compare k1 k2 == compare l1 l2 && compare (toLidar k1) (toLidar k2) == compare l1 l2
           | (k1,l1) <- namePairs, (k2,l2) <- namePairs ]
