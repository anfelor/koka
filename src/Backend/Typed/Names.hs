-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-- Internal names shared by the Core and typed IR passes.
module Backend.Typed.Names( nameUnreachable, nameSetCtxPath, nameLazyFree, isJoinName ) where

import Common.Name

nameUnreachable :: Name
nameUnreachable = newHiddenName "typed-unreachable"

nameSetCtxPath :: Name
nameSetCtxPath = newHiddenName "typed-set-ctx-path"

isJoinName :: Name -> Bool
isJoinName x = hiddenNameStartsWith x "join"

nameLazyFree :: Name
nameLazyFree = newHiddenName "typed-lazy-free"
