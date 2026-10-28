-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Internal names shared by the Core and typed IR passes.
module Backend.Typed.Names( nameUnreachable, isJoinName ) where

import Common.Name

-- marks an impossible alternative in Core; elaboration turns it into `[unreachable]`
nameUnreachable :: Name
nameUnreachable = newHiddenName "typed-unreachable"

isJoinName :: Name -> Bool
isJoinName x = hiddenNameStartsWith x "join"
