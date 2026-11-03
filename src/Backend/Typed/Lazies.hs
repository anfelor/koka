-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- The metadata of lazy types that elaboration (`Elab.Lazy`) passes to `Passes.Lazy`.
module Backend.Typed.Lazies( Lazies(..) ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Common.Name( Name )
import Backend.Typed.Syntax

-- The `lazy-C` functions with the tag of their constructor, the size of its cell and its
-- fields (with the padding, see `Elab.TypeInfo.conFieldTypes`), the
-- `lazy-eval-locked` functions, and the tag of the indirection ι of each lazy type.
data Lazies = Lazies{ lzCons :: M.Map Name (Int,Int,[VType]), lzLocked :: S.Set Name
                    , lzIndirect :: M.Map Name Int }
