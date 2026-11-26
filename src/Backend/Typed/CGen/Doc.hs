-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Wno-orphans #-}
-- String literals as documents under `OverloadedStrings`; import with `import Backend.Typed.CGen.Doc()`.
module Backend.Typed.CGen.Doc() where

import Data.String( IsString(..) )
import Lib.PPrint( Doc, string )

-- like `string`, a newline is a `line`
instance IsString Doc where
  fromString = string
