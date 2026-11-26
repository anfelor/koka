-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-- Full evaluation of the IR, so that the pipeline can time each pass on its own.
{-# LANGUAGE DeriveGeneric, DeriveAnyClass, StandaloneDeriving, DerivingStrategies #-}
module Lidar.Force( NFData, rnf ) where

import Control.DeepSeq( NFData(..), rwhnf )
import GHC.Generics( Generic )
import Lidar.Name( Name )
import Lidar.Syntax

-- the fields of a name are strict, and its hashes force its strings
instance NFData Name where rnf = rwhnf

deriving stock instance Generic Mode
deriving stock instance Generic AType
deriving stock instance Generic Prim
deriving stock instance Generic Side
deriving stock instance Generic VType
deriving stock instance Generic Raw
deriving stock instance Generic IntType
deriving stock instance Generic Sign
deriving stock instance Generic Width
deriving stock instance Generic Contents
deriving stock instance Generic Fill
deriving stock instance Generic Ty
deriving stock instance Generic TypeDef
deriving stock instance Generic TypeBody
deriving stock instance Generic ConLabel
deriving stock instance Generic Lit
deriving stock instance Generic Constant
deriving stock instance Generic Path
deriving stock instance Generic Step
deriving stock instance Generic Con
deriving stock instance Generic Field
deriving stock instance Generic AVal
deriving stock instance Generic VVal
deriving stock instance Generic JoinDef
deriving stock instance Generic VExpr
deriving stock instance Generic Def
deriving stock instance Generic DefInline
deriving stock instance Generic ValInit
deriving stock instance Generic Fip
deriving stock instance Generic FipAlloc
deriving stock instance Generic Sig
deriving stock instance Generic Extern
deriving stock instance Generic KType
deriving stock instance Generic Foreign
deriving stock instance Generic Program

deriving anyclass instance NFData Mode
deriving anyclass instance NFData AType
deriving anyclass instance NFData Prim
deriving anyclass instance NFData Side
deriving anyclass instance NFData VType
deriving anyclass instance NFData Raw
deriving anyclass instance NFData IntType
deriving anyclass instance NFData Sign
deriving anyclass instance NFData Width
deriving anyclass instance NFData Contents
deriving anyclass instance NFData Fill
deriving anyclass instance NFData Ty
deriving anyclass instance NFData TypeDef
deriving anyclass instance NFData TypeBody
deriving anyclass instance NFData ConLabel
deriving anyclass instance NFData Lit
deriving anyclass instance NFData Constant
deriving anyclass instance NFData Path
deriving anyclass instance NFData Step
deriving anyclass instance NFData Con
deriving anyclass instance NFData Field
deriving anyclass instance NFData AVal
deriving anyclass instance NFData VVal
deriving anyclass instance NFData JoinDef
deriving anyclass instance NFData VExpr
deriving anyclass instance NFData Def
deriving anyclass instance NFData DefInline
deriving anyclass instance NFData ValInit
deriving anyclass instance NFData Fip
deriving anyclass instance NFData FipAlloc
deriving anyclass instance NFData Sig
deriving anyclass instance NFData Extern
deriving anyclass instance NFData KType
deriving anyclass instance NFData Foreign
deriving anyclass instance NFData Program
