-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-- Assemble the typed IR definitions of named Koka datatypes.
module Backend.Typed.Elab.Types( typeDefs ) where

import qualified Data.Map as M
import qualified Common.NameMap as NM
import Common.Name( isLazyIndirectConName )
import Common.Syntax( dataDefIsOpen, Platform )
import Core.Core( conReprAllocSize, getConRepr )
import Kind.Newtypes
import Type.Type( typevarId, conInfoName, conInfoIsLazy )
import Backend.Typed.Syntax
import Backend.Typed.TypeInfo

refBody :: Newtypes -> DataInfo -> Tr (Maybe AType)
refBody nt info
  | dataDefIsOpen (dataInfoDef info) || null (dataInfoConstrs info) = Right Nothing
  | otherwise = Just . foldr1 ASum <$> mapM (conShape nt vargs) (dataInfoConstrs info)
  where
    vargs = map (AVar . typevarId) (filter tvarStar (dataInfoParams info))

typeDefs :: Platform -> Newtypes -> TypeDefs
typeDefs platform nt
  = M.fromList [(dataInfoName info, d) | (_,info) <- NM.toList (newtypesTypeDefs nt), not (isValueInfo info), Right d <- [typeDef platform nt info]]

typeDef :: Platform -> Newtypes -> DataInfo -> Tr TypeDef
typeDef platform nt info
  = do body <- refBody nt info
       return (TypeDef (dataInfoName info) (map typevarId (filter tvarStar (dataInfoParams info))) body (lazyInfo platform info))

lazyInfo :: Platform -> DataInfo -> Maybe LazyInfo
lazyInfo platform info
  = case [i | (i,con) <- zip [0..] cons, isLazyIndirectConName (conInfoName con)] of
      (i:_) -> Just (LazyInfo i [(conInfoIsLazy con, conReprAllocSize platform (getConRepr info con)) | con <- cons])
      []    -> Nothing
  where
    cons = dataInfoConstrs info
