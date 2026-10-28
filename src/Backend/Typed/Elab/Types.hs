-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Assemble the typed IR definitions of named Koka datatypes.
module Backend.Typed.Elab.Types( typeDefs ) where

import qualified Data.Map as M
import qualified Common.NameMap as NM
import Control.Monad( forM_, unless )
import Common.Name( isLazyIndirectConName )
import Common.Syntax( dataDefIsOpen )
import Kind.Newtypes
import Type.Type( typevarId, conInfoName, conInfoIsLazy, dataInfoIsLazy )
import Backend.Typed.Syntax
import Backend.Typed.Types( sumOf )
import Backend.Typed.Query( lazySize )
import Backend.Typed.Elab.TypeInfo

refBody :: Newtypes -> DataInfo -> Tr (Maybe AType)
refBody nt info
  | dataDefIsOpen (dataInfoDef info) || null (dataInfoConstrs info) = Right Nothing
  | otherwise = Just . sumOf <$> mapM (conShape nt (paramArgs info)) (dataInfoConstrs info)

paramArgs :: DataInfo -> [AType]
paramArgs info = map (AVar . typevarId) (filter tvarStar (dataInfoParams info))

-- the definitions, and the errors in those of lazy types
typeDefs :: Newtypes -> (TypeDefs,[String])
typeDefs nt
  = (M.fromList [(dataInfoName info, d) | (info,Right d) <- defs],
     [show (dataInfoName info) ++ ": " ++ err | (info,Left err) <- defs, dataInfoIsLazy info])
  where
    defs = [(info, typeDef nt info) | (_,info) <- NM.toList (newtypesTypeDefs nt), not (isValueInfo info)]

typeDef :: Newtypes -> DataInfo -> Tr TypeDef
typeDef nt info
  = do body <- refBody nt info
       lz <- lazyDef nt info
       return (TypeDef (dataInfoName info) (map typevarId (filter tvarStar (dataInfoParams info))) body lz)

-- A lazy type `T⟨ā⟩ := A ~> B` has the indirection among its lazy constructors. Its strict
-- tags come before its lazy ones (`datatype-ptr-is-whnf` relies on it), and every lazy
-- alternative is a box with a block, which evaluation locks.
lazyDef :: Newtypes -> DataInfo -> Tr (Maybe Lazy)
lazyDef nt info
  = case [tag | (tag,con) <- cons, isLazyIndirectConName (conInfoName con)] of
      [] -> Right Nothing
      (ind:_)
        -> do let lazies = [tag | (tag,con) <- cons, conInfoIsLazy con]
              unless (and [tag < l | (tag,con) <- cons, not (conInfoIsLazy con), l <- lazies])
                (Left "the strict constructors of a lazy type must come before its lazy ones")
              forM_ [con | (_,con) <- cons, conInfoIsLazy con] $ \con ->
                do shape <- conShape nt (paramArgs info) con
                   case shape of
                     ABox s | Right _ <- lazySize s -> return ()
                     _ -> Left ("the lazy constructor " ++ show (conInfoName con) ++ " has no fields")
              return (Just (Lazy lazies ind))
  where
    cons = zip [1..] (dataInfoConstrs info)   -- tags start at 1
