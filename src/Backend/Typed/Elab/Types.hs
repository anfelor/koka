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
import Control.Monad( forM_, unless, when )
import Data.List( partition )
import Common.Syntax( dataDefIsOpen )
import Kind.Newtypes
import Type.Type( ConInfo, typevarId, conInfoName, conInfoParams, conInfoIsLazy, dataInfoIsLazy )
import Backend.Typed.Syntax
import Backend.Typed.Env( reuseSize )
import Backend.Typed.Elab.TypeInfo

-- The body of a datatype. Only that of a reference datatype is part of the typing rules; the
-- others are metadata for C generation (see `TypeDef`).
typeBody :: Newtypes -> DataInfo -> Tr TypeBody
typeBody nt info
  | isValueInfo info = BodyValue <$> valueBody nt info (paramArgs info)
  | dataDefIsOpen (dataInfoDef info) = Right BodyOpen
  | null (dataInfoConstrs info) = Right BodyAbstract
  | otherwise = BodyRef . refShape info <$> mapM (conShape nt (paramArgs info)) (dataInfoConstrs info)

paramArgs :: DataInfo -> [AType]
paramArgs info = map (AVar . typevarId) (filter tvarStar (dataInfoParams info))

-- the definitions, and the errors in those of lazy types
typeDefs :: Newtypes -> (TypeDefs,[String])
typeDefs nt
  = (M.fromList [(tdefName d, d) | (_,Right d) <- defs],
     [show (dataInfoName info) ++ ": " ++ err | (info,Left err) <- defs, dataInfoIsLazy info])
  where
    defs = [(info, typeDef nt info) | (_,info) <- NM.toList (newtypesTypeDefs nt)]

typeDef :: Newtypes -> DataInfo -> Tr TypeDef
typeDef nt info
  = do body <- typeBody nt info
       when (isLazyInfo info) (lazyDef nt info)
       let params = map typevarId (filter tvarStar (dataInfoParams info))
       -- the constructors of an open datatype are signatures
       labels <- case body of
                   BodyOpen -> return []
                   _ -> mapM (conLabel nt (paramArgs info)) (dataInfoConstrs info)
       return (TypeDef (dataInfoName info) params body labels)

conLabel :: Newtypes -> [AType] -> ConInfo -> Tr ConLabel
conLabel nt vargs con
  = do fields <- if null (conInfoParams con) then return [] else conFieldTypes nt vargs con
       let decls = map (valueDecl nt . snd) (conInfoParams con) ++ repeat Nothing   -- no padding is declared
       return (ConLabel (conInfoName con) (take (length fields) (conFieldNames con)) (take (length fields) decls))

-- A lazy type `L ~> S` has strict constructors, which come before its lazy ones (the thunks,
-- among them the indirection), and every thunk is a box with a block, which evaluation locks.
lazyDef :: Newtypes -> DataInfo -> Tr ()
lazyDef nt info
  = do let (lazies,stricts) = partition (conInfoIsLazy . snd) cons
       when (null stricts) (Left "a lazy type without strict constructors")
       unless (maximum (map fst stricts) < minimum (map fst lazies))
         (Left "the strict constructors of a lazy type must come before its lazy ones")
       forM_ (map snd lazies) $ \con ->
         do shape <- conShape nt (paramArgs info) con
            case shape of
              ABox s | Right _ <- reuseSize s -> return ()
              _ -> Left ("the lazy constructor " ++ show (conInfoName con) ++ " has no fields")
  where
    cons = zip [1 :: Int ..] (dataInfoConstrs info)   -- tags start at 1
