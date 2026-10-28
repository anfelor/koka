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
import Common.Name( isLazyIndirectConName, makeHiddenName )
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
  = (M.fromList [(tdefName d, d) | (_,Right ds) <- defs, d <- ds],
     [show (dataInfoName info) ++ ": " ++ err | (info,Left err) <- defs, dataInfoIsLazy info])
  where
    defs = [(info, typeDef nt info) | (_,info) <- NM.toList (newtypesTypeDefs nt), not (isValueInfo info)]

-- the definition of a type, and that of `whnf(T)` for a lazy type T
typeDef :: Newtypes -> DataInfo -> Tr [TypeDef]
typeDef nt info
  = do body <- refBody nt info
       lz <- lazyDef nt info
       let name = dataInfoName info
           params = map typevarId (filter tvarStar (dataInfoParams info))
           whnf = case (lz,body) of
                    (Just Lazy{ lazyAlts = lazies, lazyWhnf = Just w }, Just (ASum alts))
                      -> [TypeDef w params (Just (ASum [alt | alt@(tag,_) <- alts, tag `notElem` lazies])) Nothing (Just name)]
                    _ -> []
       return (TypeDef name params body lz Nothing : whnf)

-- A lazy type `T⟨ā⟩ := A ~> B` has the indirection among its lazy constructors. Its strict
-- tags come before its lazy ones (`[if-whnf]` relies on it), and every lazy
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
              let whnf = if length lazies < length cons then Just (makeHiddenName "whnf" (dataInfoName info)) else Nothing
              return (Just (Lazy lazies ind whnf))
  where
    cons = zip [1..] (dataInfoConstrs info)   -- tags start at 1
