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
import Common.Name( Name, isLazyIndirectConName )
import Common.Syntax( dataDefIsOpen )
import Kind.Newtypes
import Type.Type( typevarId, conInfoName, conInfoIsLazy, dataInfoIsLazy )
import Backend.Typed.Syntax
import Backend.Typed.Types( sumOf, applyA )
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
  = (M.fromList [(tdefName d, d) | (_,Right d) <- defs],
     [show (dataInfoName info) ++ ": " ++ err | (info,Left err) <- defs, dataInfoIsLazy info])
  where
    defs = [(info, typeDef nt info) | (_,info) <- NM.toList (newtypesTypeDefs nt), not (isValueInfo info)]

typeDef :: Newtypes -> DataInfo -> Tr TypeDef
typeDef nt info
  = do body <- refBody nt info
       lz <- lazyDef nt info
       let params = map typevarId (filter tvarStar (dataInfoParams info))
       return (TypeDef (dataInfoName info) params (recType (dataInfoName info) params lz <$> body))

-- The body `(μt⟨ā⟩. A[t/T])⟨ā⟩` of a datatype `T⟨ā⟩` whose constructors are `A`, or
-- `(μt⟨ā⟩. A[t/T] ~> B[t/T])⟨ā⟩` with the lazy tags of A. Koka's type variables are positive,
-- so the binder `t` is a negative one.
recType :: Name -> [TVar] -> [Int] -> AType -> AType
recType name params lz body = AMu lz t params (foldA body) (map AVar params)
  where
    t = -2
    foldA a = case a of
      ACon n ts | n == name -> applyA (AVar t) (map foldA ts)
      ACon n ts     -> ACon n (map foldA ts)
      ABox v        -> ABox (foldV v)
      ASum ts       -> ASum [(i,foldA b) | (i,b) <- ts]
      AFun ps r     -> AFun [(m,foldV p) | (m,p) <- ps] (foldV r)
      AForall vs b  -> AForall vs (foldA b)
      AApp v ts     -> AApp v (map foldA ts)
      ALam vs b     -> ALam vs (foldA b)
      AMu l x vs b ts -> AMu l x vs (foldA b) (map foldA ts)
      AWhnf b       -> AWhnf (foldA b)
      AScalar _     -> a
      AUnit         -> a
      AVar _        -> a
    foldV v = case v of
      VPtr a        -> VPtr (foldA a)
      VSum ts       -> VSum (map foldV ts)
      VProd a b     -> VProd (foldV a) (foldV b)
      VExists vs b  -> VExists vs (foldV b)
      VCtx f a b    -> VCtx f (foldA a) (foldA b)
      VCell n a     -> VCell n (foldA a)
      VReuse _ _ _  -> v
      VUnit         -> v
      VRaw _        -> v

-- The lazy tags of a type (none for a strict one). A lazy type `μt⟨ā⟩. A ~> B` has the
-- indirection among its lazy constructors. Its strict tags come before its lazy ones
-- (`[if-whnf]` relies on it), and every lazy alternative is a box with a block, which
-- evaluation locks.
lazyDef :: Newtypes -> DataInfo -> Tr [Int]
lazyDef nt info
  = case [tag | (tag,con) <- cons, isLazyIndirectConName (conInfoName con)] of
      [] -> Right []
      _
        -> do let lazies = [tag | (tag,con) <- cons, conInfoIsLazy con]
              unless (and [tag < l | (tag,con) <- cons, not (conInfoIsLazy con), l <- lazies])
                (Left "the strict constructors of a lazy type must come before its lazy ones")
              forM_ [con | (_,con) <- cons, conInfoIsLazy con] $ \con ->
                do shape <- conShape nt (paramArgs info) con
                   case shape of
                     ABox s | Right _ <- lazySize s -> return ()
                     _ -> Left ("the lazy constructor " ++ show (conInfoName con) ++ " has no fields")
              return lazies
  where
    cons = zip [1..] (dataInfoConstrs info)   -- tags start at 1
