-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Prepare Core-specific metadata for lazy lowering in the typed IR.
module Backend.Typed.Elab.Lazy( lazyFuns ) where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Common.NameMap as NM
import Common.Name
import Kind.Newtypes
import Type.Type( lazyName, conInfoName )
import Backend.Typed.Syntax
import Backend.Typed.Common( Lazies(..) )
import Backend.Typed.Query( Env(..), reuseSize, lazySides )
import Backend.Typed.Elab.TypeInfo( conFieldTypes )

lazyFuns :: Newtypes -> TypeDefs -> Lazies
lazyFuns nt tdefs
  = Lazies (M.fromList [(funName info (show (unqualify (conInfoName con))), (tag,n,fs))
                       | (info,tvs,thunks) <- infos, (tag,con) <- cons info
                       , not (isLazyIndirectConName (conInfoName con))
                       , Just (ABox s) <- [lookup tag thunks], Right n <- [reuseSize s]
                       , Right fs <- [conFieldTypes nt (map AVar tvs) con]])
           (S.fromList [funName info "eval-locked" | (info,_,_) <- infos])
           (M.fromList [(dataInfoName info, tag) | (info,_,_) <- infos, (tag,con) <- cons info, isLazyIndirectConName (conInfoName con)])
  where
    env = Env tdefs M.empty
    cons info = zip [1..] (dataInfoConstrs info)   -- tags start at 1
    infos = [(info,tvs,thunks) | (_,info) <- NM.toList (newtypesTypeDefs nt)
                               , Just TypeDef{ tdefParams = tvs } <- [M.lookup (dataInfoName info) tdefs]
                               , Right (thunks,_) <- [lazySides env (ACon (dataInfoName info) (map AVar tvs))]]
    funName info stem = qualify (qualifier (dataInfoName info)) (lazyName info stem)
