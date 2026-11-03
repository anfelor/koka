-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Koka's conventions for lazy types: the functions that evaluate them (for `Passes.Lazy`),
-- and its tests of WHNF.
module Backend.Typed.Elab.Lazy( lazyFuns, whnfTests ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List( sortOn )
import qualified Common.NameMap as NM
import Common.Name
import Common.NamePrim( nameLazyIsWhnf, nameLazyPtrIsWhnf )
import Kind.Newtypes
import Type.Type( lazyName, conInfoName )
import Backend.Typed.Syntax
import Backend.Typed.Common( Lazies(..) )
import Backend.Typed.Query( Env(..), reuseSize, lazySides )
import Backend.Typed.Traversal( descendAll, fvE )
import Backend.Typed.Elab.TypeInfo( conFieldTypes )
import Backend.Typed.Elab.Monad( E, fresh )

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

-- Tests of WHNF (`[if-whnf]`). Koka tests a lazy value `x` with `datatype-(ptr-)is-whnf(x, tag)`,
-- after the lets of its tag argument, and a case on the result, with the join points of its
-- match in between. The test becomes `[if-whnf]` on `x`. `Paths` resolves a test or a match
-- of `x` inside another test of `x`, as its binders are then in scope.
whnfTests :: VExpr -> E VExpr
whnfTests expr
  = case expr of
      Let b _ e body
        | Just (x,pre) <- whnfTest e
        , Just (joins,b',alts) <- joinsTo body, b == b'
        , [e0,e1] <- [e' | (_,_,e') <- sortOn (\(i,_,_) -> i) alts]
        -> do d <- fresh "d"
              r <- fresh "r"
              s <- fresh "whnf"
              l <- fresh "delay"
              test <- (\e1' e0' -> Deref Owned (Var x) d (Unroll Owned d r (IfWhnf Owned r (s,e1') (l,e0'))))
                        <$> whnfTests e1 <*> whnfTests e0
              joins' <- mapM (\(j,tvs,ps,e2) -> Join NonRec j tvs ps <$> whnfTests e2) joins
              let expr' = pre (foldr ($) test joins')
              if S.member b (fvE expr') then descend else return expr'
      _ -> descend
  where
    descend = descendAll (\_ -> whnfTests) expr
    -- the test of `x`, after the lets of its tag argument
    whnfTest e
      = case e of
          Call f [_] [Var x, _] | f == nameLazyIsWhnf || f == nameLazyPtrIsWhnf -> Just (x,id)
          Let y t e1 e2 -> (\(x,pre) -> (x,Let y t e1 . pre)) <$> whnfTest e2
          _ -> Nothing
    -- the join points before the case on the result of the test
    joinsTo e
      = case e of
          Join NonRec j tvs ps e1 e2 -> (\(js,y,alts) -> ((j,tvs,ps,e1) : js,y,alts)) <$> joinsTo e2
          CaseV _ (Var y) alts -> Just ([],y,alts)
          _ -> Nothing
