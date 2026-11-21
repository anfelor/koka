-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Internal names and structural queries shared by the Core-to-typed-IR passes.
module Backend.Typed.Elab.Common( isValue, isConExpr, identityCast, isPrim, linearContexts, isLinearContextPrim, nameUnreachable, nameYieldingNonFinal, isJoinName ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List( isInfixOf )
import Common.Name
import Common.NamePrim( nameCCtxApply, nameCCtxExtend, nameEffectOpen, nameCoreHnd )
import Core.Core( Expr(..), TName(..), VarInfo(..), Branch(..), Guard(..), Def(..), DefGroup(..), flattenDefGroups )

-- marks an impossible alternative in Core; elaboration turns it into `[unreachable]`
nameUnreachable :: Name
nameUnreachable = newHiddenName "typed-unreachable"

-- `std/core/hnd/yielding-non-final`, which tests the yield flag like `yielding`
nameYieldingNonFinal :: Name
nameYieldingNonFinal = qualify nameCoreHnd (newName "yielding-non-final")

isJoinName :: Name -> Bool
isJoinName x = hiddenNameStartsWith x "join"

isValue :: Expr -> Bool
isValue expr
  = case expr of
      Var _ _       -> True
      Lit _         -> True
      Con _ _       -> True
      Lam _ _ _     -> True
      TypeLam _ e   -> isValue e
      TypeApp e _   -> isValue e
      App f args | Just arg <- identityCast expr -> isValue arg
                 | otherwise -> isConExpr f && all isValue args
      _             -> False

-- The argument of `.open` or an identity external (`isIdentityFun`, also
-- `.open(cast-ev1)`), which changes at most the effects in the type of its argument.
-- `Core.Simplify` erases these applications for the other backends.
identityCast :: Expr -> Maybe Expr
identityCast expr
  = case expr of
      App f [arg] | isIdentityFun f -> Just arg
      _ -> Nothing

-- `.open` or an identity external (`inline "#1"`, such as `unsafe-total-cast` or
-- `pretend-decreasing`), or one applied to another (`.open(cast-ev1)`): applied to one
-- argument, it changes at most the effects in its type.
isIdentityFun :: Expr -> Bool
isIdentityFun f
  = case f of
      TypeApp (Var _ (InfoExternal "#1")) _ -> True
      TypeApp (Var g _) _ -> getName g == nameEffectOpen
      App g [h] -> isIdentityFun g && isIdentityFun h
      _ -> False

-- a primitive, possibly under an identity external (such as `.open(yielding)`)
isPrim :: Name -> Expr -> Bool
isPrim name f
  = case f of
      Var (TName g _) _ -> g == name
      TypeApp g _ -> isPrim name g
      _ | Just g <- identityCast f -> isPrim name g
      _ -> False

isConExpr :: Expr -> Bool
isConExpr (Con _ _)     = True
isConExpr (TypeApp e _) = isConExpr e
isConExpr _             = False

-- `Core.CTail` plugs and extends a context in place (`kk_cctx_apply_linear` and
-- `kk_cctx_extend_linear`) where it knows the context to be unique
isLinearContextPrim :: Expr -> Bool
isLinearContextPrim f
  = case f of
      TypeApp g _ -> isLinearContextPrim g
      Var (TName g _) (InfoExternal fmt) -> g `elem` [nameCCtxApply, nameCCtxExtend] && "_linear(" `isInfixOf` fmt
      _ | Just g <- identityCast f -> isLinearContextPrim g
      _ -> False

-- The variables whose contexts are plugged or extended in place, directly or by a join point
-- that they are passed to (pattern matching passes the free variables of a shared branch).
linearContexts :: Expr -> S.Set Name
linearContexts = linearIn M.empty

-- `js`: the positions of the parameters of each join point in scope that are linear
linearIn :: M.Map Name [Int] -> Expr -> S.Set Name
linearIn js expr
  = case expr of
      App f (Var x _ : args) | isLinearContextPrim f -> S.insert (getName x) (S.unions (map go args))
      App (Var j _) args | Just is <- M.lookup (getName j) js
                    -> S.unions (S.fromList [getName x | (i,Var x _) <- zip [0..] args, i `elem` is] : map go args)
      App f args    -> S.unions (map go (f:args))
      Lam _ _ e     -> go e
      TypeLam _ e   -> go e
      TypeApp e _   -> go e
      Let [] e      -> go e
      Let (DefNonRec (Def{ defName = j, defExpr = Lam pars _ body }) : dgs) e | isJoinName j
                    -> let linear = linearIn js body
                           is = [i | (i,p) <- zip [0..] pars, S.member (getName p) linear]
                       in (linear `S.difference` S.fromList (map getName pars))
                          `S.union` linearIn (M.insert j is js) (Let dgs e)
      Let (dg:dgs) e -> S.unions (go (Let dgs e) : map (go . defExpr) (flattenDefGroups [dg]))
      Case es brs   -> S.unions (map go es ++ [go x | Branch _ gs <- brs, Guard t b <- gs, x <- [t,b]])
      _             -> S.empty
  where
    go = linearIn js
