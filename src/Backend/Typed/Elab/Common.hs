-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-- Structural queries shared by the Core-to-typed-IR passes.
module Backend.Typed.Elab.Common( isValue, isConExpr, linearContexts, isLinearContextPrim ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List( isInfixOf )
import Common.Name
import Common.NamePrim( nameCCtxApply, nameCCtxExtend )
import Core.Core( Expr(..), TName(..), VarInfo(..), Branch(..), Guard(..), Def(..), DefGroup(..), flattenDefGroups )
import Backend.Typed.Names( isJoinName )

isValue :: Expr -> Bool
isValue expr
  = case expr of
      Var _ _       -> True
      Lit _         -> True
      Con _ _       -> True
      Lam _ _ _     -> True
      TypeLam _ e   -> isValue e
      TypeApp e _   -> isValue e
      App f args    -> isConExpr f && all isValue args
      _             -> False

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
