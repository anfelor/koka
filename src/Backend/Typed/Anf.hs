-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

module Backend.Typed.Anf( anfCore, isValue ) where

import Common.Unique
import Core.Core

anfCore :: Core -> Unique Core
anfCore core
  = do defs <- mapM anfDefGroup (coreProgDefs core)
       return core{ coreProgDefs = defs }

anfDefGroup :: DefGroup -> Unique DefGroup
anfDefGroup (DefRec defs)   = DefRec <$> mapM anfDef defs
anfDefGroup (DefNonRec def) = DefNonRec <$> anfDef def

anfDef :: Def -> Unique Def
anfDef def
  = do e <- anfExpr (defExpr def)
       return def{ defExpr = e }

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

anfExpr :: Expr -> Unique Expr
anfExpr expr
  = case expr of
      TypeLam tvs e   -> TypeLam tvs <$> anfExpr e
      Let dgs body    -> Let <$> mapM anfDefGroup dgs <*> anfExpr body
      Case scruts brs -> do (bs,scruts') <- atoms scruts
                            brs' <- mapM anfBranch brs
                            return (makeLet bs (Case scruts' brs'))
      App f args      -> do (bs1,f') <- atom f
                            (bs2,args') <- atoms args
                            return (makeLet (bs1 ++ bs2) (App f' args'))
      _               -> uncurry makeLet <$> atom expr

anfBranch :: Branch -> Unique Branch
anfBranch (Branch pats guards)
  = Branch pats <$> mapM (\(Guard t e) -> Guard <$> anfExpr t <*> anfExpr e) guards

atoms :: [Expr] -> Unique ([DefGroup],[Expr])
atoms es = do rs <- mapM atom es
              return (concatMap fst rs, map snd rs)

atom :: Expr -> Unique ([DefGroup],Expr)
atom expr
  = case expr of
      Lam pars eff body -> do body' <- anfExpr body
                              return ([],Lam pars eff body')
      TypeLam tvs e | isValue e -> fmap (TypeLam tvs) <$> atom e
      TypeApp e tps     -> fmap (\e' -> TypeApp e' tps) <$> atom e
      App f args | isConExpr f -> do (bs,args') <- atoms args
                                     return (bs,App f args')
      _ | isValue expr  -> return ([],expr)
      _                 -> do e <- anfExpr expr
                              x <- uniqueName "a"
                              return ([DefNonRec (makeDef x e)], Var (TName x (typeOf expr)) InfoNone)
