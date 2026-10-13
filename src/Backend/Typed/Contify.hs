-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Contification: a local function that is only called in tail position of the
  expression that follows its definition becomes a join point (a `@join` local
  function, see `Match`). Join points are closed: its free variables become extra
  parameters, passed at every call. Runs before `Match`, which closes the guards
  over these extra arguments.
-}
module Backend.Typed.Contify( contifyCore ) where

import qualified Data.Set as S
import Common.Name
import Common.NamePrim( nameOpenNone )
import Common.Unique
import Type.Type
import Core.Core
import Core.CoreVar( freeLocals, (|~>) )

contifyCore :: Core -> Unique Core
contifyCore core
  = do defs <- mapM contifyDefGroup (coreProgDefs core)
       return core{ coreProgDefs = defs }

contifyDefGroup :: DefGroup -> Unique DefGroup
contifyDefGroup (DefRec defs)   = DefRec <$> mapM contifyDef defs
contifyDefGroup (DefNonRec def) = DefNonRec <$> contifyDef def

contifyDef :: Def -> Unique Def
contifyDef def
  = do e <- contifyExpr (defExpr def)
       return def{ defExpr = e }

contifyExpr :: Expr -> Unique Expr
contifyExpr expr
  = case expr of
      Let (DefNonRec def@Def{ defExpr = Lam ps _ body } : dgs) e
        | let f    = defTName def
              rest = makeLet dgs e
              fvs  = tnamesList (freeLocals (defExpr def))
        , tailOnly f rest
        , S.null (S.fromList (map getName (f:fvs)) `S.intersection` binders rest)
        -> do body' <- contifyExpr body
              rest' <- contifyExpr rest
              j  <- uniqueName "join"
              qs <- mapM (\x -> TName <$> uniqueName "c" <*> pure (typeOf x)) fvs
              let lam = Lam (ps ++ qs) typeTotal ([(x,Var q InfoNone) | (x,q) <- zip fvs qs] |~> body')
                  jmp args = App (Var (TName j (typeOf lam)) InfoNone) (args ++ [Var x InfoNone | x <- fvs])
              return (Let [DefNonRec (makeDef j lam)] (rewriteBottomUp (redirect f jmp) rest'))
      Lam pars eff body -> Lam pars eff <$> contifyExpr body
      App f args        -> App <$> contifyExpr f <*> mapM contifyExpr args
      TypeLam tvs e     -> TypeLam tvs <$> contifyExpr e
      TypeApp e tps     -> (\e' -> TypeApp e' tps) <$> contifyExpr e
      Let dgs body      -> Let <$> mapM contifyDefGroup dgs <*> contifyExpr body
      Case scruts brs   -> Case <$> mapM contifyExpr scruts <*> mapM contifyBranch brs
      _                 -> return expr

contifyBranch :: Branch -> Unique Branch
contifyBranch (Branch pats guards)
  = Branch pats <$> mapM (\(Guard t e) -> Guard <$> contifyExpr t <*> contifyExpr e) guards

-- a call `f(args)`, also as `@open-none<n>(f,args)` (an effect cast)
callOf :: TName -> Expr -> Maybe [Expr]
callOf f expr
  = case expr of
      App (Var g _) args | g == f -> Just args
      App (TypeApp (Var o _) _) (Var g _ : args) | g == f, getName o == nameOpenNone (length args) -> Just args
      App (Var o _) (Var g _ : args) | g == f, getName o == nameOpenNone (length args) -> Just args
      _ -> Nothing

redirect :: TName -> ([Expr] -> Expr) -> Expr -> Expr
redirect f jmp expr
  = case callOf f expr of
      Just args -> jmp args
      Nothing   -> expr

-- `f` is used and only called in tail position (`Match` makes guard bodies tail positions)
tailOnly :: TName -> Expr -> Bool
tailOnly f expr = occurs expr && tails expr
  where
    tails e
      = case callOf f e of
          Just args -> not (any occurs args)
          Nothing -> case e of
            Let dgs body -> not (any (occurs . defExpr) (flattenDefGroups dgs)) && tails body
            Case ss brs  -> not (any occurs ss) && and [not (occurs t) && tails b | Branch _ gs <- brs, Guard t b <- gs]
            _            -> not (occurs e)
    occurs e = f `S.member` freeLocals e

-- all names bound inside an expression
binders :: Expr -> S.Set Name
binders expr
  = case expr of
      Lam ps _ e    -> S.fromList (map getName ps) `S.union` binders e
      App f args    -> S.unions (map binders (f:args))
      TypeLam _ e   -> binders e
      TypeApp e _   -> binders e
      Let dgs e     -> S.unions (binders e : [S.insert (defName d) (binders (defExpr d)) | d <- flattenDefGroups dgs])
      Case ss brs   -> S.unions (map binders ss ++ [S.unions (patBinders ps : [binders t `S.union` binders b | Guard t b <- gs]) | Branch ps gs <- brs])
      _             -> S.empty
  where
    patBinders ps = S.fromList [getName x | p <- ps, x <- patVars p]
    patVars p = case p of
                  PatVar x q          -> x : patVars q
                  PatCon{ patConPatterns = qs } -> concatMap patVars qs
                  _                   -> []
