-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Construction and rewriting helpers used only by typed IR passes.
module Backend.Typed.Passes.Common where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Data.Maybe( fromMaybe )
import Control.Monad( foldM )
import Backend.Typed.Syntax
import Backend.Typed.Types( Sub, Types(..), inst )
import Backend.Typed.Traversal
import Backend.Typed.Common
import Common.Name( Name )

-- Discard an owned value by destructuring it down to boxed operands and credits.
-- Parts use their canonical paths, reusing those already in scope. Sequencing
-- a sum or existential drop needs a fresh root from the caller. Parts of a trivial
-- type (`Query.trivialTy`) are not discarded.
dropValue :: Monad m => (Ty -> Bool) -> m Path -> Scope -> Path -> Ty -> VExpr -> m VExpr
dropValue trivial _ _ _ t e
  | trivial t = return e
dropValue trivial fresh scope x t e
  = case t of
      A _ -> return (Drop x e)
      V v -> case v of
        VPtr a -> do let y = child x SDeref
                     return (reuseParts scope (Deref Owned (Var x) y (Drop y e)))
        VProd{} -> do let fields = [f | f@(_,_,s) <- fieldsAt x v, not (trivial (V s))]
                          parts = M.union (scopeOf [y | (y,_,_) <- fields]) scope
                      body <- foldM (\rest (y,_,s) -> dropValue trivial fresh parts y (V s) rest) e (reverse fields)
                      return (projectAll scope Owned x fields body)
        VSum ts -> do u <- fresh
                      alts <- mapM dropAlt (zip [0..] ts)
                      -- A continuation can bind roots. Keep it outside the case,
                      -- rather than copying its binders into every alternative.
                      return (Let u VUnit (reuseParts scope (CaseV Owned (Var x) alts)) e)
          where
            dropAlt (i,(c,s)) = do let y = child x (SInjV i c)
                                   body <- dropValue trivial fresh (M.insert y Nothing scope) y (V s) (Ret UnitV)
                                   return (i,y,body)
        VExists tvs s
          -> do let y = child x SPack
                u <- fresh
                -- Keep the continuation outside the existential's scope.
                -- Fresh types only need to avoid the payload's free variables.
                let start = minimum (0 : tvs ++ ftv s) - 1
                    bs = take (length tvs) [start,start-1 ..]
                    s' = inst tvs (map AVar bs) s
                body <- dropValue trivial fresh (M.insert y Nothing scope) y (V s') (Ret UnitV)
                return (Let u VUnit (reuseParts scope (Unpack Owned (Var x) bs y body)) e)
        VReuse _ _ _ -> return (Free x e)
        VCtx _ _ _ -> return (Drop x e)
        -- a cell is linear and never dropped, which `Check` rejects
        VCell _ _ -> return (Drop x e)
        VUnit -> return e
        VRaw _ -> return e

-- the type at steps into a product
partAt :: VType -> [Step] -> Maybe VType
partAt t [] = Just t
partAt (VProd fs) (SField i _ : ss) | i < length fs = partAt (snd (fs !! i)) ss
partAt _ _ = Nothing

-- project fields of a product variable around an expression, reusing those in scope
projectAll :: Scope -> Mode -> Path -> [(Path,Int,VType)] -> VExpr -> VExpr
projectAll scope m x fields body = foldr (\(y,i,_) e -> reuseParts scope (Proj m (Var x) i y e)) body fields

-- the projection at a step into a product
projAt :: Step -> Mode -> VVal -> Path -> VExpr -> VExpr
projAt s m v = case s of
                 SField i _ -> Proj m v i
                 _ -> error ("Backend.Typed.Common.projAt: not a step into a product: " ++ show s)

-- the pointer that the binder of a `[deref]` is the dereference of
derefOf :: Path -> Maybe Path
derefOf (Path x ss)
  = case reverse ss of
      SDeref : rest -> Just (Path x (reverse rest))
      _ -> Nothing

-- A `[let-yield]` as the `let` that is taken if no effect yields, and its yielding branch,
-- which is cold.
yieldingAlts :: VExpr -> Maybe (VExpr,VExpr)
yieldingAlts expr
  = case expr of
      LetYield x t e1 e2 e3 -> Just (Let x t e1 e2,e3)
      _ -> Nothing

renamePrefix :: Path -> Path -> Path -> Path
renamePrefix p q x
  | x `within` p = foldl child q (stepsFrom p x)
  | otherwise = x

-- replace each jump to a join point
substJump :: Name -> ([AType] -> [VVal] -> VExpr) -> VExpr -> VExpr
substJump j f expr
  = case expr of
      Jump k ts vs | k == j -> f ts vs
      Join k tvs ps e1 e2 | k == j -> Join k tvs ps (substJump j f e1) e2
      _ -> runIdentity (descendE Identity Identity (\_ e -> Identity (substJump j f e)) expr)

-- substitute types for type variables, which the expression does not bind again
substTypesE :: Sub -> VExpr -> VExpr
substTypesE sub expr
  = runIdentity (descendE Identity (Identity . substTypesV sub) (\_ e -> Identity (substTypesE sub e)) annotated)
  where
    annotated = case expr of
      Let x t e1 e2         -> Let x (subst sub t) e1 e2
      LetYield x t e1 e2 e3 -> LetYield x (subst sub t) e1 e2 e3
      Yielded t             -> Yielded (subst sub t)
      Unreachable t         -> Unreachable (subst sub t)
      Call f ts vs          -> Call f (map (subst sub) ts) vs
      Join j tvs ps e1 e2   -> Join j tvs [(x,m,subst sub t) | (x,m,t) <- ps] e1 e2
      Jump j ts vs          -> Jump j (map (subst sub) ts) vs
      _                     -> expr

substTypesV :: Sub -> VVal -> VVal
substTypesV sub val
  = mapV (substTypesA sub) (substTypesV sub) annotated
  where
    annotated = case val of
      Glob x ts   -> Glob x (map (subst sub) ts)
      Inj i t v   -> Inj i (subst sub t) v
      Ptr a v     -> Ptr (subst sub a) v
      Pack t ts v -> Pack (subst sub t) (map (subst sub) ts) v
      TyApp v ts  -> TyApp v (map (subst sub) ts)
      Context b v -> Context (subst sub b) v
      NoReuse n c -> NoReuse n ((\(Contents k p t) -> Contents k (substTypesV sub p) (subst sub t)) <$> c)
      _           -> val

substTypesA :: Sub -> AVal -> AVal
substTypesA sub val
  = case val of
      Lam ps r e      -> Lam [(x,m,subst sub t) | (x,m,t) <- ps] (subst sub r) (substTypesE sub e)
      InjA i a v      -> InjA i (subst sub a) (substTypesA sub v)
      Roll a v        -> Roll (subst sub a) (substTypesA sub v)
      InjLazy d a v   -> InjLazy d (subst sub a) (substTypesA sub v)
      OpenCon c ts vs -> OpenCon c (map (subst sub) ts) (map (substTypesV sub) vs)
      _               -> mapA id (substTypesA sub) (substTypesV sub) val

-- substitution of unboxed values (their free variables must not be bound in the scope).
-- A substitution at a named operand must itself be a variable; use a let for other values.
replaceA :: M.Map Path VVal -> AVal -> AVal
replaceA = substA . valueAt

replaceV :: M.Map Path VVal -> VVal -> VVal
replaceV = substV . valueAt

replaceVType :: M.Map Path VVal -> VType -> VType
replaceVType = substVType . valueAt

replaceContents :: M.Map Path VVal -> Contents -> Contents
replaceContents = substContents . valueAt

replaceAType :: M.Map Path VVal -> AType -> AType
replaceAType = substAType . valueAt

defScope :: Def -> Scope
defScope d = case d of
  DefFun{ defArgs = ps } -> scopeOf [x | (x,_,_) <- ps]
  DefVal{} -> M.empty

-- Reuse parts while constructing a destructuring form.
reuseParts :: Scope -> VExpr -> VExpr
reuseParts scope expr = case knownAlt scope expr of
  Just i -> snd (getConst (descendB (const (Const [])) (const (Const [])) (\bs e -> Const [(bs,e)]) expr) !! i)
  Nothing -> expr

-- Retarget a newly constructed destructuring and its continuation. Existing root
-- binders (including those of non-variable scrutinees) keep their identity.
nameParts :: VExpr -> VExpr
nameParts expr = runIdentity (descendB Identity Identity branch expr)
  where
    branch bs e = let xs = [fromMaybe x (pathOf (scrutVar expr) step) | (x,step) <- bs]
                      ren = M.fromList [(x,y) | ((x,_),y) <- zip bs xs, x /= y]
                  in Identity (xs,renameE ren e)

-- Copy an expression without duplicating its root binders. Free variables keep
-- their identities; descriptions of bound variables are renamed even out of scope.
cloneE :: Monad m => m Path -> VExpr -> m VExpr
cloneE fresh expr = do
  let xs = S.toList (S.fromList [x | x@(Path _ []) <- bindersE expr])
  ys <- mapM (const fresh) xs
  let ren = M.fromList (zip xs ys)
      renameRoot x = M.findWithDefault x x ren
      sub = valueAt (M.map Var ren)
      go = substStepWith renameRoot go
  return (if null xs then expr else go (scopeFor sub (fvE expr)) sub expr)

-- renaming includes boxed operands as well as unboxed variables
renameA :: M.Map Path Path -> AVal -> AVal
renameA = replaceA . M.map Var

renameV :: M.Map Path Path -> VVal -> VVal
renameV = replaceV . M.map Var

-- rename a variable and its parts, also where they are bound
renamePath :: Path -> Path -> VExpr -> VExpr
renamePath x y = renameE (M.singleton x y)
