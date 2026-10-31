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
import Data.List( sortOn )
import Data.Maybe( listToMaybe, fromMaybe )
import Control.Monad( foldM )
import Backend.Typed.Syntax
import Backend.Typed.Types( Sub, Types(..), inst, mapReuseContents, traverseReuseContents )
import Backend.Typed.Traversal
import Backend.Typed.Common
import Common.Name( Name, newHiddenName )

-- A fresh-name supply belongs to one definition, shared by all of a pass's
-- nested scopes. Reserve description names too: they can outlive their binders.
data NameSupply = NameSupply Int (S.Set Name)

freshFor :: Def -> NameSupply
freshFor d = NameSupply 0 (S.fromList [n | Path n _ <- args ++ mentionedE body ++ types])
  where
    body = defBody d
    args = case d of DefFun{ defArgs = ps } -> [x | (x,_,_) <- ps]; DefVal{} -> []
    types = case d of
      DefFun{ defArgs = ps, defRes = r } -> concatMap (mentionedT . (\(_,_,t) -> t)) ps ++ mentionedT r
      DefVal{ defType = t } -> mentionedT t

freshNameFrom :: String -> NameSupply -> (Name,NameSupply)
freshNameFrom prefix (NameSupply i used)
  | S.member n used = freshNameFrom prefix (NameSupply (i+1) used)
  | otherwise = (n,NameSupply (i+1) (S.insert n used))
  where n = newHiddenName (prefix ++ show i)

freshPathFrom :: String -> NameSupply -> (Path,NameSupply)
freshPathFrom prefix supply = let (n,supply') = freshNameFrom prefix supply in (root n,supply')

mentionedT :: VType -> [Path]
mentionedT t = getConst (traverseReuseContents (\p -> Const (case p of Nothing -> []; Just (Contents _ v s) -> mentionedV v ++ mentionedT s)) t)

mentionedE :: VExpr -> [Path]
mentionedE e = annotations ++ getConst (descendE (Const . (:[])) (Const . mentionedV) (\xs body -> Const (xs ++ mentionedE body)) e)
  where annotations = case e of
          Let _ t _ _ -> mentionedT t
          LetYield _ t _ _ _ -> mentionedT t
          Yielded t -> mentionedT t
          Unreachable t -> mentionedT t
          Call _ ts _ -> concatMap (mentionedT . VPtr) ts
          Jump _ ts _ -> concatMap (mentionedT . VPtr) ts
          Join _ _ ps _ _ -> concatMap (mentionedT . (\(_,_,t) -> t)) ps
          _ -> []

mentionedV :: VVal -> [Path]
mentionedV v = annotations ++ getConst (descendV (Const . mentionedA) (Const . mentionedV) v)
  where annotations = case v of
          Var x -> [x]
          Glob _ ts -> concatMap (mentionedT . VPtr) ts
          Inj _ t _ -> mentionedT t
          Ptr a _ -> mentionedT (VPtr a)
          Pack t ts _ -> mentionedT t ++ concatMap (mentionedT . VPtr) ts
          TyApp _ ts -> concatMap (mentionedT . VPtr) ts
          Context a _ -> mentionedT (VPtr a)
          NoReuse _ p -> case p of Nothing -> []; Just (Contents _ w t) -> mentionedV w ++ mentionedT t
          _ -> []

mentionedA :: AVal -> [Path]
mentionedA a = case a of
  Lam ps t e -> [x | (x,_,_) <- ps] ++ concatMap (mentionedT . (\(_,_,s) -> s)) ps ++ mentionedT t ++ mentionedE e
  _ -> annotations ++ getConst (descendA (Const . (:[])) (Const . mentionedA) (Const . mentionedV) a)
  where annotations = case a of
          InjA _ t _ -> mentionedT (VPtr t)
          Roll t _ -> mentionedT (VPtr t)
          InjLazy _ t _ -> mentionedT (VPtr t)
          OpenCon _ ts _ -> concatMap (mentionedT . VPtr) ts
          _ -> []

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

-- the bodies of the alternatives of a `CaseV`, by index
altBodies :: [(Int,Path,VExpr)] -> [VExpr]
altBodies alts = [e | (_,_,e) <- sortOn (\(i,_,_) -> i) alts]

-- the part of a value at steps from it, if the value shows it
project :: VVal -> [Step] -> Maybe VVal
project v [] = Just v
project v (s:ss)
  = case (v,s) of
      (Var x, _) -> Just (Var (foldl child x (s:ss)))
      (Tuple ws, SField i _) | i < length ws -> project (ws !! i) ss
      (Inj i _ w, SInjV j _) | i == j -> project w ss
      (Pack _ _ w, SPack) -> project w ss
      _ -> Nothing

-- the known value of a variable: the part of the known value of the longest prefix of its path
valueAt :: M.Map Path VVal -> Path -> Maybe VVal
valueAt vals (Path x ss)
  = case [w | k <- [length ss, length ss - 1 .. 0], Just v <- [M.lookup (Path x (take k ss)) vals], Just w <- [project v (drop k ss)]] of
      (w:_) -> Just w
      [] -> Nothing

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

varOf :: VVal -> Path
varOf (Var y) = y
varOf v       = error ("Backend.Typed.Common.varOf: not a variable: " ++ show v)

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

replaceE :: M.Map Path VVal -> VExpr -> VExpr
replaceE sub expr
  | M.null sub = expr
  | otherwise = substE (valueAt sub) expr

-- substitution by a function from variables to their values (binders shadow it)
type Subst = Path -> Maybe VVal

-- the substitution without the binders of a scope
hide :: [Path] -> Subst -> Subst
hide xs sub x = if any (x `within`) xs then Nothing else sub x

-- Substitution's expression callback allows a pass to fuse its own rewrites
-- with the traversal, rather than traversing a continuation again per alias.
type SubstExpr = Scope -> Subst -> VExpr -> VExpr

substA :: Subst -> AVal -> AVal
substA sub val = substAWith id substEIn (scopeFor sub (fvA val)) sub val

substAWith :: (Path -> Path) -> SubstExpr -> Scope -> Subst -> AVal -> AVal
substAWith renameRoot recur scope sub val
  = case val of
      Lam ps r e -> let xs = [x | (x,_,_) <- ps]
                        ys = map renameRoot xs
                        sub' = bindSub (zip xs ys) sub
                    in Lam [(y,m,substVType sub' t) | (y,(_,m,t)) <- zip ys ps]
                         (substVType sub' r) (recur (M.union (scopeOf ys) scope) sub' e)
      InjA i a v -> InjA i (substAType sub a) (goA v)
      Roll a v -> Roll (substAType sub a) (goA v)
      InjLazy d a v -> InjLazy d (substAType sub a) (goA v)
      OpenCon c ts vs -> OpenCon c (map (substAType sub) ts) (map goV vs)
      _ -> mapA (substName sub) goA goV val
  where
    goA = substAWith renameRoot recur scope sub
    goV = substVWith renameRoot recur scope sub

substV :: Subst -> VVal -> VVal
substV sub val = substVWith id substEIn (scopeFor sub (fvV val)) sub val

substVWith :: (Path -> Path) -> SubstExpr -> Scope -> Subst -> VVal -> VVal
substVWith renameRoot recur scope sub val
  = case val of
      Var x -> maybe val id (sub x)
      Glob x ts -> Glob x (map (substAType sub) ts)
      Inj i t v -> Inj i (substVType sub t) (goV v)
      Ptr a v -> Ptr (substAType sub a) (goA v)
      Pack t ts v -> Pack (substVType sub t) (map (substAType sub) ts) (goV v)
      TyApp v ts -> TyApp (goV v) (map (substAType sub) ts)
      Context b v -> Context (substAType sub b) (goV v)
      NoReuse n p -> NoReuse n (fmap (substContents sub) p)
      _ -> mapV goA goV val
  where
    goA = substAWith renameRoot recur scope sub
    goV = substVWith renameRoot recur scope sub

substVType :: Subst -> VType -> VType
substVType sub = mapReuseContents (fmap (substContents sub))

substContents :: Subst -> Contents -> Contents
substContents sub (Contents k p t) = Contents k (substV sub p) (substVType sub t)

substAType :: Subst -> AType -> AType
substAType sub a = case substVType sub (VPtr a) of
                     VPtr b -> b
                     _ -> a

substName :: Subst -> Path -> Path
substName sub x = maybe x varOf (sub x)

-- The parts in scope, and (for a residual boxed sum) its excluded tags.
-- Keep this information lexical: the same path can be bound in separate branches.
type Scope = M.Map Path (Maybe [Int])

scopeOf :: [Path] -> Scope
scopeOf xs = M.fromList [(x,Nothing) | x <- xs]

defScope :: Def -> Scope
defScope d = case d of
  DefFun{ defArgs = ps } -> scopeOf [x | (x,_,_) <- ps]
  DefVal{} -> M.empty

-- the scope of a subexpression of `expr` that binds `xs`
bindScope :: VExpr -> [Path] -> Scope -> Scope
bindScope expr xs scope = M.union (M.fromList [(x,rest x) | x <- xs]) scope
  where
    rest x = case expr of
      CaseA _ z as _ | x == child z SRest -> Just [i | (i,_,_) <- as]
      _ -> Nothing

-- Reuse an already established alternative, except when destructuring has the
-- effect of consuming a unique scrutinee. A residual sum also needs the same tags.
knownAlt :: Scope -> VExpr -> Maybe Int
knownAlt scope expr = do
  z <- scrutVar expr
  m <- case destructAOf expr of
         Just ds -> Just (dsMode ds)
         Nothing -> dsMode <$> destructVOf expr
  let alts = getConst (descendB (const (Const [])) (const (Const [])) (\bs e -> Const [(bs,e)]) expr)
      indices = case expr of CaseA _ _ as _ -> [i | (i,_,_) <- as]; _ -> []
  listToMaybe [i | m /= Unique, (i,(bs@(_:_),_)) <- zip [0..] alts, let ss = map snd bs, all (not . null) ss
                , all (\s -> M.member (foldl child z s) scope) ss
                , [SRest] `notElem` ss || M.lookup (child z SRest) scope == Just (Just indices)]

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

substE :: Subst -> VExpr -> VExpr
substE sub expr = substEIn (scopeFor sub (fvE expr)) sub expr

scopeFor :: Subst -> S.Set Path -> Scope
scopeFor sub = scopeOf . S.toList . S.unions . map (\x -> maybe (S.singleton x) fvV (sub x)) . S.toList

-- Substitution rebuilds destructuring binders along with their scrutinee. This
-- preserves path names while doing the substitution's existing traversal; it is
-- not a subsequent normalization pass. Descriptions use the same substitution.
substEIn :: Scope -> Subst -> VExpr -> VExpr
substEIn = substStep substEIn

-- One expression layer, including value annotations and the scopes of lambdas.
substStep :: SubstExpr -> SubstExpr
substStep = substStepWith id

-- A copy also gives each root binder a new name. Canonical parts and all
-- description annotations follow the same substitution as ordinary operands.
substStepWith :: (Path -> Path) -> SubstExpr -> SubstExpr
substStepWith renameRoot recur scope sub expr
  = case chosen of
      Just (bs,e) -> recur scope (under bs) e
      Nothing -> runIdentity (descendB Identity Identity branch operands)
  where
    annotated = case expr of
      Let x t e1 e2 -> Let x (substVType sub t) e1 e2
      LetYield x t e1 e2 e3 -> LetYield x (substVType sub t) e1 e2 e3
      Yielded t -> Yielded (substVType sub t)
      Unreachable t -> Unreachable (substVType sub t)
      Call f ts vs -> Call f (map (substAType sub) ts) vs
      Jump j ts vs -> Jump j (map (substAType sub) ts) vs
      Join j tvs ps e1 e2 -> let sub' = hide [x | (x,_,_) <- ps] sub
                            in Join j tvs [(x,m,substVType sub' t) | (x,m,t) <- ps] e1 e2
      _ -> expr
    operands = runIdentity (descendB (Identity . substName sub) (Identity . substVWith renameRoot recur scope sub)
                             (\bs e -> Identity (map fst bs,e)) annotated)
    named bs = [(x,fromMaybe (renameRoot x) (pathOf (scrutVar operands) step)) | (x,step) <- bs]
    under bs = bindSub bs sub
    alts = getConst (descendB (const (Const [])) (const (Const [])) (\bs e -> Const [(bs,e)]) operands)
    namedOperands = runIdentity (descendB Identity Identity (\bs e -> Identity (map snd (named bs),e)) operands)
    chosen = do i <- knownAlt scope namedOperands
                let (bs,e) = alts !! i
                return (named bs,e)
    branch bs e =
      let pairs = named bs
          xs = map snd pairs
      in Identity (xs,recur (bindScope operands xs scope) (under pairs) e)

-- Extend a substitution with the (possibly renamed) binders of a scope.
bindSub :: [(Path,Path)] -> Subst -> Subst
bindSub bs sub p = case [(x,y) | (x,y) <- bs, p `within` x] of
  ((x,y):_) -> project (Var y) (stepsFrom x p)
  [] -> sub p

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

renameE :: M.Map Path Path -> VExpr -> VExpr
renameE = replaceE . M.map Var

-- rename a variable and its parts, also where they are bound
renamePath :: Path -> Path -> VExpr -> VExpr
renamePath x y = renameE (M.singleton x y)
