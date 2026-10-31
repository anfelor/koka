-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Shared construction, analysis and substitution for the typed IR.
module Backend.Typed.Common where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Monoid( Sum(..) )
import Data.Functor.Identity( Identity(..) )
import Data.List( sortOn )
import Data.Maybe( listToMaybe, fromMaybe )
import Common.Name
import Common.NamePrim( nameTpReuse )
import Backend.Typed.Syntax
import Backend.Typed.Types( Sub, Types(..), inst, sumAlts, sumOf, mapReuseContents, traverseReuseContents )
import Backend.Typed.Traversal

-- A continuation that wraps an expression.
type K = VExpr -> VExpr

compose :: [K] -> K
compose = foldr (.) id

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

-- the fields of a product variable (`[proj]`), named by their paths
fieldsAt :: Path -> VType -> [(Path,Int,VType)]
fieldsAt x t
  = case t of
      VProd fs -> [(child x (SField i f),i,s) | (i,(f,s)) <- zip [0..] fs]
      _ -> []

-- The duplication rule: the type of the copy of a variable of type `t`
dupType :: Ty -> Either String Ty
dupType t
  = case t of
      V (VReuse _ _ _) -> Left "dup of a reuse credit"
      V (VCell _ _) -> Left "dup of a cell"
      V _ -> Right t
      A _ -> Left "dup of a boxed value"

-- values of these types need no reference counting, where `unroll` gives the body of a
-- named type if it is known (a type with a single constructor without fields, for example)
isTrivialWith :: (AType -> Maybe AType) -> Ty -> Bool
isTrivialWith unroll t
  = case t of
      V v -> trivialV v
      A a -> trivialA a
  where
    trivialV v = case v of
                   VRaw _       -> True
                   VUnit        -> True
                   VProd fs     -> all (trivialV . snd) fs
                   VSum ts      -> all (trivialV . snd) ts
                   VExists _ b  -> trivialV b
                   VPtr a       -> trivialA a
                   VReuse _ _ _   -> False
                   VCtx _ _ _   -> False
                   VCell _ _    -> False
    trivialA a = case a of
                   AUnit     -> True
                   ASum ts   -> all (trivialA . snd) ts
                   ACon n _  -> n == nameTpReuse || maybe False trivialA (unroll a)
                   ALazy l b -> trivialA l && trivialA b
                   AMu _ _ _ _ -> maybe False trivialA (unroll a)
                   ABox _    -> False
                   AScalar _ -> False
                   AFun _ _  -> False
                   AForall _ _ -> False
                   AVar _    -> False
                   AApp _ _  -> False
                   ALam _ _  -> False

-- Boxed sum alternatives must have a tag determined by their construction: sums are flat and
-- their tags are increasing.
isShape :: AType -> Bool
isShape a = case a of
  ASum ts -> not (null ts) && all (\(i,t) -> i >= 1 && isAlt t) ts
             && and [i < j | ((i,_),(j,_)) <- zip ts (drop 1 ts)]
  _ -> isAlt a
  where
    isAlt t = case t of
                AUnit -> True
                ABox _ -> True
                _ -> False

-- Credits and cells have ownership but no reference count: duplication cannot create another
-- owner, so they are not stored in a heap block or captured by a closure.
containsLinear :: Ty -> Bool
containsLinear (V v) = case v of
  VPtr a -> containsLinear (A a)
  VProd fs -> any (containsLinear . V . snd) fs
  VSum ts -> any (containsLinear . V . snd) ts
  VExists _ b -> containsLinear (V b)
  VUnit -> False
  VRaw _ -> False
  VReuse _ _ _ -> True
  VCtx _ _ _ -> False
  VCell _ _ -> True
containsLinear (A a) = case a of
  ABox v -> containsLinear (V v)
  AScalar _ -> False
  ASum ts -> any (containsLinear . A . snd) ts
  AForall _ b -> containsLinear (A b)
  ALam _ b -> containsLinear (A b)
  ALazy l b -> containsLinear (A l) || containsLinear (A b)
  AMu _ _ b ts -> any (containsLinear . A) (b : ts)
  ACon _ ts -> any (containsLinear . A) ts
  AApp _ ts -> any (containsLinear . A) ts
  AVar _ -> False
  AFun _ _ -> False
  AUnit -> False

-- the name under which the type of the hole is bound in the one-hole value of a context
nameHole :: Path
nameHole = root (newHiddenName "hole")

-- the one-hole values `K` of `[ctx]`: the hole occurs once, in a field of a block that `K`
-- allocates, or `K` is the hole itself (the empty context)
isCtxValue :: VVal -> Bool
isCtxValue k
  = holes k == 1 && (k == Hole || path k)
  where
    path v = case v of
               Ptr _ a -> block a
               _ -> False
    block a = case a of
                Roll _ b -> block b
                InjA _ _ b -> block b
                InjLazy _ _ b -> block b
                Box v -> field v
                BoxAt _ v -> field v
                _ -> False
    field v = case v of
                Hole -> True
                Tuple ws -> any field [w | w <- ws, holes w == 1]
                _ -> path v

-- the occurrences of the hole, except in nested contexts and closures (which do not bind it)
holes :: VVal -> Int
holes = getSum . holesV
  where
    holesV v = case v of
                 Hole -> Sum 1
                 Context _ _ -> Sum 0
                 _ -> getConst (descendV (Const . holesA) (Const . holesV) v)
    holesA a = case a of
                 Lam{} -> Sum 0
                 _ -> getConst (descendA (const (Const (Sum 0))) (Const . holesA) (Const . holesV) a)

-- the product of values (`Types.prodV`)
prodVal :: [VVal] -> VVal
prodVal []  = UnitV
prodVal [v] = v
prodVal vs  = Tuple vs

tapp :: VVal -> [AType] -> VVal
tapp v []  = v
tapp v tys = TyApp v tys

injA :: [AType] -> Int -> AVal -> AVal
injA [_] 0 v = v
injA ss i v = InjA (fst (sumAlts ss !! i)) (sumOf ss) v

-- a case on each alternative of a boxed sum `a`; the branch gets the alternative, a variable at a
-- boxed type that it may only destructure. `cons` are the constructors of the alternatives.
caseSum :: MonadFail m => [Con] -> [AType] -> Path -> (Int -> Path -> m VExpr) -> m VExpr
caseSum cons shapes a branch
  = case shapes of
      [] -> fail "empty case"
      [_] -> branch 0 a
      _ -> do alts <- mapM (\i -> do let tag = fst (sumAlts shapes !! i)
                                         y = child a (SInjA tag (cons !! i))
                                     e <- branch i y
                                     return (tag,y,e)) [0 .. length shapes - 1]
              return (CaseA Owned a alts Nothing)

-- `[unbox-ru]` and `[lock]` of a box `z` take its contents out of its block and bind its
-- block as a new root: the box, the root and the body
takesContents :: VExpr -> Maybe (Path,Path,VExpr)
takesContents expr
  = case expr of
      UnboxRu z r e -> Just (z,r,e)
      Lock z c e -> Just (z,c,e)
      _ -> Nothing

-- the bodies of the alternatives of a `CaseV`, by index
altBodies :: [(Int,Path,VExpr)] -> [VExpr]
altBodies alts = [e | (_,_,e) <- sortOn (\(i,_,_) -> i) alts]

-- the variable that a destructuring form destructures
scrutVar :: VExpr -> Maybe Path
scrutVar expr
  = case expr of
      _ | Just (z,_,_) <- takesContents expr -> Just z
        | Just ds <- destructAOf expr -> Just (dsScrut ds)
        | Just ds <- destructVOf expr, Var z <- dsScrut ds -> Just z
        | otherwise -> Nothing

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

-- the arguments of each jump to a join point; jumps are never inside values, and an inner
-- join of the same name shadows it
jumpArgs :: Name -> VExpr -> [[VVal]]
jumpArgs j expr
  = case expr of
      Jump k _ vs | k == j -> [vs]
      Join k _ _ e1 _ | k == j -> jumpArgs j e1
      _ -> getConst (descendE (const (Const [])) (const (Const [])) (\_ e -> Const (jumpArgs j e)) expr)

varOf :: VVal -> Path
varOf (Var y) = y
varOf v       = error ("Backend.Typed.Common.varOf: not a variable: " ++ show v)

-- a top-level value, possibly instantiated (`[dup-glob]`)
isGlob :: VVal -> Bool
isGlob v
  = case v of
      Glob _ _ -> True
      TyApp w _ -> isGlob w
      _ -> False

-- free variables

fvA :: AVal -> S.Set Path
fvA val
  = case val of
      Lam ps _ e -> fvE e `S.difference` S.fromList [x | (x,_,_) <- ps]
      _ -> getConst (descendA (Const . S.singleton) (Const . fvA) (Const . fvV) val)

fvV :: VVal -> S.Set Path
fvV val
  = case val of
      Var x -> S.singleton x
      _ -> getConst (descendV (Const . fvA) (Const . fvV) val)

fvE :: VExpr -> S.Set Path
fvE expr = getConst (descendE (Const . S.singleton) (Const . fvV) (\xs e -> Const (fvE e `S.difference` S.fromList xs)) expr)

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

renameE :: M.Map Path Path -> VExpr -> VExpr
renameE = replaceE . M.map Var

-- all bound variables (with repetitions)
bindersE :: VExpr -> [Path]
bindersE = getConst . descendE (const (Const [])) (Const . bindersV) (\xs e -> Const (xs ++ bindersE e))

bindersA :: AVal -> [Path]
bindersA val
  = case val of
      Lam ps _ e -> [x | (x,_,_) <- ps] ++ bindersE e
      _ -> getConst (descendA (const (Const [])) (Const . bindersA) (Const . bindersV) val)

bindersV :: VVal -> [Path]
bindersV = getConst . descendV (Const . bindersA) (Const . bindersV)

-- destructuring forms: the mode, the scrutinee, the alternatives with their binders, and a rebuild function.
-- Boxed scrutinees are names; unboxed scrutinees are values.
data Destruct v = Destruct{ dsMode :: Mode, dsScrut :: v, dsAlts :: [([Path],VExpr)], dsBuild :: Mode -> v -> [VExpr] -> VExpr }

destructAOf :: VExpr -> Maybe (Destruct Path)
destructAOf expr
  = case expr of
      SplitA m v k (x,e1) (y,e2) -> Just (Destruct m v [([x],e1),([y],e2)]
                                      (\m' v' es -> SplitA m' v' k (x,head es) (y,last es)))
      IfWhnf m v (x,e1) (y,e2) -> Just (Destruct m v [([x],e1),([y],e2)]
                                    (\m' v' es -> IfWhnf m' v' (x,head es) (y,last es)))
      CaseA m v alts def -> Just (Destruct m v ([([x],e) | (_,x,e) <- alts] ++ maybe [] (\(x,e) -> [([x],e)]) def)
                                  (\m' v' es -> CaseA m' v' [(i,x,e) | ((i,x,_),e) <- zip alts es]
                                    (fmap (\(x,_) -> (x,last es)) def)))
      Unroll m v x e        -> Just (Destruct m v [([x],e)] (\m' v' es -> Unroll m' v' x (head es)))
      Unbox m v x e         -> Just (Destruct m v [([x],e)] (\m' v' es -> Unbox m' v' x (head es)))
      Unscalar m v x e      -> Just (Destruct m v [([x],e)] (\m' v' es -> Unscalar m' v' x (head es)))
      CaseOpen m v alts def -> Just (Destruct m v ([(xs,e) | (_,xs,e) <- alts] ++ [([],def)])
                                       (\m' v' es -> CaseOpen m' v' [(c,xs,e) | ((c,xs,_),e) <- zip alts es] (last es)))
      Proj{} -> Nothing
      CaseV{} -> Nothing
      Deref{} -> Nothing
      Unpack{} -> Nothing
      Ret{} -> Nothing
      Let{} -> Nothing
      LetYield{} -> Nothing
      Yielded{} -> Nothing
      Unreachable{} -> Nothing
      Call{} -> Nothing
      App{} -> Nothing
      CaseLit{} -> Nothing
      Gen{} -> Nothing
      Dup{} -> Nothing
      Drop{} -> Nothing
      Free{} -> Nothing
      IsUnique{} -> Nothing
      IfFull{} -> Nothing
      UnboxRu{} -> Nothing
      CopyRu{} -> Nothing
      Lock{} -> Nothing
      Join{} -> Nothing
      Jump{} -> Nothing

destructVOf :: VExpr -> Maybe (Destruct VVal)
destructVOf expr
  = case expr of
      SplitA{} -> Nothing
      Proj m v i x e        -> Just (Destruct m v [([x],e)] (\m' v' es -> Proj m' v' i x (head es)))
      CaseV m v alts        -> Just (Destruct m v [([x],e) | (_,x,e) <- alts] (\m' v' es -> CaseV m' v' [(i,x,e) | ((i,x,_),e) <- zip alts es]))
      Deref m v x e         -> Just (Destruct m v [([x],e)] (\m' v' es -> Deref m' v' x (head es)))
      Unpack m v tvs x e    -> Just (Destruct m v [([x],e)] (\m' v' es -> Unpack m' v' tvs x (head es)))
      CaseA{} -> Nothing
      Unroll{} -> Nothing
      Unbox{} -> Nothing
      Unscalar{} -> Nothing
      CaseOpen{} -> Nothing
      Ret{} -> Nothing
      Let{} -> Nothing
      LetYield{} -> Nothing
      Yielded{} -> Nothing
      Unreachable{} -> Nothing
      Call{} -> Nothing
      App{} -> Nothing
      CaseLit{} -> Nothing
      Gen{} -> Nothing
      Dup{} -> Nothing
      Drop{} -> Nothing
      Free{} -> Nothing
      IsUnique{} -> Nothing
      IfWhnf{} -> Nothing
      IfFull{} -> Nothing
      UnboxRu{} -> Nothing
      CopyRu{} -> Nothing
      Lock{} -> Nothing
      Join{} -> Nothing
      Jump{} -> Nothing

-- reading the contents of a box never moves them
isRead :: VExpr -> Bool
isRead expr
  = case expr of
      SplitA{}    -> False
      Unbox{}     -> True
      Unscalar{}  -> False
      CaseOpen{}  -> True
      Proj{}      -> False
      CaseV{}     -> False
      CaseA{}     -> False
      Deref{}     -> False
      Unroll{}    -> False
      Unpack{}    -> False
      Ret{}       -> False
      Let{}       -> False
      LetYield{}  -> False
      Yielded{}   -> False
      Unreachable{} -> False
      Call{}      -> False
      App{}       -> False
      CaseLit{}   -> False
      Gen{}       -> False
      Dup{}       -> False
      Drop{}      -> False
      Free{}      -> False
      IsUnique{}  -> False
      IfWhnf{}    -> False
      IfFull{}    -> False
      UnboxRu{}   -> False
      CopyRu{}    -> False
      Lock{}      -> False
      Join{}      -> False
      Jump{}      -> False

-- the binders of these destructuring forms are the scrutinee's pointer (the scrutinee itself
-- for `[unpack]`), so they may be unique
keepsPointer :: VExpr -> Bool
keepsPointer expr
  = case expr of
      SplitA{}    -> True
      IfWhnf{}    -> True
      CaseA{}     -> True
      Deref{}     -> True
      Unroll{}    -> True
      Unpack{}    -> True
      Proj{}      -> False
      CaseV{}     -> False
      Unbox{}     -> False
      Unscalar{}  -> False
      CaseOpen{}  -> False
      Ret{}       -> False
      Let{}       -> False
      LetYield{}  -> False
      Yielded{}   -> False
      Unreachable{} -> False
      Call{}      -> False
      App{}       -> False
      CaseLit{}   -> False
      Gen{}       -> False
      Dup{}       -> False
      Drop{}      -> False
      Free{}      -> False
      IsUnique{}  -> False
      IfFull{}    -> False
      UnboxRu{}   -> False
      CopyRu{}    -> False
      Lock{}      -> False
      Join{}      -> False
      Jump{}      -> False

-- Where a variable gets the bits of another variable: a copy (`[dup]`) gets those
-- of its variable, and a parameter of a join point those of its arguments.
data Source = Copy Path | Param [VVal]

type Sources = M.Map Path Source

sources :: VExpr -> Sources
sources expr = M.union here (getConst (descendE (const (Const M.empty)) (Const . sourcesV) (\_ e -> Const (sources e)) expr))
  where
    here = case expr of
             Dup x y _ -> M.singleton y (Copy x)
             Join j _ ps _ e2 -> M.fromList [(y,Param [vs !! i | vs <- jumpArgs j e2]) | (i,(y,_,_)) <- zip [0..] ps]
             _ -> M.empty
    sourcesV = getConst . descendV (Const . sourcesA) (Const . sourcesV)
    sourcesA a = case a of
                   Lam _ _ e -> sources e
                   _ -> getConst (descendA (const (Const M.empty)) (Const . sourcesA) (Const . sourcesV) a)

-- The variable whose bits a variable has, through the longest prefix of its path that has a
-- source: a join parameter has the bits of its arguments if they are the same.
sameBits :: Sources -> Path -> Path
sameBits src x@(Path r ss)
  = case [(k,s) | k <- [length ss, length ss - 1 .. 0], Just s <- [M.lookup (Path r (take k ss)) src]] of
      ((k,s):_) -> case s of
                     Copy y -> sameBits src (extend y (drop k ss))
                     Param vs | Just (y:ys) <- mapM sameOf vs, all (== y) ys -> extend y (drop k ss)
                     _ -> x
      [] -> x
  where
    extend (Path y ts) rest = Path y (ts ++ rest)
    sameOf (Var y) = Just (sameBits src y)
    sameOf _ = Nothing

sameBitsV :: Sources -> VVal -> VVal
sameBitsV src v
  = case v of
      Var x -> Var (sameBits src x)
      _ -> mapV id (sameBitsV src) v

-- All the types that a program mentions.
programTypes :: Program -> [VType]
programTypes prog = concatMap sig (M.elems (progSigs prog)) ++ concatMap def (progDefs prog)
                    ++ concatMap (\d -> vars (tdefParams d) ++ maybe [] at (tdefBody d)) (M.elems (progTypes prog))
  where
    vars = map (VPtr . AVar)
    sig s = case s of
      SigFun vs ps r -> vars vs ++ (r : map snd ps)
      SigVal vs t -> vars vs ++ [t]
      SigCon vs ts _ -> vars vs ++ ts
    def d = case d of
      DefFun _ vs ps r e -> vars vs ++ (r : map (\(_,_,t) -> t) ps ++ et e)
      DefVal _ vs t e -> vars vs ++ (t : et e)
    at a = case a of
      ABox t -> [t]
      ASum ts -> concatMap (at . snd) ts
      AFun ps r -> r : map snd ps
      AForall _ b -> at b
      ALam _ b -> at b
      ALazy l b -> at l ++ at b
      AMu _ _ b ts -> concatMap at (b : ts)
      ACon _ ts -> concatMap at ts
      AApp _ ts -> concatMap at ts
      _ -> []
    et e = here ++ getConst (descendE (const (Const [])) (Const . vt) (\_ b -> Const (et b)) e)
      where here = case e of
                     Let _ t _ _ -> [t]
                     LetYield _ t _ _ _ -> [t]
                     Yielded t -> [t]
                     Unreachable t -> [t]
                     Join _ _ ps _ _ -> map (\(_,_,t) -> t) ps
                     Jump _ ts _ -> concatMap at ts
                     Call _ ts _ -> concatMap at ts
                     Gen vs _ -> map (VPtr . AVar) vs
                     Unpack _ _ vs _ _ -> map (VPtr . AVar) vs
                     _ -> []
    vt v = here ++ getConst (descendV (Const . avTypes) (Const . vt) v)
      where here = case v of
                     Glob _ ts -> concatMap at ts
                     TyApp _ ts -> concatMap at ts
                     Context a _ -> at a
                     Ptr a _ -> at a
                     Inj _ t _ -> [t]
                     Pack t ts _ -> t : concatMap at ts
                     NoReuse _ p -> maybe [] (\(Contents _ _ t) -> [t]) p
                     _ -> []
    avTypes a = case a of
      Lam ps r e -> r : map (\(_,_,t) -> t) ps ++ et e
      Roll t w -> at t ++ avTypes w
      InjA _ t w -> at t ++ avTypes w
      InjLazy _ t w -> at t ++ avTypes w
      OpenCon _ ts ws -> concatMap at ts ++ concatMap vt ws
      _ -> getConst (descendA (const (Const [])) (Const . avTypes) (Const . vt) a)
