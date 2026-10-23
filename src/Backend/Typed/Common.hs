-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Traversals and derived rules for the typed intermediate language.
module Backend.Typed.Common where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Monoid( Sum(..) )
import Data.Functor.Identity( Identity(..) )
import Data.List( isPrefixOf )
import Data.Maybe( listToMaybe, fromMaybe )
import Control.Monad( foldM )
import Common.Name
import Common.NamePrim( nameTpReuse )
import Backend.Typed.Syntax
import Backend.Typed.Types( Sub, Types(..), inst, sumAlts, sumOf, mapReuseContents, traverseReuseContents )

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
            dropAlt (i,s) = do let y = child x (SInjV i)
                               body <- dropValue trivial fresh (M.insert y Nothing scope) y (V s) (Ret UnitV)
                               return (y,body)
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
        VUnit -> return e
        VRaw _ -> return e

-- The fields of a product along its right spine (`[proj]`): the steps to each field and its
-- type. In layout normal form these are the fields in memory order.
productFields :: VType -> [([Step],VType)]
productFields t
  = case t of
      VProd a b -> ([SFst],a) : [(SSnd:ss,s) | (ss,s) <- spine b]
      _ -> []
  where
    spine s@VProd{} = productFields s
    spine s = [([],s)]

-- the steps to the fields of a right-nested product of `n` fields (`productFields`): field i at
-- `snd`ⁱ `fst` and the last one at `snd`ⁿ⁻¹
fieldSteps :: Int -> [[Step]]
fieldSteps n = [replicate i SSnd ++ [SFst] | i <- [0 .. n-2]] ++ [replicate (n-1) SSnd | n > 0]

-- the type at steps into a product
partAt :: VType -> [Step] -> Maybe VType
partAt t [] = Just t
partAt (VProd a b) (s:ss)
  = case s of
      SFst -> partAt a ss
      SSnd -> partAt b ss
      _ -> Nothing
partAt _ _ = Nothing

-- the fields of a product variable, named by their paths
fieldsAt :: Path -> VType -> [(Path,[Step],VType)]
fieldsAt x t = [(foldl child x ss,ss,s) | (ss,s) <- productFields t]

-- project the fields of a product variable around an expression, reusing those in scope
projectAll :: Scope -> Mode -> Path -> [(Path,[Step],VType)] -> VExpr -> VExpr
projectAll scope m x fields body = foldr (\(y,ss,_) e -> reuseParts scope (Proj m (Var x) ss y e)) body fields

-- The duplication rule, shared by the type and linearity checkers.
checkDupType :: Ty -> Either String ()
checkDupType t
  = case t of
      V (VReuse _ _ _) -> Left "dup of a reuse credit"
      V _ -> Right ()
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
                   VProd x y    -> trivialV x && trivialV y
                   VSum ts      -> all trivialV ts
                   VExists _ b  -> trivialV b
                   VPtr a       -> trivialA a
                   VReuse _ _ _   -> False
                   VCtx _ _ _   -> False
    trivialA a = case a of
                   AUnit     -> True
                   ASum ts   -> all (trivialA . snd) ts
                   ACon n _  -> n == nameTpReuse || maybe False trivialA (unroll a)
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

-- Credits have ownership but no reference count: duplication cannot create another owner.
containsReuse :: Ty -> Bool
containsReuse (V v) = case v of
  VPtr a -> containsReuse (A a)
  VProd a b -> containsReuse (V a) || containsReuse (V b)
  VSum ts -> any (containsReuse . V) ts
  VExists _ b -> containsReuse (V b)
  VUnit -> False
  VRaw _ -> False
  VReuse _ _ _ -> True
  VCtx _ _ _ -> False
containsReuse (A a) = case a of
  ABox v -> containsReuse (V v)
  AScalar _ -> False
  ASum ts -> any (containsReuse . A . snd) ts
  AForall _ b -> containsReuse (A b)
  ALam _ b -> containsReuse (A b)
  ACon _ ts -> any (containsReuse . A) ts
  AApp _ ts -> any (containsReuse . A) ts
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
                Box v -> field v
                BoxAt _ v -> field v
                _ -> False
    field v = case v of
                Hole -> True
                Pair x y | holes x == 1 -> field x
                         | otherwise -> field y
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

tapp :: VVal -> [AType] -> VVal
tapp v []  = v
tapp v tys = TyApp v tys

injA :: [AType] -> Int -> AVal -> AVal
injA [_] 0 v = v
injA ss i v = InjA (fst (sumAlts ss !! i)) (sumOf ss) v

-- a case on each alternative of a boxed sum `a`; the branch gets the alternative, a variable at a
-- boxed type that it may only destructure
caseSum :: MonadFail m => (String -> m Path) -> [AType] -> Path -> (Int -> Path -> m VExpr) -> m VExpr
caseSum fresh shapes a branch
  = case shapes of
      [] -> fail "empty case"
      [_] -> branch 0 a
      _ -> do alts <- mapM (\i -> do y <- fresh "y"
                                     e <- branch i y
                                     return (fst (sumAlts shapes !! i),y,e)) [0 .. length shapes - 1]
              return (CaseA Owned a alts Nothing)

-- one-level traversals

-- Names are operands, not values: a traversal must preserve their variable form.
-- Lambda bodies are handled separately from the values directly inside a value.
descendA :: Applicative f => (Path -> f Path) -> (AVal -> f AVal) -> (VVal -> f VVal) -> AVal -> f AVal
descendA fn fa fv val
  = case val of
      InjA i a v     -> InjA i a <$> fa v
      Roll a v       -> Roll a <$> fa v
      Box v          -> Box <$> fv v
      Scalar v       -> Scalar <$> fv v
      OpenCon c ts vs -> OpenCon c ts <$> traverse fv vs
      BoxAt r v      -> BoxAt <$> fn r <*> fv v
      BoxIn x v      -> BoxIn <$> fn x <*> fv v
      Fun _          -> pure val
      UnitA          -> pure val
      Lam _ _ _      -> pure val

descendV :: Applicative f => (AVal -> f AVal) -> (VVal -> f VVal) -> VVal -> f VVal
descendV fa fv val
  = case val of
      Inj i t v      -> Inj i t <$> fv v
      Pair v w       -> Pair <$> fv v <*> fv w
      Ptr a v        -> Ptr a <$> fa v
      Pack t ts v    -> Pack t ts <$> fv v
      TyApp v ts     -> (`TyApp` ts) <$> fv v
      DupV v         -> DupV <$> fv v
      Context b v    -> Context b <$> fv v
      Plug c v       -> Plug <$> fv c <*> fv v
      CtxCopy v      -> CtxCopy <$> fv v
      Append c d     -> Append <$> fv c <*> fv d
      Hole           -> pure val
      Var _          -> pure val
      Glob _ _       -> pure val
      UnitV          -> pure val
      Lit _          -> pure val
      NoReuse _ _    -> pure val   -- a description is not an operand

mapA :: (Path -> Path) -> (AVal -> AVal) -> (VVal -> VVal) -> AVal -> AVal
mapA fn fa fv = runIdentity . descendA (Identity . fn) (Identity . fa) (Identity . fv)

mapV :: (AVal -> AVal) -> (VVal -> VVal) -> VVal -> VVal
mapV fa fv = runIdentity . descendV (Identity . fa) (Identity . fv)

-- the operands and subexpressions of an expression, with the variables bound in each subexpression
descendE :: Applicative f => (Path -> f Path) -> (VVal -> f VVal) -> ([Path] -> VExpr -> f VExpr) -> VExpr -> f VExpr
descendE fn fv fe = descendB fn fv (\bs e -> let xs = map fst bs in (,) xs <$> fe xs e)

-- Like `descendE`, but each binder comes with its steps from the scrutinee, and `fb` gives new
-- binders for a subexpression. The binders of a `let`, a dup, a join point and the credit of
-- `[unbox-ru]` have no steps, and neither has that of `[unbox-lazy]`, which takes the contents
-- out of the box, or that of `[unscalar]`, which copies them.
descendB :: Applicative f => (Path -> f Path) -> (VVal -> f VVal) -> ([(Path,[Step])] -> VExpr -> f ([Path],VExpr)) -> VExpr -> f VExpr
descendB fn fv fb expr
  = case expr of
      Ret v                 -> Ret <$> fv v
      Let x t e1 e2         -> (\e1' (x',e2') -> Let x' t e1' e2') <$> plain e1 <*> one x [] e2
      LetYield x t e1 e2 e3 -> (\e1' (x',e2') e3' -> LetYield x' t e1' e2' e3') <$> plain e1 <*> one x [] e2 <*> plain e3
      Yielded _             -> pure expr
      Call f ts vs          -> Call f ts <$> traverse fv vs
      App f vs              -> App <$> fn f <*> traverse fv vs
      Proj m v ss x e       -> (\v' (x',e') -> Proj m v' ss x' e') <$> fv v <*> one x ss e
      CaseV m v alts        -> CaseV m <$> fv v <*> traverse (\(i,(x,e)) -> one x [SInjV i] e) (zip [0..] alts)
      CaseA m v alts def    -> CaseA m <$> fn v <*> traverse (\(i,x,e) -> (\(x',e') -> (i,x',e')) <$> one x [SInjA i] e) alts
                                       <*> traverse (\(x,e) -> one x [SRest] e) def
      SplitA m v k (x,e1) (y,e2) -> SplitA m <$> fn v <*> pure k <*> one x [SLo] e1 <*> one y [SHi] e2
      Deref m v x e         -> (\v' (x',e') -> Deref m v' x' e') <$> fv v <*> one x [SDeref] e
      Unroll m v x e        -> (\v' (x',e') -> Unroll m v' x' e') <$> fn v <*> one x [SRoll] e
      Unbox m v x e         -> (\v' (x',e') -> Unbox m v' x' e') <$> fn v <*> one x [SContents] e
      Unscalar m v x e      -> (\v' (x',e') -> Unscalar m v' x' e') <$> fn v <*> one x [] e
      UnboxLazy v x e       -> (\v' (x',e') -> UnboxLazy v' x' e') <$> fn v <*> one x [] e
      Unpack m v tvs x e    -> (\v' (x',e') -> Unpack m v' tvs x' e') <$> fv v <*> one x [SPack] e
      CaseLit v alts def    -> CaseLit <$> fv v <*> traverse (\(l,e) -> (,) l <$> plain e) alts <*> plain def
      CaseOpen m v alts def -> CaseOpen m <$> fn v <*> traverse (\(c,xs,e) -> (\(xs',e') -> (c,xs',e')) <$> fb (zip xs (map (SOpen c :) (fieldSteps (length xs)))) e) alts
                                          <*> plain def
      Gen tvs e             -> Gen tvs <$> plain e
      Drop x e              -> Drop <$> fn x <*> plain e
      Free r e              -> Free <$> fn r <*> plain e
      Dup x y e             -> (\x' (y',e') -> Dup x' y' e') <$> fn x <*> one y [] e
      IsUnique x e1 e2      -> IsUnique <$> fn x <*> plain e1 <*> plain e2
      IfFull r e1 e2        -> IfFull <$> fn r <*> plain e1 <*> plain e2
      UnboxRu v r e         -> (\v' (r',e') -> UnboxRu v' r' e') <$> fn v <*> one r [] e
      Join j tvs ps e1 e2   -> (\(xs,e1') e2' -> Join j tvs [(x',m,t) | (x',(_,m,t)) <- zip xs ps] e1' e2')
                                 <$> fb [(x,[]) | (x,_,_) <- ps] e1 <*> plain e2
      Jump j ts vs          -> Jump j ts <$> traverse fv vs
  where
    plain e = snd <$> fb [] e
    one x s e = (\(xs,e') -> (single xs,e')) <$> fb [(x,s)] e
    single xs = case xs of
                  [x] -> x
                  _   -> error "Backend.Typed.Common.descendB: expecting one binder"

-- A `[let-yield]` as the `let` that is taken if no effect yields, and its yielding branch,
-- which is cold.
yieldingAlts :: VExpr -> Maybe (VExpr,VExpr)
yieldingAlts expr
  = case expr of
      LetYield x t e1 e2 e3 -> Just (Let x t e1 e2,e3)
      _ -> Nothing

-- the binder at a step from a variable
child :: Path -> Step -> Path
child (Path x ss) s = Path x (ss ++ [s])

-- tag(z): the tag of the block of a box `z`, the alternative of a sum that it was reached
-- through (`[case-a]`), or 1 if it is the only one
boxTag :: Path -> Int
boxTag (Path _ ss)
  = case reverse ss of
      (SInjA i : _) -> i
      _ -> 1

-- the other part of the parent of a part of a pair or a box
sibling :: Step -> Maybe Step
sibling s
  = case s of
      SFst      -> Just SSnd
      SSnd      -> Just SFst
      SContents -> Just SCredit
      SCredit   -> Just SContents
      STaken    -> Just SCredit
      _         -> Nothing

-- A part without a sibling is all of its parent (in its alternative), so a use of it is a use
-- of the parent.
canonical :: Path -> Path
canonical (Path x ss) = Path x (reverse (dropWhile ((== Nothing) . sibling) (reverse ss)))

-- the variables on the path to a variable, from its root
prefixes :: Path -> [Path]
prefixes (Path x ss) = [Path x (take k ss) | k <- [0 .. length ss - 1]]

-- `x` is `y` or one of its parts
within :: Path -> Path -> Bool
within (Path x ss) (Path y ts) = x == y && ts `isPrefixOf` ss

-- the steps from a variable to one of its parts
stepsFrom :: Path -> Path -> [Step]
stepsFrom (Path _ ts) (Path _ ss) = drop (length ts) ss

-- the box whose block holds a variable in its contents: the variable before the last
-- `contents` step on its path, unless a `taken` step follows it (`[unbox-ru]` took the
-- contents out of their block)
boxOf :: Path -> Maybe Path
boxOf (Path x ss)
  = case break (`elem` [SContents,STaken]) (reverse ss) of
      (_,SContents : rest) -> Just (Path x (reverse rest))
      _ -> Nothing

-- `[unbox-ru]` of `z` renames its contents `z.contents` and their parts to `z.taken`, and
-- the body's uses of them are uses of the old names outside (`unrebase`)
rebase, unrebase :: Path -> Path -> Path
rebase z = renamePrefix (child z SContents) (child z STaken)
unrebase z = renamePrefix (child z STaken) (child z SContents)

renamePrefix :: Path -> Path -> Path -> Path
renamePrefix p q x
  | x `within` p = foldl child q (stepsFrom p x)
  | otherwise = x

-- the variable that a destructuring form destructures
scrutVar :: VExpr -> Maybe Path
scrutVar expr
  = case expr of
      UnboxRu z _ _ -> Just z
      _ | Just ds <- destructAOf expr -> Just (dsScrut ds)
        | Just ds <- destructVOf expr, Var z <- dsScrut ds -> Just z
        | otherwise -> Nothing

-- the part of a value at steps from it, if the value shows it
project :: VVal -> [Step] -> Maybe VVal
project v [] = Just v
project v (s:ss)
  = case (v,s) of
      (Var x, _) -> Just (Var (foldl child x (s:ss)))
      (Pair a _, SFst) -> project a ss
      (Pair _ b, SSnd) -> project b ss
      (Inj i _ w, SInjV j) | i == j -> project w ss
      (Pack _ _ w, SPack) -> project w ss
      _ -> Nothing

-- the known value of a variable: the part of the known value of the longest prefix of its path
valueAt :: M.Map Path VVal -> Path -> Maybe VVal
valueAt vals (Path x ss)
  = case [w | k <- [length ss, length ss - 1 .. 0], Just v <- [M.lookup (Path x (take k ss)) vals], Just w <- [project v (drop k ss)]] of
      (w:_) -> Just w
      [] -> Nothing

-- The path of a binder with steps (`descendB`) from the scrutinee `scrutVar`; the other
-- binders are roots.
pathOf :: Maybe Path -> [Step] -> Maybe Path
pathOf _ [] = Nothing
pathOf z ss = (\x -> foldl child x ss) <$> z

-- the arguments of each jump to a join point; jumps are never inside values, and an inner
-- join of the same name shadows it
jumpArgs :: Name -> VExpr -> [[VVal]]
jumpArgs j expr
  = case expr of
      Jump k _ vs | k == j -> [vs]
      Join k _ _ e1 _ | k == j -> jumpArgs j e1
      _ -> getConst (descendE (const (Const [])) (const (Const [])) (\_ e -> Const (jumpArgs j e)) expr)

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
      OpenCon c ts vs -> OpenCon c (map (subst sub) ts) (map (substTypesV sub) vs)
      _               -> mapA id (substTypesA sub) (substTypesV sub) val

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

-- the free variables of the body of `[unbox-ru]` of `z` under `z.taken` are those under `z.contents`
fvE :: VExpr -> S.Set Path
fvE expr
  = case expr of
      UnboxRu z r e -> S.insert z (S.map (unrebase z) (S.delete r (fvE e)))
      _ -> getConst (descendE (Const . S.singleton) (Const . fvV) (\xs e -> Const (fvE e `S.difference` S.fromList xs)) expr)

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

-- the scope of a subexpression of `expr` that binds `xs`, where `[unbox-ru]` also renames
-- the contents of its box
bindScope :: VExpr -> [Path] -> Scope -> Scope
bindScope expr xs scope = M.union (M.fromList [(x,rest x) | x <- xs]) outer
  where
    outer = case expr of
      UnboxRu z _ _ -> M.mapKeys (rebase z) scope
      _ -> scope
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
      Call f ts vs -> Call f (map (substAType sub) ts) vs
      Jump j ts vs -> Jump j (map (substAType sub) ts) vs
      Join j tvs ps e1 e2 -> let sub' = hide [x | (x,_,_) <- ps] sub
                            in Join j tvs [(x,m,substVType sub' t) | (x,m,t) <- ps] e1 e2
      _ -> expr
    operands = runIdentity (descendB (Identity . substName sub) (Identity . substVWith renameRoot recur scope sub)
                             (\bs e -> Identity (map fst bs,e)) annotated)
    named bs = [(x,fromMaybe (renameRoot x) (pathOf (scrutVar operands) step)) | (x,step) <- bs]
    under bs = bindSub bs (taken sub)
    -- `[unbox-ru]` renames the contents of its box: substitute its parts as the contents
    taken = case (expr,operands) of
      (UnboxRu z _ _,UnboxRu z' _ _)
        -> \s p -> if p `within` child z STaken
                     then substV (Just . Var . rebase z') <$> s (unrebase z p)
                     else s p
      _ -> id
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
      CaseA m v alts def -> Just (Destruct m v ([([x],e) | (_,x,e) <- alts] ++ maybe [] (\(x,e) -> [([x],e)]) def)
                                  (\m' v' es -> CaseA m' v' [(i,x,e) | ((i,x,_),e) <- zip alts es]
                                    (fmap (\(x,_) -> (x,last es)) def)))
      Unroll m v x e        -> Just (Destruct m v [([x],e)] (\m' v' es -> Unroll m' v' x (head es)))
      Unbox m v x e         -> Just (Destruct m v [([x],e)] (\m' v' es -> Unbox m' v' x (head es)))
      UnboxLazy v x e       -> Just (Destruct Borrowed v [([x],e)] (\_ v' es -> UnboxLazy v' x (head es)))
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
      Join{} -> Nothing
      Jump{} -> Nothing

destructVOf :: VExpr -> Maybe (Destruct VVal)
destructVOf expr
  = case expr of
      SplitA{} -> Nothing
      Proj m v ss x e       -> Just (Destruct m v [([x],e)] (\m' v' es -> Proj m' v' ss x (head es)))
      CaseV m v alts        -> Just (Destruct m v [([x],e) | (x,e) <- alts] (\m' v' es -> CaseV m' v' (zip (map fst alts) es)))
      Deref m v x e         -> Just (Destruct m v [([x],e)] (\m' v' es -> Deref m' v' x (head es)))
      Unpack m v tvs x e    -> Just (Destruct m v [([x],e)] (\m' v' es -> Unpack m' v' tvs x (head es)))
      CaseA{} -> Nothing
      Unroll{} -> Nothing
      Unbox{} -> Nothing
      UnboxLazy{} -> Nothing
      Unscalar{} -> Nothing
      CaseOpen{} -> Nothing
      Ret{} -> Nothing
      Let{} -> Nothing
      LetYield{} -> Nothing
      Yielded{} -> Nothing
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
      Join{} -> Nothing
      Jump{} -> Nothing

-- reading the contents of a box never moves them
isRead :: VExpr -> Bool
isRead expr
  = case expr of
      SplitA{}    -> False
      Unbox{}     -> True
      UnboxLazy{} -> True
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
      Join{}      -> False
      Jump{}      -> False

-- the binders of these destructuring forms are the scrutinee's pointer (the scrutinee itself
-- for `[unpack]`), so they may be unique
keepsPointer :: VExpr -> Bool
keepsPointer expr
  = case expr of
      SplitA{}    -> True
      CaseA{}     -> True
      Deref{}     -> True
      Unroll{}    -> True
      Unpack{}    -> True
      Proj{}      -> False
      CaseV{}     -> False
      Unbox{}     -> False
      UnboxLazy{} -> False
      Unscalar{}  -> False
      CaseOpen{}  -> False
      Ret{}       -> False
      Let{}       -> False
      LetYield{}  -> False
      Yielded{}   -> False
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
      Join{}      -> False
      Jump{}      -> False

-- Where a variable gets the bits of another variable: a copy (`[dup]`) gets those of its
-- variable, the contents taken by `[unbox-ru]` those of the old contents, and a parameter of
-- a join point those of its arguments.
data Source = Copy Path | Param [VVal]

type Sources = M.Map Path Source

sources :: VExpr -> Sources
sources expr = M.union here (getConst (descendE (const (Const M.empty)) (Const . sourcesV) (\_ e -> Const (sources e)) expr))
  where
    here = case expr of
             Dup x y _ -> M.singleton y (Copy x)
             UnboxRu z _ _ -> M.singleton (child z STaken) (Copy (child z SContents))
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
                     Copy y -> extend (sameBits src y) (drop k ss)
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
      ACon _ ts -> concatMap at ts
      AApp _ ts -> concatMap at ts
      _ -> []
    et e = here ++ getConst (descendE (const (Const [])) (Const . vt) (\_ b -> Const (et b)) e)
      where here = case e of
                     Let _ t _ _ -> [t]
                     LetYield _ t _ _ _ -> [t]
                     Yielded t -> [t]
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
      OpenCon _ ts ws -> concatMap at ts ++ concatMap vt ws
      _ -> getConst (descendA (const (Const [])) (Const . avTypes) (Const . vt) a)
