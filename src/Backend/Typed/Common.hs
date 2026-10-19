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
import Data.Maybe( fromMaybe )
import Common.Name
import Common.NamePrim( nameTpReuse )
import Backend.Typed.Syntax
import Backend.Typed.Types( Types(..), inst, sumAlts, sumWidth, mapReuseContents )

-- A continuation that wraps an expression.
type K = VExpr -> VExpr

compose :: [K] -> K
compose = foldr (.) id

-- Discard an owned value by destructuring it down to boxed operands and credits.
-- The caller supplies fresh names from its own pass's supply.
dropValue :: Monad m => m Path -> Path -> Ty -> VExpr -> m VExpr
dropValue _ _ t e
  | isTrivial t = return e
dropValue fresh x t e
  = case t of
      A _ -> return (Drop x e)
      V v -> case v of
        VPtr a -> do y <- fresh
                     return (Deref Owned (Var x) y (Drop y e))
        VProd a b -> do y <- fresh
                        z <- fresh
                        rest <- dropValue fresh z (V b) e
                        body <- dropValue fresh y (V a) rest
                        return (Unpair Owned (Var x) y z body)
        VSum ts -> do alts <- mapM dropAlt ts
                      return (CaseV Owned (Var x) alts)
          where
            dropAlt s = do y <- fresh
                           body <- dropValue fresh y (V s) e
                           return (y,body)
        VExists tvs s
          -> do y <- fresh
                u <- fresh
                -- Keep the continuation outside the existential's scope.
                -- Fresh types only need to avoid the payload's free variables.
                let start = minimum (0 : tvs ++ ftv s) - 1
                    bs = take (length tvs) [start,start-1 ..]
                    s' = inst tvs (map AVar bs) s
                body <- dropValue fresh y (V s') (Ret UnitV)
                return (Let u VUnit (Unpack Owned (Var x) bs y body) e)
        VReuse _ _ -> return (Free x e)
        VCtx _ _ -> return (Drop x e)
        VUnit -> return e
        VRaw _ -> return e

-- values of these types need no reference counting
isTrivial :: Ty -> Bool
isTrivial = isTrivialWith (const Nothing)

-- `isTrivial`, where `unroll` gives the body of a named type if it is known (a type with a
-- single constructor without fields, for example)
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
                   VReuse _ _     -> False
                   VCtx _ _     -> False
    trivialA a = case a of
                   AUnit     -> True
                   ASum ts   -> all (trivialA . snd) ts
                   ACon n _  -> n == nameTpReuse || maybe False trivialA (unroll a)
                   ABox _    -> False
                   AFun _ _  -> False
                   AForall _ _ -> False
                   AVar _    -> False
                   AApp _ _  -> False
                   ALam _ _  -> False

-- Boxed sum alternatives must have a tag determined by their construction.
isShape :: AType -> Bool
isShape a = case a of
  AUnit -> True
  ABox _ -> True
  ASum ts -> not (null ts) && all (\(i,t) -> i >= 0 && isShape t) ts
             && and [i + sumWidth t <= j | ((i,t),(j,_)) <- zip ts (drop 1 ts)]
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
  VReuse _ _ -> True
  VCtx _ _ -> False
containsReuse (A a) = case a of
  ABox v -> containsReuse (V v)
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

sumOf :: [AType] -> AType
sumOf [a] = a
sumOf ts = ASum (sumAlts ts)

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
      OpenCon c ts v -> OpenCon c ts <$> fv v
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

-- Like `descendE`, but each binder comes with its step from the scrutinee, and `fb` gives new
-- binders for a subexpression. The binders of a `let` and a join point have no step,
-- and neither has that of `[unbox-lazy]`, which takes the contents out of the box.
descendB :: Applicative f => (Path -> f Path) -> (VVal -> f VVal) -> ([(Path,Maybe Step)] -> VExpr -> f ([Path],VExpr)) -> VExpr -> f VExpr
descendB fn fv fb expr
  = case expr of
      Ret v                 -> Ret <$> fv v
      Let x t e1 e2         -> (\e1' (x',e2') -> Let x' t e1' e2') <$> plain e1 <*> one x Nothing e2
      Call f ts vs          -> Call f ts <$> traverse fv vs
      App f vs              -> App <$> fn f <*> traverse fv vs
      Unpair m v x y e      -> (\v' ((x',y'),e') -> Unpair m v' x' y' e') <$> fv v <*> two (x,SFst) (y,SSnd) e
      CaseV m v alts        -> CaseV m <$> fv v <*> traverse (\(i,(x,e)) -> one x (Just (SInjV i)) e) (zip [0..] alts)
      CaseA m v alts def    -> CaseA m <$> fn v <*> traverse (\(i,x,e) -> (\(x',e') -> (i,x',e')) <$> one x (Just (SInjA i)) e) alts
                                       <*> traverse (\(x,e) -> one x (Just SRest) e) def
      SplitA m v k (x,e1) (y,e2) -> SplitA m <$> fn v <*> pure k <*> one x (Just SLo) e1 <*> one y (Just SHi) e2
      Deref m v x e         -> (\v' (x',e') -> Deref m v' x' e') <$> fv v <*> one x (Just SDeref) e
      Unroll m v x e        -> (\v' (x',e') -> Unroll m v' x' e') <$> fn v <*> one x (Just SRoll) e
      Unbox m v x e         -> (\v' (x',e') -> Unbox m v' x' e') <$> fn v <*> one x (Just SContents) e
      UnboxLazy v x e       -> (\v' (x',e') -> UnboxLazy v' x' e') <$> fn v <*> one x Nothing e
      Unpack m v tvs x e    -> (\v' (x',e') -> Unpack m v' tvs x' e') <$> fv v <*> one x (Just SPack) e
      CaseLit v alts def    -> CaseLit <$> fv v <*> traverse (\(l,e) -> (,) l <$> plain e) alts <*> plain def
      CaseOpen m v alts def -> CaseOpen m <$> fn v <*> traverse (\(c,x,e) -> (\(x',e') -> (c,x',e')) <$> one x (Just (SOpen c)) e) alts
                                          <*> plain def
      Gen tvs e             -> Gen tvs <$> plain e
      Drop x e              -> Drop <$> fn x <*> plain e
      Free r e              -> Free <$> fn r <*> plain e
      Dup x e               -> Dup <$> fn x <*> plain e
      IsUnique x e1 e2      -> IsUnique <$> fn x <*> plain e1 <*> plain e2
      UnboxRu v r e         -> (\v' (r',e') -> UnboxRu v' r' e') <$> fn v <*> one r (Just SCredit) e
      Join j ps e1 e2       -> (\(xs,e1') e2' -> Join j [(x',m,t) | (x',(_,m,t)) <- zip xs ps] e1' e2')
                                 <$> fb [(x,Nothing) | (x,_,_) <- ps] e1 <*> plain e2
      Jump j vs             -> Jump j <$> traverse fv vs
  where
    plain e = snd <$> fb [] e
    one x s e = (\(xs,e') -> (single xs,e')) <$> fb [(x,s)] e
    two (x,s) (y,t) e = (\(xs,e') -> (pair xs,e')) <$> fb [(x,Just s),(y,Just t)] e
    single xs = case xs of
                  [x] -> x
                  _   -> error "Backend.Typed.Common.descendB: expecting one binder"
    pair xs = case xs of
                [x,y] -> (x,y)
                _     -> error "Backend.Typed.Common.descendB: expecting two binders"

-- the binder at a step from a variable
child :: Path -> Step -> Path
child (Path x ss) s = Path x (ss ++ [s])

-- ⌊x⌋: the tag offset of a boxed operand in the sum it was reached through, if it was (the
-- trailing `[case-a]` and `[split-a]` steps of its path)
sumOffset :: Path -> Maybe Int
sumOffset (Path _ ss)
  = case takeWhile inSum (reverse ss) of
      [] -> Nothing
      ts -> Just (sum [i | SInjA i <- ts])
  where
    inSum s = case s of
                SInjA _ -> True
                SRest   -> True
                SLo     -> True
                SHi     -> True
                _       -> False

tagOffset :: Path -> Int
tagOffset = fromMaybe 0 . sumOffset

-- the other part of the parent of a part of a pair or a box
sibling :: Step -> Maybe Step
sibling s
  = case s of
      SFst      -> Just SSnd
      SSnd      -> Just SFst
      SContents -> Just SCredit
      SCredit   -> Just SContents
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

-- substitute the known values (`valueAt`) in a value, but not in its boxed values
substValues :: M.Map Path VVal -> VVal -> VVal
substValues vals val
  = case val of
      Var x -> maybe val id (valueAt vals x)
      _ -> mapV id (substValues vals) val

-- The path of a binder with a step (`descendB`) from the scrutinee `scrutVar`; the other
-- binders are roots.
pathOf :: Maybe Path -> Maybe Step -> Maybe Path
pathOf z s = child <$> z <*> s

-- the arguments of each jump to a join point; jumps are never inside values, and an inner
-- join of the same name shadows it
jumpArgs :: Name -> VExpr -> [[VVal]]
jumpArgs j expr
  = case expr of
      Jump k vs | k == j -> [vs]
      Join k _ e1 _ | k == j -> jumpArgs j e1
      _ -> getConst (descendE (const (Const [])) (const (Const [])) (\_ e -> Const (jumpArgs j e)) expr)

-- replace each jump to a join point
substJump :: Name -> ([VVal] -> VExpr) -> VExpr -> VExpr
substJump j f expr
  = case expr of
      Jump k vs | k == j -> f vs
      Join k ps e1 e2 | k == j -> Join k ps (substJump j f e1) e2
      _ -> runIdentity (descendE Identity Identity (\_ e -> Identity (substJump j f e)) expr)

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
fvE = getConst . descendE (Const . S.singleton) (Const . fvV) (\xs e -> Const (fvE e `S.difference` S.fromList xs))

-- substitution of unboxed values (their free variables must not be bound in the scope).
-- A substitution at a named operand must itself be a variable; use a let for other values.
replaceA :: M.Map Path VVal -> AVal -> AVal
replaceA sub val
  = case val of
      Lam ps r e -> let sub' = foldr M.delete sub [x | (x,_,_) <- ps]
                    in Lam [(x,m,replaceVType sub' t) | (x,m,t) <- ps]
                         (replaceVType sub' r) (replaceE sub' e)
      InjA i a v -> InjA i (replaceAType sub a) (replaceA sub v)
      Roll a v -> Roll (replaceAType sub a) (replaceA sub v)
      OpenCon c ts v -> OpenCon c (map (replaceAType sub) ts) (replaceV sub v)
      _ -> mapA (replaceName sub) (replaceA sub) (replaceV sub) val

replaceV :: M.Map Path VVal -> VVal -> VVal
replaceV sub val
  = case val of
      Var x -> M.findWithDefault val x sub
      Glob x ts -> Glob x (map (replaceAType sub) ts)
      Inj i t v -> Inj i (replaceVType sub t) (replaceV sub v)
      Ptr a v -> Ptr (replaceAType sub a) (replaceA sub v)
      Pack t ts v -> Pack (replaceVType sub t) (map (replaceAType sub) ts) (replaceV sub v)
      TyApp v ts -> TyApp (replaceV sub v) (map (replaceAType sub) ts)
      Context b v -> Context (replaceAType sub b) (replaceV sub v)
      NoReuse n p -> NoReuse n (fmap (replaceContents sub) p)
      _ -> mapV (replaceA sub) (replaceV sub) val

replaceVType :: M.Map Path VVal -> VType -> VType
replaceVType sub = mapReuseContents (fmap (replaceContents sub))

replaceContents :: M.Map Path VVal -> Contents -> Contents
replaceContents sub (Contents k p t) = Contents k (replaceV sub p) (replaceVType sub t)

replaceAType :: M.Map Path VVal -> AType -> AType
replaceAType sub a = case replaceVType sub (VPtr a) of
                      VPtr b -> b
                      _ -> a

replaceName :: M.Map Path VVal -> Path -> Path
replaceName sub x = maybe x varOf (M.lookup x sub)

replaceE :: M.Map Path VVal -> VExpr -> VExpr
replaceE sub expr
  | M.null sub = expr
  | otherwise = runIdentity (descendE (Identity . replaceName sub) (Identity . replaceV sub)
                  (\xs e -> Identity (replaceE (foldr M.delete sub xs) e)) annotated)
  where
    annotated = case expr of
      Let x t e1 e2 -> Let x (replaceVType sub t) e1 e2
      Call f ts vs -> Call f (map (replaceAType sub) ts) vs
      Join j ps e1 e2 -> let sub' = foldr M.delete sub [x | (x,_,_) <- ps]
                        in Join j [(x,m,replaceVType sub' t) | (x,m,t) <- ps] e1 e2
      _ -> expr

-- renaming includes boxed operands as well as unboxed variables
renameA :: M.Map Path Path -> AVal -> AVal
renameA = replaceA . M.map Var

renameV :: M.Map Path Path -> VVal -> VVal
renameV = replaceV . M.map Var

renameE :: M.Map Path Path -> VExpr -> VExpr
renameE = replaceE . M.map Var

-- rename a variable and its parts, also where they are bound
renamePath :: Path -> Path -> VExpr -> VExpr
renamePath x (Path r ss) = goE
  where
    rn p | p `within` x = Path r (ss ++ stepsFrom x p)
         | otherwise = p
    goE = runIdentity . descendB (Identity . rn) (Identity . goV) (\bs e -> Identity (map (rn . fst) bs, goE e))
    goV v = case v of
              Var p -> Var (rn p)
              _ -> mapV goA goV v
    goA a = case a of
              Lam ps t e -> Lam [(rn p,m,s) | (p,m,s) <- ps] t (goE e)
              _ -> mapA rn goA goV a

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
      CaseOpen m v alts def -> Just (Destruct m v ([([x],e) | (_,x,e) <- alts] ++ [([],def)])
                                       (\m' v' es -> CaseOpen m' v' [(c,x,e) | ((c,x,_),e) <- zip alts es] (last es)))
      Unpair{} -> Nothing
      CaseV{} -> Nothing
      Deref{} -> Nothing
      Unpack{} -> Nothing
      Ret{} -> Nothing
      Let{} -> Nothing
      Call{} -> Nothing
      App{} -> Nothing
      CaseLit{} -> Nothing
      Gen{} -> Nothing
      Dup{} -> Nothing
      Drop{} -> Nothing
      Free{} -> Nothing
      IsUnique{} -> Nothing
      UnboxRu{} -> Nothing
      Join{} -> Nothing
      Jump{} -> Nothing

destructVOf :: VExpr -> Maybe (Destruct VVal)
destructVOf expr
  = case expr of
      SplitA{} -> Nothing
      Unpair m v x y e      -> Just (Destruct m v [([x,y],e)] (\m' v' es -> Unpair m' v' x y (head es)))
      CaseV m v alts        -> Just (Destruct m v [([x],e) | (x,e) <- alts] (\m' v' es -> CaseV m' v' (zip (map fst alts) es)))
      Deref m v x e         -> Just (Destruct m v [([x],e)] (\m' v' es -> Deref m' v' x (head es)))
      Unpack m v tvs x e    -> Just (Destruct m v [([x],e)] (\m' v' es -> Unpack m' v' tvs x (head es)))
      CaseA{} -> Nothing
      Unroll{} -> Nothing
      Unbox{} -> Nothing
      UnboxLazy{} -> Nothing
      CaseOpen{} -> Nothing
      Ret{} -> Nothing
      Let{} -> Nothing
      Call{} -> Nothing
      App{} -> Nothing
      CaseLit{} -> Nothing
      Gen{} -> Nothing
      Dup{} -> Nothing
      Drop{} -> Nothing
      Free{} -> Nothing
      IsUnique{} -> Nothing
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
      CaseOpen{}  -> True
      Unpair{}    -> False
      CaseV{}     -> False
      CaseA{}     -> False
      Deref{}     -> False
      Unroll{}    -> False
      Unpack{}    -> False
      Ret{}       -> False
      Let{}       -> False
      Call{}      -> False
      App{}       -> False
      CaseLit{}   -> False
      Gen{}       -> False
      Dup{}       -> False
      Drop{}      -> False
      Free{}      -> False
      IsUnique{}  -> False
      UnboxRu{}   -> False
      Join{}      -> False
      Jump{}      -> False

-- the binders of these destructuring forms are the scrutinee's pointer, so they may be unique
keepsPointer :: VExpr -> Bool
keepsPointer expr
  = case expr of
      SplitA{}    -> True
      CaseA{}     -> True
      Deref{}     -> True
      Unroll{}    -> True
      Unpack{}    -> True
      Unpair{}    -> False
      CaseV{}     -> False
      Unbox{}     -> False
      UnboxLazy{} -> False
      CaseOpen{}  -> False
      Ret{}       -> False
      Let{}       -> False
      Call{}      -> False
      App{}       -> False
      CaseLit{}   -> False
      Gen{}       -> False
      Dup{}       -> False
      Drop{}      -> False
      Free{}      -> False
      IsUnique{}  -> False
      UnboxRu{}   -> False
      Join{}      -> False
      Jump{}      -> False
