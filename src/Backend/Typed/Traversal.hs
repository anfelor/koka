-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Traversals, structural queries and path operations for the typed IR.
module Backend.Typed.Traversal where

import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Data.List( isPrefixOf )
import Data.Maybe( isJust )
import Data.Monoid( Sum(..) )
import Common.Name( Name )
import Backend.Typed.Syntax

-- the steps from the scrutinee of a `[case-open]` alternative for `c` to its binders: the
-- fields of the product `v.C` (`[proj]`), or `v.C` itself if there is one field
openSteps :: Name -> [Path] -> [[Step]]
openSteps c [_] = [[SOpen c]]
openSteps c xs = [[SOpen c, projStep i x] | (i,x) <- zip [0..] xs]

-- one-level traversals

-- Names are operands, not values: a traversal must preserve their variable form.
-- Lambda bodies are handled separately from the values directly inside a value.
descendA :: Applicative f => (Path -> f Path) -> (AVal -> f AVal) -> (VVal -> f VVal) -> AVal -> f AVal
descendA fn fa fv val
  = case val of
      InjA i a v     -> InjA i a <$> fa v
      Roll a v       -> Roll a <$> fa v
      InjLazy d a v  -> InjLazy d a <$> fa v
      Box v          -> Box <$> fv v
      Scalar v       -> Scalar <$> fv v
      OpenCon c ts vs -> OpenCon c ts <$> traverse fv vs
      BoxAt r v      -> BoxAt <$> fn r <*> fv v
      Fun _          -> pure val
      UnitA          -> pure val
      Lam _ _ _      -> pure val

descendV :: Applicative f => (AVal -> f AVal) -> (VVal -> f VVal) -> VVal -> f VVal
descendV fa fv val
  = case val of
      Inj i t v      -> Inj i t <$> fv v
      Tuple vs       -> Tuple <$> traverse fv vs
      Ptr a v        -> Ptr a <$> fa v
      Pack t ts v    -> Pack t ts <$> fv v
      TyApp v ts     -> (`TyApp` ts) <$> fv v
      DupV v         -> DupV <$> fv v
      Context b v    -> Context b <$> fv v
      Plug c v       -> Plug <$> fv c <*> fv v
      CtxCopy v      -> CtxCopy <$> fv v
      Append c d     -> Append <$> fv c <*> fv d
      Memoize c d k v -> Memoize <$> fv c <*> pure d <*> pure k <*> fv v
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

-- the bodies of the lambdas in a value (but not in their bodies), with their parameters and
-- result types
lamsV :: Applicative f => ([(Path,Mode,VType)] -> VType -> VExpr -> f VExpr) -> VVal -> f VVal
lamsV f = goV
  where
    goV = descendV goA goV
    goA (Lam ps r e) = Lam ps r <$> f ps r e
    goA a = descendA pure goA goV a

-- the operands and subexpressions of an expression, with the variables bound in each subexpression
descendE :: Applicative f => (Path -> f Path) -> (VVal -> f VVal) -> ([Path] -> VExpr -> f VExpr) -> VExpr -> f VExpr
descendE fn fv fe = descendB fn fv (\bs e -> let xs = map fst bs in (,) xs <$> fe xs e)

-- `descendE` that also applies `fe` to the bodies of the lambdas in the operands, with their
-- parameters
descendAll :: Applicative f => ([Path] -> VExpr -> f VExpr) -> VExpr -> f VExpr
descendAll fe = descendE pure (lamsV (\ps _ -> fe [x | (x,_,_) <- ps])) fe

-- the subexpressions of an expression, in the order of `descendE`
subexprs :: VExpr -> [VExpr]
subexprs = getConst . descendE (const (Const [])) (const (Const [])) (\_ e -> Const [e])

-- Like `descendE`, but each binder comes with its steps from the scrutinee, and `fb` gives new
-- binders for a subexpression. The binders of a `let`, a dup, a join point, the credit of
-- `[unbox-ru]` and `[copy-ru]`, and the cell of `[lock]` have no steps, and neither has that of `[unscalar]`,
-- which copies the contents of a scalar.
descendB :: Applicative f => (Path -> f Path) -> (VVal -> f VVal) -> ([(Path,[Step])] -> VExpr -> f ([Path],VExpr)) -> VExpr -> f VExpr
descendB fn fv fb expr
  = case expr of
      Ret v                 -> Ret <$> fv v
      Let x t e1 e2         -> (\e1' (x',e2') -> Let x' t e1' e2') <$> plain e1 <*> one x [] e2
      LetYield x t e1 e2 e3 -> (\e1' (x',e2') e3' -> LetYield x' t e1' e2' e3') <$> plain e1 <*> one x [] e2 <*> plain e3
      Yielded _             -> pure expr
      Unreachable _         -> pure expr
      Call f ts vs          -> Call f ts <$> traverse fv vs
      App f vs              -> App <$> fn f <*> traverse fv vs
      Proj m v i x e        -> (\v' (x',e') -> Proj m v' i x' e') <$> fv v <*> one x [projStep i x] e
      CaseV m v alts        -> CaseV m <$> fv v <*> traverse (\(i,x,e) -> (\(x',e') -> (i,x',e')) <$> one x [injVStep i x] e) alts
      CaseA m v alts def    -> CaseA m <$> fn v <*> traverse (\(i,x,e) -> (\(x',e') -> (i,x',e')) <$> one x [injAStep i x] e) alts
                                       <*> traverse (\(x,e) -> one x [SRest] e) def
      SplitA m v k (x,e1) (y,e2) -> SplitA m <$> fn v <*> pure k <*> one x [SLo] e1 <*> one y [SHi] e2
      IfWhnf m v (x,e1) (y,e2) -> IfWhnf m <$> fn v <*> one x [SWhnf] e1 <*> one y [SDelay] e2
      Deref m v x e         -> (\v' (x',e') -> Deref m v' x' e') <$> fv v <*> one x [SDeref] e
      Unroll m v x e        -> (\v' (x',e') -> Unroll m v' x' e') <$> fn v <*> one x [SRoll] e
      Unbox m v x e         -> (\v' (x',e') -> Unbox m v' x' e') <$> fn v <*> one x [SContents] e
      Unscalar m v x e      -> (\v' (x',e') -> Unscalar m v' x' e') <$> fn v <*> one x [] e
      Unpack m v tvs x e    -> (\v' (x',e') -> Unpack m v' tvs x' e') <$> fv v <*> one x [SPack] e
      CaseLit v alts def    -> CaseLit <$> fv v <*> traverse (\(l,e) -> (,) l <$> plain e) alts <*> plain def
      CaseOpen m v alts def -> CaseOpen m <$> fn v <*> traverse (\(c,xs,e) -> (\(xs',e') -> (c,xs',e')) <$> fb (zip xs (openSteps c xs)) e) alts
                                          <*> plain def
      Gen tvs e             -> Gen tvs <$> plain e
      Drop x e              -> Drop <$> fn x <*> plain e
      Free r e              -> Free <$> fn r <*> plain e
      Dup x y e             -> (\x' (y',e') -> Dup x' y' e') <$> fn x <*> one y [] e
      IsUnique x e1 e2      -> IsUnique <$> fn x <*> plain e1 <*> plain e2
      IfFull r e1 e2        -> IfFull <$> fn r <*> plain e1 <*> plain e2
      UnboxRu v r e         -> (\v' (r',e') -> UnboxRu v' r' e') <$> fn v <*> one r [] e
      CopyRu v r e          -> (\v' (r',e') -> CopyRu v' r' e') <$> fn v <*> one r [] e
      Lock z c e            -> (\z' (c',e') -> Lock z' c' e') <$> fn z <*> one c [] e
      Join r j tvs ps e1 e2 -> (\(xs,e1') e2' -> Join r j tvs [(x',m,t) | (x',(_,m,t)) <- zip xs ps] e1' e2')
                                 <$> fb [(x,[]) | (x,_,_) <- ps] e1 <*> plain e2
      Jump j ts vs          -> Jump j ts <$> traverse fv vs
  where
    plain e = snd <$> fb [] e
    one x s e = (\(xs,e') -> (single xs,e')) <$> fb [(x,s)] e
    single xs = case xs of
                  [x] -> x
                  _   -> error "Backend.Typed.Traversal.descendB: expecting one binder"

-- the binder at a step from a variable
child :: Path -> Step -> Path
child (Path x ss) s = Path x (ss ++ [s])

-- tag(z): the tag of the block of a box `z`, the alternative of a sum that it was reached
-- through (`[case-a]`), or 1 if it is the only one
boxTag :: Path -> Int
boxTag (Path _ ss)
  = case reverse ss of
      (SInjA i _ : _) -> i
      _ -> 1

-- the step to the alternative i of a `[case]` from its binder x, which names its constructor if
-- it is a path to that alternative (`FromCore.valueAlt`): not if the scrutinee is not a variable
injVStep :: Int -> Path -> Step
injVStep i (Path _ ss)
  = case reverse ss of
      (SInjV _ c : _) -> SInjV i c
      _ -> SInjV i (tagCon i)

-- the step to the field i of a product from its binder x, which names the field if it is a
-- path to that field: not if the scrutinee is not a variable
projStep :: Int -> Path -> Step
projStep i (Path _ ss)
  = case reverse ss of
      (SField _ f : _) -> SField i f
      _ -> SField i (posField i)

-- the step to the alternative i of a `[case-a]` from its binder x, which is a path to that
-- alternative and so names its constructor (`FromCore.boxedAlt`)
injAStep :: Int -> Path -> Step
injAStep i (Path x ss)
  = case reverse ss of
      (SInjA _ c : _) -> SInjA i c
      _ -> error ("Backend.Typed.Traversal.injAStep: the binder " ++ show (Path x ss) ++ " is not an alternative")

-- the other part of the parent of a part of a box
sibling :: Step -> Maybe Step
sibling s
  = case s of
      SContents -> Just SCredit
      SCredit   -> Just SContents
      _         -> Nothing

-- A part without a sibling is all of its parent (in its alternative), so a use of it is a use
-- of the parent. A field of a product has siblings, as products have at least two fields where
-- elaboration generates them (`[proj]`).
canonical :: Path -> Path
canonical (Path x ss) = Path x (reverse (dropWhile (not . hasSibling) (reverse ss)))
  where
    hasSibling s = case s of
                     SField _ _ -> True
                     _ -> isJust (sibling s)

-- `x` is `y` or one of its parts
within :: Path -> Path -> Bool
within (Path x ss) (Path y ts) = x == y && ts `isPrefixOf` ss

-- the steps from a variable to one of its parts
stepsFrom :: Path -> Path -> [Step]
stepsFrom (Path _ ts) (Path _ ss) = drop (length ts) ss

-- The path of a binder with steps (`descendB`) from the scrutinee `scrutVar`; the other
-- binders are roots.
pathOf :: Maybe Path -> [Step] -> Maybe Path
pathOf _ [] = Nothing
pathOf z ss = (\x -> foldl child x ss) <$> z

-- the fields of a product variable (`[proj]`), named by their paths
fieldsAt :: Path -> VType -> [(Path,Int,VType)]
fieldsAt x t
  = case t of
      VProd fs -> [(child x (SField i f),i,s) | (i,(f,s)) <- zip [0..] fs]
      _ -> []

-- `[unbox-ru]` and `[lock]` of a box `z` take its contents out of its block and bind its
-- block as a new root: the box, the root and the body
takesContents :: VExpr -> Maybe (Path,Path,VExpr)
takesContents expr
  = case expr of
      UnboxRu z r e -> Just (z,r,e)
      Lock z c e -> Just (z,c,e)
      _ -> Nothing

-- the variable that a destructuring form destructures
scrutVar :: VExpr -> Maybe Path
scrutVar expr
  = case expr of
      _ | Just (z,_,_) <- takesContents expr -> Just z
        | Just ds <- destructAOf expr -> Just (dsScrut ds)
        | Just ds <- destructVOf expr, Var z <- dsScrut ds -> Just z
        | otherwise -> Nothing

-- the arguments of each jump to a join point; jumps are never inside values, and an inner
-- join of the same name shadows it (also in its body if it is recursive)
jumpArgs :: Name -> VExpr -> [[VVal]]
jumpArgs j expr
  = case expr of
      Jump k _ vs | k == j -> [vs]
      Join NonRec k _ _ e1 _ | k == j -> jumpArgs j e1
      Join Rec{} k _ _ _ _ | k == j -> []
      _ -> getConst (descendE (const (Const [])) (const (Const [])) (\_ e -> Const (jumpArgs j e)) expr)

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

-- An alternative of a test with two alternatives (`[case]`, `[case-a]` or `[split-a]`), taken
-- against the other one: whether it is the first, both alternatives, and the test with new
-- bodies for them.
data TestSide = TestSide{ sideTest :: VExpr, sideMode :: Mode, sideFirst :: Bool
                        , sideTaken :: (Path,VExpr), sideOther :: (Path,VExpr)
                        , sideRebuild :: VExpr -> VExpr -> VExpr }

testSides :: VExpr -> [TestSide]
testSides expr
  = case expr of
      CaseV m v [(i,x,a),(j,y,b)] -> both m (x,a) (y,b) (\a' b' -> CaseV m v [(i,x,a'),(j,y,b')])
      CaseA m v [(i,x,a),(j,y,b)] Nothing -> both m (x,a) (y,b) (\a' b' -> CaseA m v [(i,x,a'),(j,y,b')] Nothing)
      CaseA m v [(i,x,a)] (Just (y,b)) -> both m (x,a) (y,b) (\a' b' -> CaseA m v [(i,x,a')] (Just (y,b')))
      SplitA m v k (x,a) (y,b) -> both m (x,a) (y,b) (\a' b' -> SplitA m v k (x,a') (y,b'))
      _ -> []
  where
    both m l r build = [TestSide expr m True l r build, TestSide expr m False r l (flip build)]

-- The side of a test whose other alternative is `failure`, which does not use its binder:
-- consecutive tests with one failure form a conjunction.
failingTo :: VExpr -> VExpr -> Maybe TestSide
failingTo failure expr
  = case [s | s <- testSides expr, let (y,other) = sideOther s, other == failure, not (any (`within` y) (fvE other))] of
      (s:_) -> Just s
      [] -> Nothing
