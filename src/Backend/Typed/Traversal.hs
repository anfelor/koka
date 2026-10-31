-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- One-level traversals and path operations for the typed IR.
module Backend.Typed.Traversal where

import Data.Functor.Identity( Identity(..) )
import Data.List( isPrefixOf )
import Data.Maybe( isJust )
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

-- the operands and subexpressions of an expression, with the variables bound in each subexpression
descendE :: Applicative f => (Path -> f Path) -> (VVal -> f VVal) -> ([Path] -> VExpr -> f VExpr) -> VExpr -> f VExpr
descendE fn fv fe = descendB fn fv (\bs e -> let xs = map fst bs in (,) xs <$> fe xs e)

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
      Join j tvs ps e1 e2   -> (\(xs,e1') e2' -> Join j tvs [(x',m,t) | (x',(_,m,t)) <- zip xs ps] e1' e2')
                                 <$> fb [(x,[]) | (x,_,_) <- ps] e1 <*> plain e2
      Jump j ts vs          -> Jump j ts <$> traverse fv vs
  where
    plain e = snd <$> fb [] e
    one x s e = (\(xs,e') -> (single xs,e')) <$> fb [(x,s)] e
    single xs = case xs of
                  [x] -> x
                  _   -> error "Backend.Typed.Common.descendB: expecting one binder"

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
      _ -> error ("Backend.Typed.Common.injAStep: the binder " ++ show (Path x ss) ++ " is not an alternative")

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

-- the variables on the path to a variable, from its root
prefixes :: Path -> [Path]
prefixes (Path x ss) = [Path x (take k ss) | k <- [0 .. length ss - 1]]

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
