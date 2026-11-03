-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Shared builders, context and value-source analysis, and lazy metadata for the typed IR.
module Backend.Typed.Common where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Monoid( Sum(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Traversal

-- A continuation that wraps an expression.
type K = VExpr -> VExpr

compose :: [K] -> K
compose = foldr (.) id

-- the name under which the type of the hole is bound in the one-hole value of a context
nameHole :: Path
nameHole = root (newHiddenName "hole")

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

-- Where a variable gets the bits of another variable: a copy (`[dup]`) gets those
-- of its variable, and a parameter of a join point those of its arguments (including those
-- of the jumps in its body if it is recursive).
data Source = Copy Path | Param [VVal]

type Sources = M.Map Path Source

sources :: VExpr -> Sources
sources expr = M.union here (getConst (descendAll (\_ e -> Const (sources e)) expr))
  where
    here = case expr of
             Dup x y _ -> M.singleton y (Copy x)
             Join r j _ ps e1 e2 -> let jumps = jumpArgs j e2 ++ (case r of Rec{} -> jumpArgs j e1; NonRec -> [])
                                    in M.fromList [(y,Param [vs !! i | vs <- jumps]) | (i,(y,_,_)) <- zip [0..] ps]
             _ -> M.empty

-- The variable whose bits a variable has, through the longest prefix of its path that has a
-- source: a join parameter has the bits of its arguments if they are the same. An argument
-- with the bits of the parameter itself (passed back by a recursive jump, possibly through
-- other parameters) does not change them.
sameBits :: Sources -> Path -> Path
sameBits src = go S.empty
  where
    go seen x@(Path r ss)
      = case [(k,s) | k <- [length ss, length ss - 1 .. 0], Just s <- [M.lookup (Path r (take k ss)) src]] of
          ((k,s):_) -> let p = Path r (take k ss)
                       in case s of
                            Copy y -> go seen (extend y (drop k ss))
                            Param vs | not (S.member p seen), Just ys <- mapM (sameOf (S.insert p seen)) vs
                                     , (y:ys') <- filter (/= p) ys, all (== y) ys' -> extend y (drop k ss)
                            _ -> x
          [] -> x
    extend (Path y ts) rest = Path y (ts ++ rest)
    sameOf seen (Var y) = Just (go seen y)
    sameOf _ _ = Nothing

-- The `lazy-C` functions with the tag of their constructor, the size of its cell and its
-- fields (with the padding, see `Elab.TypeInfo.conFieldTypes`), the
-- `lazy-eval-locked` functions, and the tag of the indirection ι of each lazy type.
data Lazies = Lazies{ lzCons :: M.Map Name (Int,Int,[VType]), lzLocked :: S.Set Name
                    , lzIndirect :: M.Map Name Int }

-- the values of the fields of a constructor `fields`, followed by those of its padding
padFields :: [VType] -> [VVal] -> [VVal]
padFields fields vs = vs ++ map zero (drop (length vs) fields)
  where
    zero (VRaw RFloat64) = Lit (LitFloat 0)
    zero _ = Lit (LitChar '\0')

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
