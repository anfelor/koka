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
import Backend.Typed.Types( sumAlts, sumOf )
import Backend.Typed.Traversal

-- A continuation that wraps an expression.
type K = VExpr -> VExpr

compose :: [K] -> K
compose = foldr (.) id

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

-- Where a variable gets the bits of another variable: a copy (`[dup]`) gets those
-- of its variable, and a parameter of a join point those of its arguments.
data Source = Copy Path | Param [VVal]

type Sources = M.Map Path Source

sources :: VExpr -> Sources
sources expr = M.union here (getConst (descendAll (\_ e -> Const (sources e)) expr))
  where
    here = case expr of
             Dup x y _ -> M.singleton y (Copy x)
             Join j _ ps _ e2 -> M.fromList [(y,Param [vs !! i | vs <- jumpArgs j e2]) | (i,(y,_,_)) <- zip [0..] ps]
             _ -> M.empty

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

-- The `lazy-C` functions with the tag of their constructor, the size of its cell and its
-- fields (with the padding, see `Elab.TypeInfo.conFieldTypes`), the
-- `lazy-eval-locked` functions, and the tag of the indirection ι of each lazy type.
data Lazies = Lazies{ lzCons :: M.Map Name (Int,Int,[VType]), lzLocked :: S.Set Name
                    , lzIndirect :: M.Map Name Int }

-- the values of the fields of a constructor `fields`, followed by those of its padding
padFields :: [VType] -> [VVal] -> [VVal]
padFields fields vs = vs ++ [Lit (LitChar '\0') | _ <- drop (length vs) fields]
