-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Value-source analysis: which variables have the same bits as another.
module Backend.Typed.Sources( Source(..), Sources, sources, sameBits ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Backend.Typed.Syntax
import Backend.Typed.Traversal( descendAll, jumpArgs )

-- Where a variable gets the bits of another variable: a parameter of a join point gets those
-- of its arguments (including those of the jumps in its body if it is recursive).
data Source = Param [VVal]

type Sources = M.Map Path Source

sources :: VExpr -> Sources
sources expr = M.union here (getConst (descendAll (\_ e -> Const (sources e)) expr))
  where
    here = case expr of
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
                            Param vs | not (S.member p seen), Just ys <- mapM (sameOf (S.insert p seen)) vs
                                     , (y:ys') <- filter (/= p) ys, all (== y) ys' -> extend y (drop k ss)
                            _ -> x
          [] -> x
    extend (Path y ts) rest = Path y (ts ++ rest)
    sameOf seen (Var y) = Just (go seen y)
    sameOf _ _ = Nothing
