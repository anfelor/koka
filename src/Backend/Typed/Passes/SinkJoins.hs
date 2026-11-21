-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Join sinking (before `JoinArgs`).

  A join point is moved into a subexpression of its scope as long as that subexpression
  contains all of its jumps. The match compiler defines the join of a guard's fall-through
  after the whole match, outside the branch that binds the variables passed to it:

    join j(x) = e1 in case z of { injᵢ y -> ... jump j(y) ... jump j(y) ...; ... }

  becomes

    case z of { injᵢ y -> join j(x) = e1 in ... jump j(y) ... jump j(y) ...; ... }

  so that `JoinArgs` can make the invariant argument `y` a capture (and a credit keeps its
  description in the join body). A recursive join point is sunk in the same way, so that
  `JoinArgs` can capture a borrowed variable that the branch of its entry jumps binds.

  The join body is closed except for the variables that `JoinArgs` captures, which it
  introduces later. It stays outside the binders of its free variables and outside a join
  that it jumps to or that shadows it.
-}
module Backend.Typed.Passes.SinkJoins( sinkJoinsProgram ) where

import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Passes.Common( mapAll )
import Backend.Typed.Traversal( descendE, fvE, jumpArgs )

sinkJoinsProgram :: Program -> Program
sinkJoinsProgram prog = prog{ progDefs = [d{ defBody = sjE (defBody d) } | d <- progDefs prog] }

sjE :: VExpr -> VExpr
sjE expr
  = case expr of
      Join j tvs ps e1 e2 -> let e1' = sjE e1 in sink [j] (freeIn ps e1') [e1'] (Join j tvs ps e1') (sjE e2)
      JoinRec t ds e -> let ds' = [d{ joinBody = sjE (joinBody d) } | d <- ds]
                        in sink (map joinName ds') (S.unions [freeIn ps e1 | JoinDef _ _ ps e1 <- ds']) (map joinBody ds') (JoinRec t ds') (sjE e)
      _ -> mapAll (const sjE) expr
  where
    freeIn ps e1 = fvE e1 `S.difference` S.fromList [x | (x,_,_) <- ps]

-- define the join points `js` with their free variables and bodies (`point e` defines them
-- around `e`) in the innermost subexpression of `e` that contains every jump to them
sink :: [Name] -> S.Set Path -> [VExpr] -> (VExpr -> VExpr) -> VExpr -> VExpr
sink js free bodies point e
  = case getConst (descendE (const (Const [])) (const (Const [])) (\xs sub -> Const [xs | jumpsIn sub]) e) of
      [xs] | movable, all (`S.notMember` free) xs
        -> runIdentity (descendE Identity Identity (\_ sub -> Identity (if jumpsIn sub then sink js free bodies point sub else sub)) e)
      _ -> point e
  where
    jumpsIn sub = any (\j -> not (null (jumpArgs j sub))) js
    movable = case e of
                Join k _ _ _ _ -> outside [k]
                JoinRec _ ds _ -> outside (map joinName ds)
                _ -> True
    outside ks = all (`notElem` js) ks && and [null (jumpArgs k b) | k <- ks, b <- bodies]
