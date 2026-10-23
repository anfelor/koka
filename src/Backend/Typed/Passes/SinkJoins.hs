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

    join j(x) = e1 in case^ z of { injᵢ y -> ... jump j(y) ... jump j(y) ...; ... }

  becomes

    case^ z of { injᵢ y -> join j(x) = e1 in ... jump j(y) ... jump j(y) ...; ... }

  so that `JoinArgs` can make the invariant argument `y` a capture (and a credit keeps its
  description in the join body).

  The join body is closed except for the variables that `JoinArgs` captures, which it
  introduces last. It stays outside the binders of its free variables and outside a join
  that it jumps to or that shadows it.
-}
module Backend.Typed.Passes.SinkJoins( sinkJoinsProgram ) where

import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common

sinkJoinsProgram :: Program -> Program
sinkJoinsProgram prog = prog{ progDefs = [d{ defBody = sjE (defBody d) } | d <- progDefs prog] }

sjE :: VExpr -> VExpr
sjE expr
  = case expr of
      Join j tvs ps e1 e2 -> sink j tvs ps (sjE e1) (sjE e2)
      _ -> runIdentity (descendE Identity (Identity . sjV) (\_ e -> Identity (sjE e)) expr)

-- define `join j(ps) = e1` in the innermost subexpression of `e` that contains every jump to it
sink :: Name -> [TVar] -> [(Path,Mode,VType)] -> VExpr -> VExpr -> VExpr
sink j tvs ps e1 e
  = case getConst (descendE (const (Const [])) (const (Const [])) (\xs sub -> Const [xs | jumpsIn sub]) e) of
      [xs] | movable, all (`S.notMember` free) xs
        -> runIdentity (descendE Identity Identity (\_ sub -> Identity (if jumpsIn sub then sink j tvs ps e1 sub else sub)) e)
      _ -> Join j tvs ps e1 e
  where
    jumpsIn sub = not (null (jumpArgs j sub))
    free = fvE e1 `S.difference` S.fromList [x | (x,_,_) <- ps]
    movable = case e of
                Join k _ _ _ _ -> k /= j && null (jumpArgs k e1)
                _ -> True

sjV :: VVal -> VVal
sjV = mapV sjA sjV

sjA :: AVal -> AVal
sjA val
  = case val of
      Lam ps r e -> Lam ps r (sjE e)
      _          -> mapA id sjA sjV val
