-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Filling the credit of a uniqueness test in its shared branch (after `JoinArgs`, before
  `ExpandReuse`).

  The test that makes a credit (Lean's `reset`) leaves it empty in the shared branch. `DropSpec`
  makes the test the scope of a join point that takes the credit (besides the parts that it
  passes on, and the credits that `Reuse` adds):

    join j(ȳ,r : ◇n[k; z.contents : V]) = e
    if-unique z then (..; jump j(v̄,r')) else (..; jump j(w̄,no-reuse n [k; z.contents : V]))

  and `Reuse` binds it by a `let` (`dropReuse`):

    let r : ◇n[k; z.contents : V] = if-unique z then (let @ r' = z in ..; ret r')
                                    else (drop z; ret no-reuse n [k; z.contents : V]) in e

  The credit is the one that describes the contents of `z`. If every path of `e` allocates in
  it (`consumed`), the shared branch fills it with a copy of the block of `z` (`[copy-ru]`)
  instead, so that it is full on both paths:

    join j(ȳ,r : ◆n[k; z.contents : V]) = e
    if-unique z then (..; jump j(v̄,r')) else (let @copy c = z in ..; jump j(w̄,c))

  `ExpandReuse` then tests nothing, and `e` exists once, where Lean copies it into both
  branches (`ExpandResetReuse`). As the copy has the description of the block, code generation
  stores only the fields that change on both paths. The shared path pays for this:

  - the allocation moves before the calls of `e` (`map` without TRMC, for example, allocates
    on the way down);
  - the copy writes the fields that `e` then overwrites;
  - a cold path on which an effect yields may free the block that it just allocated.
-}
module Backend.Typed.Passes.FillCredits( fillCreditsProgram ) where

import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Monoid( Any(..), All(..) )
import Control.Monad.State
import Backend.Typed.Syntax
import Backend.Typed.Traversal( child, descendA, descendAll, descendE, descendV, fvE, fvV )
import Backend.Typed.Passes.Common( NameSupply, freshFor, freshPathFrom, substJump, yieldingAlts )

type C a = State NameSupply a

fillCreditsProgram :: Program -> Program
fillCreditsProgram prog
  = prog{ progDefs = [d{ defBody = evalState (fillE (defBody d)) (freshFor d) } | d <- progDefs prog] }

fillE :: VExpr -> C VExpr
fillE expr
  = case expr of
      Join j tvs ps e (IsUnique z u s)
        | ((i,r,m,n,p):_) <- [(i,r,m,n,p) | (i,(r,m,VReuse MaybeEmpty n p)) <- zip [0 :: Int ..] ps, describes z p]
        , consumed False r e
        -> do c <- state (freshPathFrom "fc")
              let ps' = [if k == i then (r,m,VReuse Full n p) else b | (k,b) <- zip [0..] ps]
                  s' = substJump j (\ts vs -> Jump j ts [if k == i then Var c else v | (k,v) <- zip [0..] vs]) s
              Join j tvs ps' <$> fillE e <*> (IsUnique z <$> fillE u <*> (CopyRu z c <$> fillE s'))
      Let r (VReuse MaybeEmpty n p) (IsUnique z u (Drop z' (Ret (NoReuse _ _)))) e
        | z' == z, describes z p, consumed False r e
        -> do c <- state (freshPathFrom "fc")
              u' <- fillE u
              Let r (VReuse Full n p) (IsUnique z u' (CopyRu z c (Drop z (Ret (Var c))))) <$> fillE e
      _ -> descendAll (\_ -> fillE) expr

-- the description of a credit for the block of `z`
describes :: Path -> Maybe Contents -> Bool
describes z p
  = case p of
      Just (Contents _ (Var x) _) -> x == child z SContents
      _ -> False

-- Lean's `consumed`: every path consumes the credit directly, by an allocation in it or (if
-- `freeing`) a `free`, and not by passing it on to a join point, function or result. Unlike in
-- Lean, a jump to a join point whose body consumes the credit (which it captures) consumes it too,
-- as the body runs at most once, and only by a jump. The paths on which an effect yields may
-- always free it.
consumed :: Bool -> Path -> VExpr -> Bool
consumed = go S.empty
  where
    -- `js`: the join points in scope whose bodies consume the credit
    go js freeing r expr
      = case expr of
          _ | Just (e,ey) <- yieldingAlts expr -> go js freeing r e && go js True r ey
          Free r' e -> if r' == r then freeing else go js freeing r e
          Let _ _ e1 e2 | isStatement e1 -> if mentions e1 then direct e1 else go js freeing r e2
                        | otherwise -> not (mentions e1) && go js freeing r e2
          Join k _ _ e1 e2 | mentions e1 -> go js freeing r e1 && go (S.insert k js) freeing r e2
                           | otherwise -> go js freeing r e2
          IfFull r' _ _ | r' == r -> False
          Jump k _ vs | S.member k js -> not (any (varIn r) vs)
          _ | isStatement expr -> direct expr
          _ -> getAll (getConst (descendE (const (Const (All True))) (\v -> Const (All (not (S.member r (fvV v)))))
                                         (\_ e -> Const (All (go js freeing r e))) expr))
      where
        mentions e = S.member r (fvE e)
        direct stmt = let vs = statementValues stmt
                      in any (boxesIn r) vs && not (any (varIn r) vs)

isStatement :: VExpr -> Bool
isStatement e
  = case e of
      Ret _ -> True
      Call{} -> True
      App{} -> True
      Jump{} -> True
      _ -> False

statementValues :: VExpr -> [VVal]
statementValues = getConst . descendE (const (Const [])) (Const . pure) (\_ _ -> Const [])

-- whether a value allocates in the credit
boxesIn :: Path -> VVal -> Bool
boxesIn r = getAny . getConst . descendV (Const . Any . boxesInA) (Const . Any . boxesIn r)
  where
    boxesInA a = case a of
                   BoxAt r' v -> r' == r || boxesIn r v
                   _ -> getAny (getConst (descendA (const (Const (Any False))) (Const . Any . boxesInA) (Const . Any . boxesIn r) a))

-- whether a value uses the credit as a value (and not by allocating in it)
varIn :: Path -> VVal -> Bool
varIn r v = case v of
              Var x -> x == r
              _ -> getAny (getConst (descendV (Const . Any . varInA) (Const . Any . varIn r) v))
  where
    varInA a = getAny (getConst (descendA (const (Const (Any False))) (Const . Any . varInA) (Const . Any . varIn r) a))
