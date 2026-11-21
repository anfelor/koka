-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- A-normal form (after `Contify`).

  Nested lets are reassociated. Roots are unique throughout a definition, so moving a let
  out of its bound computation cannot capture a variable in its continuation. A test for a
  yield keeps its shape (see `Yields`): a let is not moved into or out of the bound
  computation of a result that may yield.

  A let whose bound computation has several tail positions becomes a join point for its
  continuation (a commuting conversion, as in case-of-case):

    let x = case v of { injᵢ y -> eᵢ } in e   ~>   join j(x, z̄) = e in case v of { injᵢ y -> eᵢ' }

  where each tail `ret w` of eᵢ becomes `jump j(w, z̄)`, and any other tail `t` becomes
  `let x' = t in jump j(x', z̄)`. Jumps to the join points of the bound computation stay, as
  their bodies are converted. As Perceus expects closed join points, the free variables z̄ of
  the continuation are passed as owned parameters (like `Contify`), also through the join
  points of the bound computation, and the conversion is skipped if one of them is a boxed
  operand. It is also skipped if x or a captured variable is a context, which may need to
  be unique, or if x may be the dummy of a yield.

  This runs after `Contify`, as converting the calls of a closure in the tail positions
  would prevent its contification. `Simplify` then inlines the joins with a single jump, and
  replaces the jumps with a known argument by the alternative of the join body.
-}
module Backend.Typed.Passes.Anf( anfProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Maybe( fromMaybe )
import Data.Monoid( Sum(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Traversal( descendE, fvE, subexprs, within )
import Backend.Typed.Passes.Common( defGamma, descendTyped, lamsTyped, NameSupply, freshFor, freshNameFrom, perBody, renameE, substJump )
import Backend.Typed.Env( Env, envOf, M, evalM, state )
import Backend.Typed.Query( Gamma )
import Backend.Typed.Types( yields )

type P a = M () NameSupply a

fresh :: String -> P Name
fresh s = state (freshNameFrom s)

anfProgram :: Program -> (Program,[String])
anfProgram prog = perBody (\d -> evalM (anfE (envOf prog) (defGamma d) (defBody d)) () (freshFor d)) prog

anfE :: Env -> Gamma -> VExpr -> P VExpr
anfE env g expr
  = do expr' <- descendTyped env g (lamsTyped g (anfE env)) (anfE env) expr
       case expr' of
         Let x t e1 e2 -> bind g x t e1 e2
         _ -> return expr'

bind :: Gamma -> Path -> VType -> VExpr -> VExpr -> P VExpr
bind g x t (Let y s e1 e2) body | not (yields t || yields s) = Let y s e1 <$> bind g x t e2 body
bind g x t e body
  | tailCount e > 1, joinable t, Just zs <- mapM unboxed captures, all (joinable . snd) zs
  = do j <- fresh "join"
       (qs,body') <- closeOver zs body
       e' <- toJumps j t zs e
       return (Join j [] ((x,Owned,t) : qs) body' e')
  | otherwise = return (Let x t e body)
  where
    captures = filter (\y -> not (y `within` x)) (S.toList (fvE body))
    unboxed y = case M.lookup y g of
                  Just (V v) -> Just (y,v)
                  _ -> Nothing
    joinable s = case s of
                   VCtx{} -> False
                   _ -> not (yields s)

-- Replace each tail position of an expression by a jump to `j` that passes its result and
-- the captures `zs`. The join points of the expression are closed, so they take the captures
-- as parameters too.
toJumps :: Name -> VType -> [(Path,VType)] -> VExpr -> P VExpr
toJumps j t zs expr
  = case expr of
      Join k tvs ps body scope
        -> do (qs,body') <- closeOver zs =<< toJumps j t zs body
              scope' <- toJumps j t zs (substJump k (\ts vs -> Jump k ts (vs ++ captured)) scope)
              return (Join k tvs (ps ++ qs) body' scope')
      _ -> fromMaybe (tailJump expr) (descendTails (toJumps j t zs) expr)
  where
    captured = map (Var . fst) zs
    jump v = Jump j [] (v : captured)
    tailJump e = case e of
                   Ret v -> return (jump v)
                   _ -> do y <- root <$> fresh "res"
                           return (Let y t e (jump (Var y)))

-- Owned parameters for the captures `zs` of the body of a join point, renamed in the body.
closeOver :: [(Path,VType)] -> VExpr -> P ([(Path,Mode,VType)],VExpr)
closeOver zs body
  = do qs <- mapM (const (root <$> fresh "capture")) zs
       return ([(q,Owned,s) | (q,(_,s)) <- zip qs zs], renameE (M.fromList (zip (map fst zs) qs)) body)

-- One layer of the tail positions of an expression, or `Nothing` if it is a tail itself. A
-- jump has none, and a lambda, `gen` and a recursive join point are tails. So is a test for a
-- yield: the continuation cannot know its outcome, and `Yields` removes the test of a call
-- whose result is only reboxed in the bound expression of a let.
descendTails :: Applicative f => (VExpr -> f VExpr) -> VExpr -> Maybe (f VExpr)
descendTails go expr
  = case expr of
      Let x t e1 e2 -> Just (Let x t e1 <$> go e2)
      IfYielding{} -> Nothing
      Jump{} -> Just (pure expr)
      Gen{} -> Nothing
      CastEv{} -> Nothing
      Total{} -> Nothing
      JoinRec{} -> Nothing
      _ | null (subexprs expr) -> Nothing
        | otherwise -> Just (descendE pure pure (\_ e -> go e) expr)

tailCount :: VExpr -> Int
tailCount e = maybe 1 (getSum . getConst) (descendTails (Const . Sum . tailCount) e)
