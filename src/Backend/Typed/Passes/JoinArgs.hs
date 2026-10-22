-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Invariant join arguments (the last pass).

  An owned join parameter that receives the same variable at every jump is removed, and
  the join body captures that variable instead (`[join]`). This removes the copies, and a
  credit keeps its description in the join body, so code generation can omit the stores
  of unchanged fields when it reuses the credit.

  The variable must not be bound in the join point's body or scope: it is then bound
  outside, and every jump passes the same one.
-}
module Backend.Typed.Passes.JoinArgs( joinArgsProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List( transpose )
import Data.Functor.Identity( Identity(..) )
import Backend.Typed.Syntax
import Backend.Typed.Common

joinArgsProgram :: Program -> Program
joinArgsProgram prog = prog{ progDefs = [d{ defBody = jaE (defScope d) (defBody d) } | d <- progDefs prog] }

jaE :: Scope -> VExpr -> VExpr
jaE scope expr
  = case expr of
      Join j ps e1 e2
        -> let e1' = jaE (M.union (scopeOf [x | (x,_,_) <- ps]) scope) e1
               e2' = jaE scope e2
               bound = S.fromList (bindersE e1' ++ bindersE e2')
               -- for each parameter, the variable that every jump passes to it
               invariant (_,Owned,_) vs@(Var y : _) | all (== Var y) vs, S.notMember y bound = Just y
               invariant _ _ = Nothing
               ys = zipWith invariant ps (transpose (jumpArgs j e2') ++ repeat [])
               sub = M.fromList [(x,Var y) | ((x,_,_),Just y) <- zip ps ys]
               kept :: [a] -> [a]
               kept vs = [v | (v,Nothing) <- zip vs ys]
           in Join j (kept ps) (substEIn (M.union (scopeOf [x | (x,_,_) <- kept ps]) scope) (valueAt sub) e1') (substJump j (Jump j . kept) e2')
      _ -> runIdentity (descendE Identity (Identity . jaV scope) (\xs e -> Identity (jaE (bindScope expr xs scope) e)) expr)

jaV :: Scope -> VVal -> VVal
jaV scope = mapV (jaA scope) (jaV scope)

jaA :: Scope -> AVal -> AVal
jaA scope val
  = case val of
      Lam ps r e -> Lam ps r (jaE (M.union (scopeOf [x | (x,_,_) <- ps]) scope) e)
      _          -> mapA id (jaA scope) (jaV scope) val
