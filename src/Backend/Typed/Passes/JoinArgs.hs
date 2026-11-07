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
  the join body captures that variable instead (`[join]`). A credit then keeps its
  description in the join body, so code generation can omit the stores of unchanged fields
  when it reuses the credit.

  The variable must be in scope at the join point and not be bound in its body or scope:
  every jump then passes the same one. A field that the branches read themselves is first
  brought into scope: elaboration reads a field where it is used, and `Paths` merges the
  reads only within a scope, before `Contify` makes the join point. When every binder of
  the variable in the scope of the join is a borrowed `[proj]` of the same variable in scope
  at the join point, that read moves to just before it. It cannot fail, and the variable it
  reads is live there, as the branches read it.

  A credit that `Reuse` asks for has no description. If the jumps pass different credits
  with the same declared description, or empty ones (which satisfy every description), the
  parameter gets that description, so the join body can still omit the stores: for example,
  the shared continuation of two branches that both took the block of the same box. Its
  names must be in scope at the join point, as substitution does not follow a name out of
  its scope (such as `z.contents` before the `[bunbox]` of `z`); `SinkJoins` moves a join
  into the branch that binds the box.

  A recursive join point can only capture borrowed variables (`[join-rec]`): a borrowed
  parameter becomes a capture when every entry jump passes the same variable and every jump
  in its body passes the parameter itself. The variable must be in scope at the join point
  and not be bound in the body or scope, and its type must not mention the type parameters
  of the join point. It is then borrowed or trivial there, as the jumps in the scope are
  tail calls that lend it.
-}
module Backend.Typed.Passes.JoinArgs( joinArgsProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List( transpose )
import Data.Functor.Const( Const(..) )
import Backend.Typed.Syntax
import Backend.Typed.Types( Types(..) )
import Backend.Typed.Traversal( bindersE, descendAll, fvV, jumpArgs )
import Backend.Typed.Passes.Common( mapAll, Scope, bindScope, defScope, scopeOf, substEIn, substJump, valueAt )

joinArgsProgram :: Program -> Program
joinArgsProgram prog = prog{ progDefs = [d{ defBody = jaE (declared (defBody d)) (defScope d) (defBody d) } | d <- progDefs prog] }

-- the declared descriptions of the credits that join parameters and `let`s bind in a
-- definition (its binders are fresh)
type Declared = M.Map Path (Maybe Contents)

declared :: VExpr -> Declared
declared expr = M.union here (getConst (descendAll (\_ e -> Const (declared e)) expr))
  where
    here = case expr of
             Join _ _ _ ps _ _ -> M.fromList [(x,p) | (x,_,VReuse _ _ p) <- ps]
             Let x (VReuse _ _ p) _ _ -> M.singleton x p
             _ -> M.empty

jaE :: Declared -> Scope -> VExpr -> VExpr
jaE decl scope expr
  = case expr of
      -- a borrowed parameter that the entry jumps pass the same variable to, and the jumps in
      -- the body the parameter itself
      Join rc@Rec{} j tvs ps e1 e2
        -> let e1' = jaE decl (scopeOf [x | (x,_,_) <- ps]) e1
               e2' = jaE decl scope e2
               bound = S.fromList (bindersE e1' ++ bindersE e2')
               entry = transpose (jumpArgs j e2') ++ repeat []
               back = transpose (jumpArgs j e1') ++ repeat []
               invariant (x,Borrowed,t) vs@(Var y : _) ws
                 | all (== Var y) vs, all (== Var x) ws, M.member y scope, S.notMember y bound
                 , all (`notElem` tvs) (ftv t) = Just y
               invariant _ _ _ = Nothing
               ys = zipWith3 invariant ps entry back
               (ps',body) = capture scope ps ys e1'
           in Join rc j tvs ps' (substJump j (\ts -> Jump j ts . kept ys) body) (substJump j (\ts -> Jump j ts . kept ys) e2')
      Join NonRec j tvs ps e1 e0
        -> let e1' = jaE decl (M.union (scopeOf [x | (x,_,_) <- ps]) scope) e1
               e0' = jaE decl scope e0
               args0 = transpose (jumpArgs j e0') ++ repeat []
               -- the reads of fields that every jump passes to an owned parameter
               hoisted = [(y,p,i) | ((_,Owned,_),Var y : vs) <- zip ps args0, all (== Var y) vs, M.notMember y scope
                                  , y `notElem` bindersE e1', rs@((p,i):_) <- [readsOf y e0'], all (== (p,i)) rs
                                  , length rs == length (filter (== y) (bindersE e0')), M.member p scope]
               e2' = unread (S.fromList [y | (y,_,_) <- hoisted]) e0'
               scope' = M.union (scopeOf [y | (y,_,_) <- hoisted]) scope
               bound = S.fromList (bindersE e1' ++ bindersE e2')
               args = transpose (jumpArgs j e2') ++ repeat []
               -- for each parameter, the variable that every jump passes to it
               invariant (_,Owned,_) vs@(Var y : _) | all (== Var y) vs, M.member y scope', S.notMember y bound = Just y
               invariant _ _ = Nothing
               ys = zipWith invariant ps args
               -- the description of every credit that the jumps pass to a credit without one
               describe (x,m,VReuse f n Nothing) vs
                 | (p:qs) <- [descOf v | v <- vs, not (isNoReuse v)], all (== p) qs, Just d <- p, inScope d
                 = (x,m,VReuse f n (Just d))
               describe p _ = p
               descOf v = case v of
                            Var y -> M.findWithDefault Nothing y decl
                            _ -> Nothing
               isNoReuse v = case v of
                               NoReuse _ _ -> True
                               _ -> False
               inScope (Contents _ v _) = all (`M.member` scope') (fvV v)
               (ps',body) = capture scope' (zipWith describe ps args) ys e1'
               join = Join NonRec j tvs ps' body (substJump j (\ts -> Jump j ts . kept ys) e2')
           in foldr (\(y,p,i) -> Proj (Var p) i y) join hoisted
      _ -> mapAll (\xs -> jaE decl (bindScope expr xs scope)) expr

-- the join body captures the variable `y` instead of each parameter with `Just y`, which
-- the parameters no longer contain
capture :: Scope -> [(Path,Mode,VType)] -> [Maybe Path] -> VExpr -> ([(Path,Mode,VType)],VExpr)
capture scope ps ys body
  = (ps', substEIn (M.union (scopeOf [x | (x,_,_) <- ps']) scope) (valueAt sub) body)
  where
    ps' = kept ys ps
    sub = M.fromList [(x,Var y) | ((x,_,_),Just y) <- zip ps ys]

-- the arguments of the parameters that are not captured
kept :: [Maybe Path] -> [a] -> [a]
kept ys vs = [v | (v,Nothing) <- zip vs ys]

-- the variable and field of each borrowed `[proj]` that binds `y`
readsOf :: Path -> VExpr -> [(Path,Int)]
readsOf y expr = here ++ getConst (descendAll (\_ e -> Const (readsOf y e)) expr)
  where
    here = case expr of
             Proj (Var p) i x _ | x == y -> [(p,i)]
             _ -> []

-- remove the `[proj]`s that bind the variables `ys`
unread :: S.Set Path -> VExpr -> VExpr
unread ys expr
  = case expr of
      Proj _ _ x e | S.member x ys -> unread ys e
      _ -> mapAll (\_ -> unread ys) expr
