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

  Recursive join points are left unchanged, as they cannot capture variables.
-}
module Backend.Typed.Passes.JoinArgs( joinArgsProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List( transpose )
import Data.Functor.Const( Const(..) )
import Backend.Typed.Syntax
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
      -- a recursive join point is closed
      Join rc@Rec{} j tvs ps e1 e2
        -> Join rc j tvs ps (jaE decl (scopeOf [x | (x,_,_) <- ps]) e1) (jaE decl scope e2)
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
               sub = M.fromList [(x,Var y) | ((x,_,_),Just y) <- zip ps ys]
               kept :: [a] -> [a]
               kept vs = [v | (v,Nothing) <- zip vs ys]
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
               ps' = kept (zipWith describe ps args)
               join = Join NonRec j tvs ps' (substEIn (M.union (scopeOf [x | (x,_,_) <- ps']) scope') (valueAt sub) e1') (substJump j (\ts -> Jump j ts . kept) e2')
           in foldr (\(y,p,i) -> Proj Borrowed (Var p) i y) join hoisted
      _ -> mapAll (\xs -> jaE decl (bindScope expr xs scope)) expr

-- the variable and field of each borrowed `[proj]` that binds `y`
readsOf :: Path -> VExpr -> [(Path,Int)]
readsOf y expr = here ++ getConst (descendAll (\_ e -> Const (readsOf y e)) expr)
  where
    here = case expr of
             Proj Borrowed (Var p) i x _ | x == y -> [(p,i)]
             _ -> []

-- remove the `[proj]`s that bind the variables `ys`
unread :: S.Set Path -> VExpr -> VExpr
unread ys expr
  = case expr of
      Proj _ _ _ x e | S.member x ys -> unread ys e
      _ -> mapAll (\_ -> unread ys) expr
