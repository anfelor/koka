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
  every jump then passes the same one. (`[unbox-ru]` renames the contents of a box, so a jump
  after it may pass a variable that is not in scope at the join point.)

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
      Join NonRec j tvs ps e1 e2
        -> let e1' = jaE decl (M.union (scopeOf [x | (x,_,_) <- ps]) scope) e1
               e2' = jaE decl scope e2
               bound = S.fromList (bindersE e1' ++ bindersE e2')
               args = transpose (jumpArgs j e2') ++ repeat []
               -- for each parameter, the variable that every jump passes to it
               invariant (_,Owned,_) vs@(Var y : _) | all (== Var y) vs, M.member y scope, S.notMember y bound = Just y
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
               inScope (Contents _ v _) = all (`M.member` scope) (fvV v)
               ps' = kept (zipWith describe ps args)
           in Join NonRec j tvs ps' (substEIn (M.union (scopeOf [x | (x,_,_) <- ps']) scope) (valueAt sub) e1') (substJump j (\ts -> Jump j ts . kept) e2')
      _ -> mapAll (\xs -> jaE decl (bindScope expr xs scope)) expr
