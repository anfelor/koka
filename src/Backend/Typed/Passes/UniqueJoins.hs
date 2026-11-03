-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Unique contexts in join points (right after TailRec).

  A context that is unique can be plugged and appended in place without `ctx-copy`. This
  pass finds the binders of contexts that always hold a unique value, makes the parameters
  among them unique, and removes the copies of unique values:

    join rec j(acc : ctx) = ... jump j(acc ++ ctx K) ... ret (ctx-copy acc)[v] in jump j(c)
    ~> join rec j(acc :! ctx) = ... jump j(acc ++ ctx K) ... ret acc[v] in jump j(ctx-copy c)

  The candidates are the owned or unique parameters of join points and the binders of `let`
  (`[let-unique]`) of context type, and the unique parameters of the definition. A candidate is excluded if a borrowed use may demote it: `dup x`, a borrowed
  argument of a call or jump, or a capture of a recursive join point (which is borrowed). So is
  a name that is also bound by another binder, and a parameter of a recursive join point whose
  body has no `ctx-copy` (promoting it would only add a copy at the entry).

  The unique binders U are the greatest set of candidates such that every value that flows
  into one is unique given U (`uniq`, as `CheckLinear.uniqueV`): the arguments of every jump
  to a non-recursive join point, those of the jumps in the body of a recursive one, and the
  results of the bound expression of a `let` (`tails`). A result is a value, or a call that is
  unique if its function has a unique result, or a worker with one (`UniqueWorkers`) whose
  unique parameters receive unique values; such a call is redirected to the worker. The jumps that enter a recursive join point are exempt: they copy an
  argument for a promoted parameter that is not unique, once per loop instead of once per
  iteration. Then `ctx-copy v` of a unique `v` is `v` (`kk_cctx_copy` only copies a shared
  context). `CheckLinear` validates the result.

  The body of a closure is a scope of its own, in which the variables it captures are owned.
-}
module Backend.Typed.Passes.UniqueJoins( uniqueJoinsProgram, uniqueScope, Flow(..), tails, uniq, uniqF, copyCount, isCtx, workerName ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Data.Monoid( Sum(..) )
import Common.Name( Name, makeHiddenName )
import Backend.Typed.Syntax
import Backend.Typed.Env( Env(..), envOf )
import Backend.Typed.Traversal( descendA, descendE, descendV, fvE, fvV, jumpArgs, lamsV, mapA, mapV )
import Backend.Typed.Passes.Common( paramModes, resultMode, substJump )

uniqueJoinsProgram :: Program -> Program
uniqueJoinsProgram prog = prog{ progDefs = map def (progDefs prog) }
  where
    env = envOf prog
    def d = case d of
              DefFun{} -> d{ defBody = scope env (defArgs d) (defBody d) }
              DefVal{} -> d{ defBody = scope env [] (defBody d) }

-- a definition or closure body with its parameters
scope :: Env -> [(Path,Mode,VType)] -> VExpr -> VExpr
scope env ps body = snd (uniqueScope env ps body)

-- the unique binders of a definition or closure body, and the rewritten body
uniqueScope :: Env -> [(Path,Mode,VType)] -> VExpr -> (S.Set Path, VExpr)
uniqueScope env ps body = (u, rewrite env u body')
  where
    body' = closures body
    u = unique env (Facts [x | (x,_,_) <- ps] [x | (x,Unique,t) <- ps, isCtx t] S.empty [] <> facts env M.empty body')
    closures e = runIdentity (descendE pure (lamsV (\qs _ b -> Identity (scope env qs b))) (\_ b -> Identity (closures b)) e)

isCtx :: VType -> Bool
isCtx t = case t of
            VCtx{} -> True
            _ -> False

-- what flows into a binder: a value, the result of a call, or another result
data Flow = FVal VVal | FCall Name [VVal] | FOther

-- the results of an expression, in its tail positions (the bodies of its join points
-- included, and its jumps excluded)
tails :: VExpr -> [Flow]
tails expr
  = case expr of
      Ret v -> [FVal v]
      Call f _ vs -> [FCall f vs]
      Jump{} -> []
      Unreachable{} -> []
      Let _ _ _ e -> tails e
      LetYield _ _ _ e2 e3 -> tails e2 ++ tails e3
      App{} -> [FOther]
      Gen{} -> [FOther]
      Yielded{} -> [FOther]
      _ -> getConst (descendE (const (Const [])) (const (Const [])) (\_ e -> Const (tails e)) expr)

-- the binders of a scope (with repetitions), the binders among them that are candidates, the
-- variables that may be demoted, and what flows into binders
data Facts = Facts{ fBinders :: [Path], fCands :: [Path], fDemoted :: S.Set Path, fFlows :: [(Path,Flow)] }

instance Semigroup Facts where
  Facts a b c d <> Facts a' b' c' d' = Facts (a ++ a') (b ++ b') (S.union c c') (d ++ d')

instance Monoid Facts where
  mempty = Facts [] [] S.empty []

-- the facts of an expression, with the parameter modes of the join points in scope; the bodies
-- of closures are not part of the scope
facts :: Env -> M.Map Name [Mode] -> VExpr -> Facts
facts env js expr
  = case expr of
      Join r j _ ps e1 e2
        -> let xs = [x | (x,_,_) <- ps]
               js' = M.insert j [m | (_,m,_) <- ps] js
               (body,iters,caps) = case r of
                                     NonRec -> (js, e2, S.empty)
                                     Rec _ -> (js', e1, fvE e1 `S.difference` S.fromList xs)
               cands = [x | (x,m,t) <- ps, isCtx t, m == Unique || (m == Owned && profitable)]
               profitable = case r of
                              NonRec -> True
                              Rec _ -> copyCount e1 > 0
           in Facts xs cands caps [(x,FVal v) | vs <- jumpArgs j iters, (x,v) <- zip xs vs]
              <> facts env body e1 <> facts env js' e2
      Let x t e1 _ -> Facts [] [x | isCtx t] S.empty [(x,r) | r <- tails e1] <> sub
      Dup x _ -> demote [Var x] <> sub
      Call f _ vs -> demote (borrowed (paramModes env f (length vs)) vs)
      Jump j _ vs -> demote (borrowed (M.findWithDefault [] j js) vs)
      _ -> sub
  where
    sub = getConst (descendE (const (Const mempty)) (const (Const mempty)) (\xs e -> Const (Facts xs [] S.empty [] <> facts env js e)) expr)
    demote vs = mempty{ fDemoted = S.unions (map fvV vs) }
    borrowed ms vs = [v | (Borrowed,v) <- zip ms vs]

-- the number of copies of contexts in an expression, outside of closures
copyCount :: VExpr -> Int
copyCount = getSum . go
  where
    go e = getConst (descendE (const (Const mempty)) (Const . copyV) (\_ b -> Const (go b)) e)
    copyV v = case v of
                CtxCopy w -> Sum 1 <> copyV w
                _ -> getConst (descendV (Const . copyA) (Const . copyV) v)
    copyA a = getConst (descendA (const (Const mempty)) (Const . copyA) (Const . copyV) a)

-- the greatest set of candidates that only receive unique values
unique :: Env -> Facts -> S.Set Path
unique env fs = fixpoint (M.keysSet (M.filter id (M.intersectionWith (==) cands bound)) `S.difference` fDemoted fs)
  where
    count xs = M.fromListWith (+) [(x,1::Int) | x <- xs]
    bound = count (fBinders fs)
    cands = count (fCands fs)
    flows = M.fromListWith (++) [(x,[v]) | (x,v) <- fFlows fs]
    fixpoint u = let u' = S.filter (\x -> all (uniqF env u) (M.findWithDefault [] x flows)) u
                 in if u' == u then u else fixpoint u'

-- a unique value given the unique binders (`CheckLinear.uniqueV`)
uniq :: S.Set Path -> VVal -> Bool
uniq u val
  = case val of
      Var x -> S.member x u
      UnitV -> True
      Inj _ _ w -> uniq u w
      Tuple vs -> all (uniq u) vs
      Pack _ _ w -> uniq u w
      Context _ _ -> True
      CtxCopy _ -> True
      Append c d -> uniq u c && uniq u d
      _ -> False

-- a unique result given the unique binders
uniqF :: Env -> S.Set Path -> Flow -> Bool
uniqF env u r
  = case r of
      FVal v -> uniq u v
      FCall f vs -> resultMode env (callee env u f vs) == Unique
      FOther -> False

-- the worker of a function `f` (`UniqueWorkers`)
workerName :: Name -> Name
workerName = makeHiddenName "unique"

-- the function that a call of `f` calls: its worker if the arguments of the worker's unique
-- parameters are unique
callee :: Env -> S.Set Path -> Name -> [VVal] -> Name
callee env u f vs
  = case M.lookup w (envSigs env) of
      Just (SigFun _ ps _ _) | and [uniq u v | ((Unique,_),v) <- zip ps vs] -> w
      _ -> f
  where
    w = workerName f

-- make the unique parameters unique, copy the arguments that are not unique at the entries of
-- recursive join points, remove the copies of unique values, and call workers
rewrite :: Env -> S.Set Path -> VExpr -> VExpr
rewrite env u expr
  = case expr of
      Join r j tvs ps e1 e2
        -> let ps' = [(x,if S.member x u then Unique else m,t) | (x,m,t) <- ps]
               promoted = [S.member x u && m == Owned | (x,m,_) <- ps]
               entry ts vs = Jump j ts [if p && not (uniq u v) then CtxCopy v else v | (p,v) <- zip promoted vs]
               e2' = case r of
                       NonRec -> rewrite env u e2
                       Rec _ -> substJump j entry (rewrite env u e2)
           in Join r j tvs ps' (rewrite env u e1) e2'
      Call f tys vs -> Call (callee env u f vs) tys (map rewriteV vs)
      _ -> runIdentity (descendE pure (Identity . rewriteV) (\_ e -> Identity (rewrite env u e)) expr)
  where
    rewriteV v = case mapV rewriteA rewriteV v of
                   CtxCopy w | uniq u w -> w
                   v' -> v'
    rewriteA = mapA id rewriteA rewriteV
