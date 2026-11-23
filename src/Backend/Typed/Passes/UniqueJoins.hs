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

    join rec j(acc : ctx) = ... let a = acc ++ ctx K in jump j(a) ... let c = ctx-copy acc in c[v]
    in jump j(c₀)
    ~> join rec j(acc :! ctx) = ... let a = acc ++ ctx K in jump j(a) ... acc[v]
       in let c₁ = ctx-copy c₀ in jump j(c₁)

  The candidates are the owned or unique parameters of join points and the binders of `let`
  (`[let-unique]`) of context type, and the unique parameters of the definition. A candidate is excluded if a borrowed use may demote it: `dup x`, a borrowed
  argument of a call or jump, or a capture of a recursive join point (which is borrowed). So is
  a name that is also bound by another binder, and a parameter of a recursive join point whose
  body has no `ctx-copy` (promoting it would only add a copy at the entry).

  The unique binders U are the greatest set of candidates such that every value that flows
  into one is unique given U (`uniq`, as `CheckLinear.uniqueV`): the arguments of every jump
  to a non-recursive join point, those of the jumps in the body of a recursive one, and the
  results of the bound expression of a `let` (`tails`). A result is a value, an append or a
  copy (which are unique), `null` (the dummy, which never reaches the binder of `[is-null]`),
  or a call to a function with a unique result. The jumps that enter a recursive join point
  can copy a shared argument for a promoted parameter once per loop instead of once per
  iteration. Then `ctx-copy v` of a unique `v` is `v` (`kk_cctx_copy` only copies a shared
  context): `let x = ctx-copy v in e` becomes `e[x := v]`. `CheckLinear` validates the result.

  The body of a closure is a scope of its own, in which the variables it captures are owned.
-}
module Backend.Typed.Passes.UniqueJoins( uniqueJoinsProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( foldM, zipWithM )
import Control.Monad.State( State, evalState, state )
import Data.Functor.Const( Const(..) )
import Lidar.Name( Name )
import Backend.Typed.Syntax
import Backend.Typed.Env( Env, envOf )
import Backend.Typed.Traversal( canonical, descendE, fvE, fvV, jumpArgs, lamsV, subexprs )
import Backend.Typed.Types( inst )
import Backend.Typed.Build( K, compose )
import Backend.Typed.Passes.Common( NameSupply, freshFor, freshPathFrom, paramModes, replaceE, resultMode, substJumpM )

uniqueJoinsProgram :: Program -> Program
uniqueJoinsProgram prog = prog{ progDefs = map def (progDefs prog) }
  where
    env = envOf prog
    def d = d{ defBody = evalState (uniqueScope env (params d) (defBody d)) (freshFor d) }
    params d = case d of
                 DefFun{} -> defArgs d
                 DefVal{} -> []

-- rewrite the body of a definition or closure; names are fresh in the whole definition
uniqueScope :: Env -> [(Path,Mode,VType)] -> VExpr -> State NameSupply VExpr
uniqueScope env ps body
  = do body' <- closures body
       let u = unique env (Facts [x | (x,_,_) <- ps] [x | (x,Unique,t) <- ps, isCtx t] S.empty [] <> facts env M.empty body')
       rewrite u body'
  where
    closures e = descendE pure (lamsV (\qs _ b -> uniqueScope env qs b)) (\_ b -> closures b) e

-- a context, or a context that may be null (whose `[is-null]` binds the context itself)
isCtx :: VType -> Bool
isCtx t = case t of
            VCtx{} -> True
            VOrNull s -> isCtx s
            _ -> False

-- what flows into a binder: a value, the result of a call, a unique context (of `[ctx-append]`
-- or `[ctx-copy]`), or another result
data Flow = FVal VVal | FCall Name | FUnique | FOther

-- the results of an expression, in its tail positions (the bodies of its join points
-- included, and its jumps excluded)
tails :: VExpr -> [Flow]
tails expr
  = case expr of
      Ret v -> [FVal v]
      Call f _ _ -> [FCall f]
      Append{} -> [FUnique]
      CtxCopy{} -> [FUnique]
      Plug{} -> [FOther]
      Memoize{} -> [FOther]
      Jump{} -> []
      Unreachable{} -> []
      Let _ _ _ e -> tails e
      App{} -> [FOther]
      Gen{} -> [FOther]
      CastEv{} -> [FOther]
      Total{} -> [FOther]
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
      Join j _ ps e1 e2
        -> point ps True S.empty (jumpArgs j e2) <> facts env js e1 <> facts env (M.insert j [m | (_,m,_) <- ps] js) e2
      -- the jumps in the bodies iterate, and their captures are borrowed
      JoinRec _ ds e
        -> let js' = M.union (M.fromList [(j,[m | (_,m,_) <- ps]) | JoinDef j _ ps _ <- ds]) js
           in mconcat [point ps (hasCopy body) (fvE body `S.difference` S.fromList [x | (x,_,_) <- ps])
                             (concatMap (jumpArgs j . joinBody) ds) <> facts env js' body
                      | JoinDef j _ ps body <- ds]
              <> facts env js' e
      Let x t e1 _ -> bound x t e1 <> sub
      Dup x _ -> demote [Var x] <> sub
      Call f _ vs -> demote (borrowed (paramModes env f (length vs)) vs)
      Jump j _ vs -> demote (borrowed (M.findWithDefault [] j js) vs)
      _ -> sub
  where
    sub = getConst (descendE (const (Const mempty)) (const (Const mempty)) (\xs e -> Const (Facts xs [] S.empty [] <> facts env js e)) expr)
    -- a join point with the arguments of the jumps that flow into its parameters
    point ps profitable caps iters
      = let xs = [x | (x,_,_) <- ps]
        in Facts xs [x | (x,m,t) <- ps, isCtx t, m == Unique || (m == Owned && profitable)] caps
                 [(x,FVal v) | vs <- iters, (x,v) <- zip xs vs]
    bound x t e1 = Facts [] [x | isCtx t] S.empty [(x,r) | r <- tails e1]
    demote vs = mempty{ fDemoted = S.map canonical (S.unions (map fvV vs)) }
    borrowed ms vs = [v | (Borrowed,v) <- zip ms vs]

-- whether an expression copies a context outside of closures
hasCopy :: VExpr -> Bool
hasCopy CtxCopy{} = True
hasCopy e = any hasCopy (subexprs e)

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
      Var x -> S.member (canonical x) u
      UnitV -> True
      Inj _ _ w -> uniq u w
      Tuple vs -> all (uniq u) vs
      Pack _ _ w -> uniq u w
      Context _ _ -> True
      Some w -> uniq u w
      Null _ -> True
      Up w -> uniq u w
      Down _ w -> uniq u w
      _ -> False

-- a unique result given the unique binders
uniqF :: Env -> S.Set Path -> Flow -> Bool
uniqF env u r
  = case r of
      FVal v -> uniq u v
      FCall f -> resultMode env f == Unique
      FUnique -> True
      FOther -> False

-- promote unique parameters, copy shared arguments at recursive join entries,
-- and remove copies of unique values
rewrite :: S.Set Path -> VExpr -> State NameSupply VExpr
rewrite u expr
  = case expr of
      Join j tvs ps e1 e2 -> Join j tvs (params ps) <$> rewrite u e1 <*> rewrite u e2
      JoinRec t ds e
        -> do ds' <- mapM (\d -> (\b -> d{ joinParams = params (joinParams d), joinBody = b }) <$> rewrite u (joinBody d)) ds
              e' <- rewrite u e
              JoinRec t ds' <$> foldM (\e1 (JoinDef j tvs ps _) -> substJumpM j (entry j tvs ps) e1) e' ds
        where
          entry j tvs ps tys vs = do (ks,vs') <- unzip <$> zipWithM (arg tvs tys) ps vs
                                     return (compose ks (Jump j tys vs'))
          -- the argument of an owned parameter that becomes unique is copied unless it is unique
          arg :: [TVar] -> [AType] -> (Path,Mode,VType) -> VVal -> State NameSupply (K,VVal)
          arg tvs tys (x,m,t) v
            | m == Owned, S.member x u, not (uniq u v)
            = do c <- state (freshPathFrom "copy")
                 return (Let c (inst tvs tys t) (CtxCopy v), Var c)
            | otherwise = return (id,v)
      CtxCopy v | uniq u v -> pure (Ret v)
      Let x _ (CtxCopy v) e | uniq u v -> rewrite u (replaceE (M.singleton x v) e)
      _ -> descendE pure pure (\_ e -> rewrite u e) expr
  where
    params ps = [(x,if S.member x u then Unique else m,t) | (x,m,t) <- ps]
