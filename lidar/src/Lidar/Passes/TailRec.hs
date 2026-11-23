-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Tail calls within a group of functions become loops (right after Perceus).

  A function whose body calls itself in tail position becomes a recursive join point
  (`[join-rec]`) whose parameters are those of the function, with the same modes:

    fun f⟨ā⟩(x̄ :q̄ V̄) : W = e   ~>   fun f⟨ā⟩(ȳ :q̄ V̄) : W = join rec j⟨b̄⟩(x̄ :q̄ V̄) : W = e' in jump j[b̄](ȳ)

  where e' replaces the self tail calls `f[B̄](v̄)` of e by `jump j[B̄ restricted to b̄](v̄)`.
  The join point quantifies over the type parameters b̄ of f that the calls change (for
  polymorphic recursion). These must not occur in W (`[join-rec]` requires b̄ ∉ ftv(W)), so
  a call can only become a jump if it passes the parameters in W unchanged. The others stay
  those of f, so that `JoinArgs` can capture variables whose types mention them. The body
  of the function only has its parameters in scope, so the join point is closed.

  Functions f₁, ..., fₙ (n ≥ 2) that call each other in tail position share a worker, which
  takes the arguments of one of them as an unboxed sum, and whose group of join points has a
  body for each function:

    fun w⟨ā,b̄₁,...,b̄ₙ⟩(s :q ⊕ᵢ ⊗V̄ᵢ) : W
      = join rec : W { j₁⟨c̄₁⟩(x̄₁ :q V̄₁) = e₁'; ...; jₙ⟨c̄ₙ⟩(x̄ₙ :q V̄ₙ) = eₙ' }
        in case s of { injᵢ y -> jump jᵢ[c̄ᵢ](y.field₀, ...) }
    inline fun fᵢ⟨āᵢ,b̄ᵢ⟩(x̄ᵢ :q V̄ᵢ) : Wᵢ = w[āᵢ,any,...,b̄ᵢ,...,any](injᵢ (x̄ᵢ))

  where eᵢ' replaces the tail calls to the functions of the group by jumps, as above. The
  results Wᵢ are W up to a renaming of their type parameters āᵢ to ā, and the other type
  parameters b̄ᵢ of the functions are distinct; the other functions' are `any` in a wrapper.
  All parameters have the same mode q, and the results the same mode and `fip` annotation.
  The bodies are renamed apart, as the names of a definition are unique. The other calls
  to fᵢ stay calls of its wrapper, which is `inline` (even if fᵢ is `noinline`): C generation
  defines it in the header, where the C compiler can inline it into its callers.
-}
module Lidar.Passes.TailRec( tailRecProgram, loopWorkerName ) where

import qualified Data.Map as M
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Data.Graph( SCC(..), stronglyConnComp )
import qualified Data.Set as S
import Data.List( nub, zip4 )
import Control.Monad( zipWithM )
import Control.Monad.State( evalState, state )
import Data.Maybe( fromMaybe, maybeToList )
import Lidar.Name( Name, makeHiddenName )
import Lidar.Syntax
import Lidar.Types( Types(..), atAny, holdsToken, inst, prodV )
import Lidar.Build( prodVal )
import Lidar.Traversal( child, descendE, fieldsAt, jumps )
import Lidar.Passes.Common( NameSupply(..), freshFor, substJump, substTypesE, freshNameFrom, freshPathFrom, mentionedT, renameE, cloneE )

-- the worker of a group of functions, named after its first one
loopWorkerName :: Name -> Name
loopWorkerName = makeHiddenName "loop"

tailRecProgram :: M.Map Name Fip -> Program -> Program
tailRecProgram fips prog
  = prog{ progSigs = M.union (M.fromList [(defName w,sigOf w) | (w,_) <- mutuals]) (progSigs prog)
        , progDefs = concatMap place (progDefs prog) }
  where
    funs = M.fromList [(defName d,d) | d <- progDefs prog, sharesLoops d]
    groups = [ds | CyclicSCC scc@(_:_:_) <- stronglyConnComp [(d,defName d,mutualCalls fips funs d) | d <- M.elems funs]
                 , let ds = [d | d <- progDefs prog, defName d `elem` map defName scc]   -- in program order
                       tvs = concatMap defParams ds
                 , length tvs == length (nub tvs), length (nub [m | d <- ds, (_,m,_) <- defArgs d]) <= 1]
    mutuals = map mutual groups
    workers = M.fromList [(defName (head vs),w) | (w,vs) <- mutuals]
    wrappers = M.fromList [(defName v,v) | (_,vs) <- mutuals, v <- vs]
    place d = maybeToList (M.lookup (defName d) workers) ++ [M.findWithDefault (tailRecDef d) (defName d) wrappers]
    sigOf w = SigFun (defParams w) [(m,t) | (_,m,t) <- defArgs w] (defResMode w) (defRes w)

tailRecDef :: Def -> Def
tailRecDef def
  = case def of
      DefFun{ defName = f, defParams = tvs, defArgs = args, defRes = res, defBody = body }
        | all (\(_,_,t) -> null (mentionedT t)) args     -- the parameters are renamed
        , body0 <- tailJumps (M.singleton f (tvs,cands,j)) body, body0 /= body
        -> let (ys,_) = foldr (\_ (ps,s) -> let (p,s') = freshPathFrom "arg" s in (p:ps,s')) ([],supply') args
               (bs,bodies) = restrict j cands [body0]
           in def{ defArgs = [(y,m,t) | (y,(_,m,t)) <- zip ys args]
                 , defBody = JoinRec res [JoinDef j bs args e | e <- bodies] (Jump j (map AVar bs) (map Var ys)) }
      _ -> def
  where
    (j,supply') = freshNameFrom "loop" (freshFor def)
    -- the type parameters that a loop over the body may quantify over
    cands = others def

-- the type parameters of a function that are not in its result
others :: Def -> [TVar]
others d = [a | a <- defParams d, a `notElem` ftv (defRes d)]

-- restrict the jumps to `j` in the bodies to the candidates `cs` that some jump changes, which
-- the join point quantifies over
restrict :: Name -> [TVar] -> [VExpr] -> ([TVar],[VExpr])
restrict j cs bodies = (bs, map (substJump j (\ts -> Jump j [t | (t,c) <- zip ts cs, c `elem` bs])) bodies)
  where
    bs = [c | (i,c) <- zip [0..] cs, any (\(ts,_) -> ts !! i /= AVar c) (concatMap (jumps j) bodies)]

-- Whether a function can share a worker: its parameters are neither renamed nor tokens.
sharesLoops :: Def -> Bool
sharesLoops d
  = case d of
      DefFun{ defArgs = args } -> all (\(_,_,t) -> null (mentionedT t) && not (holdsToken t)) args
      DefVal{} -> False

-- the functions that a function calls in tail position, if they can share a worker: with the
-- same result up to a renaming of its type parameters, which the call passes unchanged
mutualCalls :: M.Map Name Fip -> M.Map Name Def -> Def -> [Name]
mutualCalls fips funs d
  = nub [g | (g,tys) <- getConst (tailCallsM (\g tys _ -> Const [(g,tys)]) (defBody d))
           , Just e <- [M.lookup g funs], length tys == length (defParams e)
           , M.lookup g fips == M.lookup (defName d) fips, defResMode e == defResMode d
           , Just _ <- [renaming (defRes e) (defRes d)]
           , alphaEq (inst (defParams e) tys (defRes e)) (defRes d)]

-- the renaming of the type variables of `t` that gives `u`
renaming :: VType -> VType -> Maybe (M.Map TVar TVar)
renaming t u
  | length as == length bs, alphaEq (subst (M.fromList (zip as (map AVar bs))) t) u = Just (M.fromList (zip as bs))
  | otherwise = Nothing
  where
    as = nub (ftv t)
    bs = nub (ftv u)

-- the worker of a group of functions, and their wrappers
mutual :: [Def] -> (Def,[Def])
mutual ds
  = (DefFun w tvs [(s,q,sumT)] (defResMode d1) res (JoinRec res points (CaseV (Var s) (zipWith3 enter [0..] js points))) InlineAuto
    , zipWith wrapper [0..] ds)
  where
    d1 = head ds
    res = defRes d1
    w = loopWorkerName (defName d1)
    q = head ([m | d <- ds, (_,m,_) <- defArgs d] ++ [Owned])
    -- the type parameters of the result (those of the first function), then the others
    wtvs = nub (ftv res)
    tvs = wtvs ++ concatMap others ds
    sigmas = [fromMaybe M.empty (renaming (defRes d) res) | d <- ds]
    -- the parameters and bodies with the type parameters of the worker, those after the first
    -- renamed apart
    supply = NameSupply 0 (S.unions [used | d <- ds, let NameSupply _ used = freshFor d])
    (renamed,js,s) = flip evalState supply $
                       (,,) <$> zipWithM apart [0 :: Int ..] (zip ds sigmas)
                            <*> mapM (const (state (freshNameFrom "loop"))) ds
                            <*> state (freshPathFrom "args")
    apart i (d,sigma)
      = do let sub = M.map AVar sigma
               ps = [(x,m,subst sub t) | (x,m,t) <- defArgs d]
               body = substTypesE sub (defBody d)
           if i == 0 then return (ps,body)
           else do ys <- mapM (const fresh) ps
                   body' <- cloneE fresh (renameE (M.fromList [(x,y) | ((x,_,_),y) <- zip ps ys]) body)
                   return ([(y,m,t) | ((_,m,t),y) <- zip ps ys], body')
    fresh = state (freshPathFrom "x")
    -- the type parameters of each function in the worker, and those its join may quantify over
    targets = M.fromList [(defName d,([M.findWithDefault a a sigma | a <- defParams d],others d,j)) | (d,sigma,j) <- zip3 ds sigmas js]
    (css,bodies) = foldr (\(d,j) (cs,bs) -> let (c,bs') = restrict j (others d) bs in (c:cs,bs'))
                         ([],[tailJumps targets body | (_,body) <- renamed]) (zip ds js)
    points = [JoinDef j c ps body | (j,c,(ps,_),body) <- zip4 js css renamed bodies]
    sumT = VSum [(tagCon i,prodV [t | (_,_,t) <- joinParams p]) | (i,p) <- zip [0..] points]
    -- the entry of an alternative: its fields are the arguments
    enter i j p
      = let y = child s (SInjV i (tagCon i))
            jump = Jump j (map AVar (joinTVars p))
        in (i,y,case joinParams p of
                  [] -> jump []
                  [_] -> jump [Var y]
                  ps -> let fields = fieldsAt y (prodV [t | (_,_,t) <- ps])
                        in foldr (\(x,k,_) -> Proj (Var y) k x) (jump [Var x | (x,_,_) <- fields]) fields)
    wrapper i d
      = let inverse = M.fromList [(b,a) | (a,b) <- M.toList (sigmas !! i)]
            tys = [AVar (M.findWithDefault b b inverse) | b <- wtvs]
                  ++ concat [map (if k == i then AVar else const atAny) (others e) | (k,e) <- zip [0 :: Int ..] ds]
        in d{ defBody = Call w tys [Inj i (inst tvs tys sumT) (prodVal [Var x | (x,_,_) <- defArgs d])], defInline = InlineAlways }

-- replace the tail calls to the functions of `points` by jumps to their join points, with the
-- type parameters of the functions in the join and those that the join may quantify over:
-- the calls must pass the others unchanged
tailJumps :: M.Map Name ([TVar],[TVar],Name) -> VExpr -> VExpr
tailJumps points = runIdentity . tailCallsM call
  where
    call g tys vs
      = Identity $ case M.lookup g points of
          Just (tvs,bs,j) | length tys == length tvs, and [ty == AVar a | (a,ty) <- zip tvs tys, a `notElem` bs]
            -> Jump j [ty | (a,ty) <- zip tvs tys, a `elem` bs] vs
          _ -> Call g tys vs

-- apply a function to the calls in tail position
tailCallsM :: Applicative m => (Name -> [AType] -> [VVal] -> m VExpr) -> VExpr -> m VExpr
tailCallsM f = go
  where
    go expr
      = case expr of
          Call g tys vs -> f g tys vs
          -- not in tail position
          Let x t e1 e2 -> Let x t e1 <$> go e2
          Gen _ _ -> pure expr
          CastEv{} -> pure expr
          Total{} -> pure expr
          JoinRec t ds e -> JoinRec t ds <$> go e
          _ -> descendE pure pure (\_ e -> go e) expr
