-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Copy propagation (before Perceus): `let x = ret y in e` becomes `e[x := y]`.

  Pattern matching binds many aliases (such as the whole scrutinee); an alias that
  is still live keeps the scrutinee alive, so destructuring could not take ownership.
  Roots are unique throughout a definition. Substitution renames descendant paths
  and descriptions too, and reuses destructured children already in scope.

  Before that, join points with at most one jump are inlined: the jump becomes a binding
  of the parameters to the arguments (aliases that copy propagation then removes), and
  instantiates the type parameters. First, a jump whose arguments select an alternative of
  a destructuring at the start of the join body (under dereferences and unrolls) is replaced
  by a copy of that alternative, if it does not use its binder, with the same bindings. With
  the commuting conversions of `Anf`, this is case-of-case: in
  `join j(x) = case x of {...} in ... jump j(inj₁ ()) ...` the jump becomes the first
  alternative.

  Inlining can put a case on a boxed sum `z` in the default of a case on `z`, whose binder
  `z.rest` it would bind again (`substStep` reuses the outer case only if both took the same
  tags). The inner case then scrutinizes `z.rest` instead: it drops the alternatives that
  the outer case took, keeps its default only if a tag remains, and is its default if no
  alternative remains.

  Afterwards, a fresh context that is only appended is inlined: elaboration binds the
  argument of `c ++ ctx K` (Koka's `cctx/(++)`) and copies it as if it may be shared
  but the literal is unique, and appended in place it extends `c` without testing
  whether it is empty (see `genAppend` in `CGen`).

  Finally, a case on a known value (an injection, or a value that the definition binds with
  `let x = ret v`, through the pointers and rolls of `v`), or an `is-null` of a known `some`
  or `null`, is replaced by its alternative if that does not use its binder. An `is-null`
  whose value is unused and whose null branch is `unreachable` goes away: in `std/core/hnd`, a
  dummy may pass with the flag clear (the result of a final yield's continuation, or of a
  closure at a type variable), and only a used value needs the test. Inlining leaves such cases, mostly on constructors without
  fields. The bindings of values, pointers, rolls and globals that are then unused are removed.
-}
module Lidar.Passes.Simplify( simplifyProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State( State, evalState, state )
import Lidar.Syntax
import Lidar.Traversal( child, descendAll, descendE, fvE, fvFrom, fvV, hasRegion, jumpArgs, lamsV, stepsFrom, usedIn, within )
import Lidar.Passes.Common( mapAll, NameSupply, SubstExpr, cloneE, defGamma, defScope, descendTyped, freshFor, freshNameFrom, lamsTyped, perBody, project, renamePath, substJump, substJumpM, substName, substStep, substTypesE, valueAt )
import Lidar.Types( Types(..) )
import Lidar.Env( Env, M, envOf, evalM, liftE )
import Lidar.Query( Gamma, inferVar )

simplifyProgram :: Program -> (Program,[String])
simplifyProgram prog = perBody (simplifyDef (envOf prog)) prog

simplifyDef :: Env -> Def -> Either String VExpr
simplifyDef env def
  = do copied <- evalM (restsE env (defGamma def) (copyE (defScope def) (const Nothing) inlined)) () ()
       return (fst (knownE M.empty (freshE copied)))
  where
    inlined = evalState (inlineE (defBody def)) (freshFor def)

-- join points

inlineE :: VExpr -> State NameSupply VExpr
inlineE expr
  = case expr of
      Join j tvs ps e1 e2
        -> do e1' <- inlineE e1
              let bindArgs body ts vs = let sub = M.fromList (zip tvs ts)
                                        in foldr (\((x,_,t),v) e -> Let x (subst sub t) (Ret v) e) (substTypesE sub body) (zip ps vs)
                  known :: [AType] -> [VVal] -> State NameSupply VExpr
                  known ts vs = case selected (M.fromList (zip [x | (x,_,_) <- ps] vs)) e1' of
                                   Just alt -> cloneE (root <$> state (freshNameFrom "known")) (bindArgs alt ts vs)
                                   Nothing -> return (Jump j ts vs)
              e2' <- substJumpM j known =<< inlineE e2
              return (case length (jumpArgs j e2') of
                        0 -> e2'
                        1 -> substJump j (bindArgs e1') e2'
                        _ -> Join j tvs ps e1' e2')
      _ -> descendAll (const inlineE) expr

-- The alternative of a destructuring (under dereferences and unrolls) that the known values
-- select, if it does not use its binder.
selected :: M.Map Path VVal -> VExpr -> Maybe VExpr
selected known expr
  = case expr of
      Deref v x e -> ifUsed x (Deref v x) <$> selected (shadow [x] known) e
      Unroll v x e -> ifUsed x (Unroll v x) <$> selected (shadow [x] known) e
      _ -> case decided known expr of
             Just (x,e) | not (used x e) -> Just e
             _ -> Nothing

copyE :: SubstExpr
copyE scope sub expr
  = case expr of
      Let x _ (Ret (Var y)) e
        -> let y' = substName sub y
               alias p | p `within` x = project (Var y') (stepsFrom x p)
                       | otherwise = sub p
           in copyE scope alias e
      _ -> inlineApply (substStep copyE scope sub expr)

-- Copy propagation exposes let-bound adapters that elaboration cannot fuse.
-- Inline only an immediate, single call, including one whose result is let-bound, and not a
-- `[total]` region, which may be in token-threaded code here (`Traversal.hasRegion`).
-- Parameter bindings must not capture names in the actual arguments.
inlineApply :: VExpr -> VExpr
inlineApply expr
  = case expr of
      Let f _ (Ret (Ptr _ (Lam ps _ body))) rest | not (hasRegion body)
        -> let apply (Deref (Var x) g (App h vs))
                 | x == f, g == h, length ps == length vs
                 , all (S.notMember f . fvV) vs
                 , all (\(p,_,_) -> all (S.notMember p . fvV) vs) ps
                 = Just (foldr (\((p,_,t),v) e -> Let p t (Ret v) e) body (zip ps vs))
               apply _ = Nothing
           in case rest of
                Let x t call e | S.notMember f (fvE e), Just body' <- apply call
                  -> Let x t body' e
                Let x t (CastEv u s call) e | S.notMember f (fvE e), Just body' <- apply call
                  -> Let x t (CastEv u s body') e
                _ | Just body' <- apply rest -> body'
                _ -> expr
      _ -> expr

-- cases in the default of a case on the same sum

restsE :: Env -> Gamma -> VExpr -> M () () VExpr
restsE env g expr
  = case expr of
      CaseA z alts def
        | let r = child z SRest, M.member r g
        -> restsE env g =<< inRest r z alts def
      _ -> descendTyped env g (lamsTyped g (restsE env)) (restsE env) expr
  where
    -- the case on `z` as a case on its default binder `r` in scope
    inRest r z alts def
      = do t <- liftE (inferVar g r)
           tags <- case t of
                     A (ASum ts) -> return (map fst ts)
                     _ -> fail ("the default of a case is not a boxed sum: " ++ show r)
           let moved y e = let y' = if y `within` z then foldl child r (stepsFrom z y) else y
                           in (y', renamePath y y' e)
               alts' = [(i,y',e') | (i,y,e) <- alts, i `elem` tags, let (y',e') = moved y e]
               left = [i | i <- tags, i `notElem` [j | (j,_,_) <- alts']]
           case (alts',def) of
             ([], Just (d,e)) -> return (renamePath d r e)
             ([], Nothing) -> fail ("a case without alternatives in the default of a case: " ++ show z)
             _ -> return (CaseA r alts' (if null left then Nothing else uncurry moved <$> def))

shadow :: [Path] -> M.Map Path a -> M.Map Path a
shadow xs sub = foldr M.delete sub xs

-- fresh contexts

freshE :: VExpr -> VExpr
freshE expr
  = case expr of
      Let x _ (Ret k@(Context _ _)) e
        | Just e' <- appendFresh x k e -> freshE e'
      _ -> mapAll (const freshE) expr

-- Inline the fresh context `x = k` into an append that follows immediately and is its only
-- use, as `let c = ctx-copy c₀ in let d = ctx-copy x in c ++ d`: the copy of `x` goes away.
appendFresh :: Path -> VVal -> VExpr -> Maybe VExpr
appendFresh x k expr
  = case expr of
      Let d _ (CtxCopy (Var z)) e | z == x, S.notMember x (fvE e) -> appended d e
      Let c t e1@(CtxCopy _) e | S.notMember x (fvE e1) -> Let c t e1 <$> appendFresh x k e
      _ -> Nothing
  where
    appended d e = case e of
                     Let y t e1 e2 | Just e1' <- append d e1, S.notMember d (fvE e2) -> Just (Let y t e1' e2)
                     _ -> append d e
    append d (Append c (Var z)) | z == d, S.notMember d (fvV c) = Just (Append c k)
    append _ _ = Nothing

-- cases of known values

-- The result comes with its free variables, which `knownE` keeps as it rebuilds (`fvFrom`).
knownE :: M.Map Path VVal -> VExpr -> (VExpr, S.Set Path)
knownE known expr
  = case expr of
      Let x t e1 e2
        -> let (e1',fv1) = knownE known e1
               known' = case e1' of
                          Ret v -> M.insert x v (shadow [x] known)
                          _     -> shadow [x] known
               r2@(e2',fv2) = knownE known' e2
           in if isRet e1' && not (usedIn x fv2) then r2 else rebuilt [fv1,fv2] (Let x t e1' e2')
      Deref v x e -> keepIfUsed x (Deref v x) [] (knownE (shadow [x] known) e)
      LetCast v b x e -> keepIfUsed x (LetCast v b x) [] (knownE (shadow [x] known) e)
      LetGlob x g ts e -> keepIfUsed x (LetGlob x g ts) [] (knownE (shadow [x] known) e)
      Unroll v x e -> keepIfUsed x (Unroll v x) [] (knownE (shadow [x] known) e)
      _ | Just (x,e) <- decided known expr -> taken x e
      IsNull v n@Unreachable{} (x,e) -> keepIfUsed x (\e' -> IsNull v n (x,e')) [S.empty] (knownE (shadow [x] known) e)
      _ -> descend
  where
    descend = uncurry rebuilt (descendE pure (lamsV (\ps _ e -> ([], fst (knownE (shadow [y | (y,_,_) <- ps] known) e))))
                                         (\xs e -> let (e',fv) = knownE (shadow xs known) e in ([fv], e')) expr)
    -- the taken alternative, unless it uses its binder
    taken x e = let r@(_,fv) = knownE (shadow [x] known) e
                in if usedIn x fv then descend else r
    isRet (Ret _) = True
    isRet _ = False

-- an expression with its free variables, given those of its subexpressions
rebuilt :: [S.Set Path] -> VExpr -> (VExpr, S.Set Path)
rebuilt fvs e = (e, fvFrom fvs e)

-- `ifUsed` on an expression with its free variables; `wrap` puts it last among subexpressions
-- whose free variables are `fvs`
keepIfUsed :: Path -> (VExpr -> VExpr) -> [S.Set Path] -> (VExpr, S.Set Path) -> (VExpr, S.Set Path)
keepIfUsed x wrap fvs r@(e,fv) = if usedIn x fv then rebuilt (fvs ++ [fv]) (wrap e) else r

-- the alternative of a destructuring of a known value, with its binder
decided :: M.Map Path VVal -> VExpr -> Maybe (Path,VExpr)
decided known expr
  = case expr of
      CaseV v alts
        | Just (Inj i _ _) <- case v of { Var x -> valueAt known x; _ -> Just v }
        -> alt i alts Nothing
      CaseA v alts def
        | Just (InjA i _ _) <- knownAt known v
        -> alt i alts def
      SplitA v k (x,e1) (y,e2)
        | Just (InjA i _ _) <- knownAt known v
        -> Just (if i < k then (x,e1) else (y,e2))
      IfWhnf v (x,e1) (y,e2)
        | Just (InjLazy d _ _) <- knownAt known v
        -> Just (if d == Whnf then (x,e1) else (y,e2))
      IsNull v n (x,e)
        -> case case v of { Var y -> valueAt known y; _ -> Just v } of
             Just (Some _) -> Just (x,e)
             Just (Null _) -> Just (x,n)
             _ -> Nothing
      _ -> Nothing
  where
    alt i alts def = case [(x,e) | (j,x,e) <- alts, j == i] ++ maybe [] pure def of
                       (a:_) -> Just a
                       [] -> Nothing

-- keep a destructuring with the binder `x` around `e` if `e` uses it
ifUsed :: Path -> (VExpr -> VExpr) -> VExpr -> VExpr
ifUsed x wrap e = if used x e then wrap e else e

used :: Path -> VExpr -> Bool
used x e = usedIn x (fvE e)

-- the known boxed value at a path that passes through a pointer of a known value
knownAt :: M.Map Path VVal -> Path -> Maybe AVal
knownAt known (Path x ss)
  = case [a | k <- [length ss, length ss - 1 .. 0], Just v <- [M.lookup (Path x (take k ss)) known], Just a <- [inside v (drop k ss)]] of
      (a:_) -> Just a
      [] -> Nothing
  where
    inside v steps = case break (== SDeref) steps of
                       (vs,SDeref:as) | Just (Ptr _ a) <- project v vs -> insideA a as
                       _ -> Nothing
    insideA a steps
      = case (a,steps) of
          (_,[]) -> Just a
          (Roll _ b, SRoll:as) -> insideA b as
          (InjA i _ _, SInjA j _:as) | i == j -> insideA a as
          (InjA _ _ _, s:as) | s `elem` [SRest,SLo,SHi] -> insideA a as
          (InjLazy Whnf _ b, SWhnf:as) -> insideA b as
          (InjLazy Delay _ b, SDelay:as) -> insideA b as
          _ -> Nothing
