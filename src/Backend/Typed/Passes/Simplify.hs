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
  and descriptions too, and reuses destructured parts already in scope.

  Before that, join points with at most one jump are inlined: the jump becomes a binding
  of the parameters to the arguments (aliases that copy propagation then removes).

  Afterwards, a fresh context that is only appended is inlined: elaboration binds the
  argument of `c ++ ctx K` (Koka's `cctx/(++)`) and copies it as if it may be shared,
  but the literal is unique, and appended in place it extends `c` without testing
  whether it is empty (see `genAppend` in `CGen`).

  Finally, a boxed case on a known value (one that the definition binds with `let x = ret v`,
  through the pointers and rolls of `v`) is replaced by its alternative if that does not use
  its binder. Inlining leaves such cases, mostly on constructors without fields. The
  bindings of values, pointers and rolls that are then unused are removed.
-}
module Backend.Typed.Passes.Simplify( simplifyProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Identity( Identity(..) )
import Backend.Typed.Syntax
import Backend.Typed.Common

simplifyProgram :: Program -> Program
simplifyProgram prog = prog{ progDefs = map simplifyDef (progDefs prog) }

simplifyDef :: Def -> Def
simplifyDef def = def{ defBody = knownE M.empty (freshE (copyE (defScope def) (const Nothing) (inlineE (defBody def)))) }

-- join points

inlineE :: VExpr -> VExpr
inlineE expr
  = case expr of
      Join j ps e1 e2
        -> let e1' = inlineE e1
               e2' = inlineE e2
               bindArgs vs = foldr (\((x,_,t),v) e -> Let x t (Ret v) e) e1' (zip ps vs)
           in case length (jumpArgs j e2') of
                0 -> e2'
                1 -> substJump j bindArgs e2'
                _ -> Join j ps e1' e2'
      _ -> runIdentity (descendE Identity (Identity . inlineV) (\_ e -> Identity (inlineE e)) expr)

inlineV :: VVal -> VVal
inlineV = mapV inlineA inlineV

inlineA :: AVal -> AVal
inlineA val
  = case val of
      Lam ps r e -> Lam ps r (inlineE e)
      _          -> mapA id inlineA inlineV val

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
-- Inline only an immediate, single call, including one whose result is let-bound.
-- Parameter bindings must not capture names in the actual arguments.
inlineApply :: VExpr -> VExpr
inlineApply expr
  = case expr of
      Let f _ (Ret (Ptr _ (Lam ps _ body))) rest
        -> let apply (Deref Owned (Var x) g (App h vs))
                 | x == f, g == h, length ps == length vs
                 , all (S.notMember f . fvV) vs
                 , all (\(p,_,_) -> all (S.notMember p . fvV) vs) ps
                 = Just (foldr (\((p,_,t),v) e -> Let p t (Ret v) e) body (zip ps vs))
               apply _ = Nothing
           in case rest of
                Let x t call e | S.notMember f (fvE e), Just body' <- apply call
                  -> Let x t body' e
                _ | Just body' <- apply rest -> body'
                _ -> expr
      _ -> expr

shadow :: [Path] -> M.Map Path a -> M.Map Path a
shadow xs sub = foldr M.delete sub xs

-- fresh contexts

freshE :: VExpr -> VExpr
freshE expr
  = case expr of
      Let x t (Ret k@(Context _ _)) e
        | Just e' <- appendFresh x k e -> freshE e'
        | otherwise -> Let x t (Ret (freshV k)) (freshE e)
      _ -> runIdentity (descendE Identity (Identity . freshV) (\_ e -> Identity (freshE e)) expr)

-- inline the fresh context `x = k` into an append that follows immediately and is its only use
appendFresh :: Path -> VVal -> VExpr -> Maybe VExpr
appendFresh x k expr
  = case expr of
      Let y t (Ret v) e | Just v' <- append v, S.notMember x (fvE e) -> Just (Let y t (Ret v') e)
      Ret v | Just v' <- append v -> Just (Ret v')
      _ -> Nothing
  where
    append (Append c (CtxCopy (Var z))) | z == x, S.notMember x (fvV c) = Just (Append c k)
    append _ = Nothing

freshV :: VVal -> VVal
freshV = mapV freshA freshV

freshA :: AVal -> AVal
freshA val
  = case val of
      Lam ps r e -> Lam ps r (freshE e)
      _          -> mapA id freshA freshV val

-- cases of known values

knownE :: M.Map Path VVal -> VExpr -> VExpr
knownE known expr
  = case expr of
      Let x t e1 e2
        -> let e1' = knownE known e1
               known' = case e1' of
                          Ret v -> M.insert x v (shadow [x] known)
                          _     -> shadow [x] known
               e2' = knownE known' e2
           in if isRet e1' && not (used x e2') then e2' else Let x t e1' e2'
      Deref m v x e -> ifUsed x (Deref m v x) (knownE (shadow [x] known) e)
      Unroll m v x e -> ifUsed x (Unroll m v x) (knownE (shadow [x] known) e)
      CaseA _ v alts def
        | Just (InjA i _ _) <- knownAt known v
        , ((x,e):_) <- [(x,e) | (j,x,e) <- alts, j == i] ++ maybe [] pure def
        -> taken x e
      SplitA _ v k (x,e1) (y,e2)
        | Just (InjA i _ _) <- knownAt known v
        -> if i < k then taken x e1 else taken y e2
      _ -> descend
  where
    descend = runIdentity (descendE Identity (Identity . knownV known) (\xs e -> Identity (knownE (shadow xs known) e)) expr)
    -- the taken alternative, unless it uses its binder
    taken x e = let e' = knownE (shadow [x] known) e
                in if used x e' then descend else e'
    isRet (Ret _) = True
    isRet _ = False

-- keep a destructuring with the binder `x` around `e` if `e` uses it
ifUsed :: Path -> (VExpr -> VExpr) -> VExpr -> VExpr
ifUsed x wrap e = if used x e then wrap e else e

used :: Path -> VExpr -> Bool
used x e = any (`within` x) (fvE e)

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
          (InjA i _ _, SInjA j:as) | i == j -> insideA a as
          (InjA _ _ _, s:as) | s `elem` [SRest,SLo,SHi] -> insideA a as
          _ -> Nothing

knownV :: M.Map Path VVal -> VVal -> VVal
knownV known = mapV (knownA known) (knownV known)

knownA :: M.Map Path VVal -> AVal -> AVal
knownA known val
  = case val of
      Lam ps r e -> Lam ps r (knownE (shadow [x | (x,_,_) <- ps] known) e)
      _          -> mapA id (knownA known) (knownV known) val
