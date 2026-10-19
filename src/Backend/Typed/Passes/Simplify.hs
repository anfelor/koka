-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Copy propagation (before Perceus): `let x = ret y in e` becomes `e[x := y]`.

  Pattern matching binds many aliases (such as the whole scrutinee); an alias that
  is still live keeps the scrutinee alive, so destructuring could not take ownership.
  Names can be bound more than once (`Match` duplicates code), so an alias is only
  replaced if its target is not bound again in its scope, and binders shadow aliases.

  Before that, join points with at most one jump are inlined: the jump becomes a binding
  of the parameters to the arguments (aliases that copy propagation then removes).

  Afterwards, a fresh context that is only appended is inlined: elaboration binds the
  argument of `c ++ ctx K` (Koka's `cctx/(++)`) and copies it as if it may be shared,
  but the literal is unique, and appended in place it extends `c` without testing
  whether it is empty (see `genAppend` in `CGen`).
-}
module Backend.Typed.Passes.Simplify( simplifyProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Identity( Identity(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common

simplifyProgram :: Program -> Program
simplifyProgram prog = prog{ progDefs = map simplifyDef (progDefs prog) }

simplifyDef :: Def -> Def
simplifyDef def = def{ defBody = freshE (copyE M.empty (inlineE (defBody def))) }

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

copyE :: M.Map Path Path -> VExpr -> VExpr
copyE sub expr
  = case expr of
      Let x _ (Ret (Var y)) e
        | let y' = M.findWithDefault y y sub, y' `notElem` bindersE e
        -> copyE (M.insert x y' sub) e
      _ -> inlineApply (runIdentity (descendE (Identity . (\x -> M.findWithDefault x x sub)) (Identity . copyV sub) (\xs e -> Identity (copyE (shadow xs sub) e)) expr))

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

copyV :: M.Map Path Path -> VVal -> VVal
copyV sub val
  = case val of
      Var x      -> Var (M.findWithDefault x x sub)
      _          -> mapV (copyA sub) (copyV sub) val

copyA :: M.Map Path Path -> AVal -> AVal
copyA sub val
  = case val of
      Lam ps r e -> Lam ps r (copyE (shadow [x | (x,_,_) <- ps] sub) e)
      _ -> mapA (\x -> M.findWithDefault x x sub) (copyA sub) (copyV sub) val

shadow :: [Path] -> M.Map Path Path -> M.Map Path Path
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
