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
-}
module Backend.Typed.Passes.Simplify( simplifyProgram ) where

import qualified Data.Map as M
import Data.Monoid( Sum(..) )
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common

simplifyProgram :: Program -> Program
simplifyProgram prog = prog{ progDefs = map simplifyDef (progDefs prog) }

simplifyDef :: Def -> Def
simplifyDef def = def{ defBody = copyE M.empty (inlineE (defBody def)) }

-- join points

inlineE :: VExpr -> VExpr
inlineE expr
  = case expr of
      Join j ps e1 e2
        -> let e1' = inlineE e1
               e2' = inlineE e2
               bindArgs vs = foldr (\((x,_,t),v) e -> Let x t (Ret v) e) e1' (zip ps vs)
           in case jumpsTo j e2' of
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

-- jumps are never inside values; an inner join of the same name shadows
jumpsTo :: Name -> VExpr -> Int
jumpsTo j expr
  = case expr of
      Jump k _ | k == j -> 1
      Join k _ e1 _ | k == j -> jumpsTo j e1
      _ -> getSum (getConst (descendE (const (Const 0)) (const (Const 0)) (\_ e -> Const (Sum (jumpsTo j e))) expr))

substJump :: Name -> ([VVal] -> VExpr) -> VExpr -> VExpr
substJump j f expr
  = case expr of
      Jump k vs | k == j -> f vs
      Join k ps e1 e2 | k == j -> Join k ps (substJump j f e1) e2
      _ -> runIdentity (descendE Identity Identity (\_ e -> Identity (substJump j f e)) expr)

copyE :: M.Map Name Name -> VExpr -> VExpr
copyE sub expr
  = case expr of
      Let x _ (Ret (Var y)) e
        | let y' = M.findWithDefault y y sub, y' `notElem` bindersE e
        -> copyE (M.insert x y' sub) e
      _ -> runIdentity (descendE (Identity . (\x -> M.findWithDefault x x sub)) (Identity . copyV sub) (\xs e -> Identity (copyE (shadow xs sub) e)) expr)

copyV :: M.Map Name Name -> VVal -> VVal
copyV sub val
  = case val of
      Var x      -> Var (M.findWithDefault x x sub)
      _          -> mapV (copyA sub) (copyV sub) val

copyA :: M.Map Name Name -> AVal -> AVal
copyA sub val
  = case val of
      Lam ps r e -> Lam ps r (copyE (shadow [x | (x,_,_) <- ps] sub) e)
      _ -> mapA (\x -> M.findWithDefault x x sub) (copyA sub) (copyV sub) val

shadow :: [Name] -> M.Map Name Name -> M.Map Name Name
shadow xs sub = foldr M.delete sub xs
