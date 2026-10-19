-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Inlining of structural values (the last pass).

  A structural value (variables, pairs, injections, `()` and literals) is rebuilt from its
  parts at no cost, so `let x = ret v` becomes `e[x := v]`, at any type and however often `x`
  is used: a `dup x` duplicates the variables of `v`, and a destructuring of `x` is that of
  `v`, which selects its alternative. A part of `x` is the part of `v` at its steps
  (`valueAt`). A name denotes the same value in the whole definition, so the substitution
  applies everywhere, including the descriptions that name `x` out of its scope.

  Afterwards the payload of a `box@r` names the same values as the description of `r`, so
  code generation compares them syntactically to omit the stores of unchanged fields. It runs
  after `JoinArgs`, so that a captured variable is inlined into the join body as well.

  Existentials are not inlined: unpacking a known `pack` would substitute its types.
-}
module Backend.Typed.Passes.Inline( inlineProgram ) where

import qualified Data.Map as M
import Data.Maybe( fromMaybe )
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Backend.Typed.Syntax
import Backend.Typed.Common

-- the structural values bound by lets
type Values = M.Map Path VVal

inlineProgram :: Program -> Program
inlineProgram prog = prog{ progDefs = map inlineDef (progDefs prog) }

inlineDef :: Def -> Def
inlineDef def
  = case def of
      DefFun{ defArgs = ps } -> def{ defArgs = [(x,m,substVType sub t) | (x,m,t) <- ps], defRes = substVType sub (defRes def), defBody = body }
      DefVal{} -> def{ defType = substVType sub (defType def), defBody = body }
  where
    vals = valuesE (defBody def)
    sub = known vals
    body = substE sub (inlineE vals (defBody def))

-- the value of a variable, in terms of variables that are not inlined
known :: Values -> Path -> Maybe VVal
known vals x = resolve <$> valueAt vals x
  where
    resolve v = case v of
                  Var y -> fromMaybe v (known vals y)
                  _ -> mapV id resolve v

structural :: VVal -> Bool
structural v
  = case v of
      Var _ -> True
      Pair a b -> structural a && structural b
      Inj _ _ w -> structural w
      UnitV -> True
      Lit _ -> True
      _ -> False

-- the variables of a structural value, once for each occurrence
occurrences :: VVal -> [Path]
occurrences v
  = case v of
      Var x -> [x]
      _ -> getConst (descendV (const (Const [])) (Const . occurrences) v)

valuesE :: VExpr -> Values
valuesE expr = here <> getConst (descendE (const (Const M.empty)) (Const . valuesV) (\_ e -> Const (valuesE e)) expr)
  where
    here = case expr of
             Let x _ (Ret v) _ | structural v -> M.singleton x v
             _ -> M.empty

valuesV :: VVal -> Values
valuesV = getConst . descendV (Const . valuesA) (Const . valuesV)

valuesA :: AVal -> Values
valuesA val
  = case val of
      Lam _ _ e -> valuesE e
      _ -> getConst (descendA (const (Const M.empty)) (Const . valuesA) (Const . valuesV) val)

-- remove the lets of the inlined values, and the forms that use them as a whole
inlineE :: Values -> VExpr -> VExpr
inlineE vals expr
  = case expr of
      Let x _ _ e | M.member x vals -> inlineE vals e
      Dup x e | Just w <- known vals x -> foldr Dup (inlineE vals e) (occurrences w)
      Unpair _ (Var z) _ _ e | Just (Pair _ _) <- known vals z -> inlineE vals e
      CaseV _ (Var z) alts | Just (Inj i _ _) <- known vals z -> inlineE vals (snd (alts !! i))
      _ -> runIdentity (descendE Identity (Identity . inlineV vals) (\_ e -> Identity (inlineE vals e)) expr)

inlineV :: Values -> VVal -> VVal
inlineV vals = mapV (inlineA vals) (inlineV vals)

inlineA :: Values -> AVal -> AVal
inlineA vals val
  = case val of
      Lam ps r e -> Lam ps r (inlineE vals e)
      _ -> mapA id (inlineA vals) (inlineV vals) val
