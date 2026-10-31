-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Inlining of structural values (the last pass).

  A structural value (variables, pairs, injections, `()` and literals) is rebuilt from its
  parts at no cost, so `let x = ret v` becomes `e[x := v]`, at any type and however often `x`
  is used: a destructuring of `x` is that of `v`, which selects its alternative. A part of `x` is the part of `v` at its steps
  (`valueAt`). A name denotes the same value in the whole definition, so the substitution
  applies everywhere, including the descriptions that name `x` out of its scope.

  Afterwards the payload of a `box@r` names the same values as the description of `r`, so
  code generation compares them syntactically to omit the stores of unchanged fields. It runs
  after `JoinArgs`, so that a captured variable is inlined into the join body as well.

  In an enum alternative, a reused payload can name its old enum field instead of the
  equal constructor constant, or a variable with its bits (`sameBits`), such as a copy of
  it. Only variables still in scope are used; enum values carry no ownership. Descriptions
  and the checking rules stay unchanged.

  Bindings that keep a literal dereference named are retained, preserving its operand
  path without introducing a fresh root, and so are those of values that are duplicated as
  a whole (`[dup]` takes a variable). Existentials are not inlined: unpacking a known
  `pack` would substitute its types.
-}
module Backend.Typed.Passes.Inline( inlineProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe( fromMaybe )
import Data.Functor.Const( Const(..) )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Traversal( descendA, descendAll, descendV, mapV )
import Backend.Typed.Passes.Common( mapAll, defGamma, descendTyped, defScope, perBody, project, substEIn, substVType, valueAt )
import Backend.Typed.Monad
import Backend.Typed.Query( Env, Gamma, envOf, inferVar, lamGamma )

-- the structural values bound by lets
type Values = M.Map Path VVal

inlineProgram :: Program -> (Program,[String])
inlineProgram prog
  = perBody (\d -> evalM (reuseE (defBody d)) (envOf inlined,defGamma d,M.empty,sources (defBody d)) ()) inlined
  where
    inlined = prog{ progDefs = map inlineDef (progDefs prog) }

inlineDef :: Def -> Def
inlineDef def
  = case def of
      DefFun{ defArgs = ps } -> def{ defArgs = [(x,m,substVType sub t) | (x,m,t) <- ps], defRes = substVType sub (defRes def), defBody = body }
      DefVal{} -> def{ defType = substVType sub (defType def), defBody = body }
  where
    (allVals,scruts) = valuesE (defBody def)
    -- Keep a binding if substituting it would turn a variable dereference into
    -- a literal dereference: its operand must remain a path, rather than become
    -- a fresh root. The C compiler can still propagate the literal.
    kept = S.fromList [root n | x@(Path n _) <- S.toList scruts, Just v <- [known allVals x], not (variable v)]
    vals = M.withoutKeys allVals kept
    sub = known vals
    body = substEIn (defScope def) sub (inlineE vals (defBody def))
    variable (Var _) = True
    variable _ = False

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
      Tuple ws -> all structural ws
      Inj _ _ w -> structural w
      UnitV -> True
      Lit _ -> True
      _ -> False

valuesE :: VExpr -> (Values,S.Set Path)
valuesE expr = here <> getConst (descendAll (\_ e -> Const (valuesE e)) expr)
  where
    here = case expr of
             Let x _ (Ret v) _ | structural v -> (M.singleton x v,S.empty)
             Deref _ (Var x) _ _ -> (M.empty,S.singleton x)
             Dup x _ _ -> (M.empty,S.singleton x)
             _ -> mempty

-- remove the lets of the inlined values, and the forms that use them as a whole
inlineE :: Values -> VExpr -> VExpr
inlineE vals expr
  = case expr of
      Let x _ _ e | M.member x vals -> inlineE vals e
      Proj _ (Var z) _ _ e | Just Tuple{} <- known vals z -> inlineE vals e
      CaseV _ (Var z) alts | Just (Inj i _ _) <- known vals z, (e:_) <- [e | (j,_,e) <- alts, j == i] -> inlineE vals e
      _ -> mapAll (\_ -> inlineE vals) expr

-- The enum facts are local to a branch, unlike the structural lets above. The sources of
-- the definition give the variables with the bits of others.
type Reuse a = M (Env,Gamma,Values,Sources) () a

-- In an alternative of a case on an enum, the enum is known.
reuseE :: VExpr -> Reuse VExpr
reuseE expr
  = do (env,g,facts,src) <- ask
       let under g' = local (const (env,g',facts,src)) . reuseE
       case expr of
         CaseV m (Var z) alts | Right (V t) <- inferVar g z, enumType t
           -> CaseV m (Var z) <$> sequence [(,,) i x <$> local (const (env,M.insert x (V VUnit) g,M.insert z (Inj i t UnitV) facts,src)) (reuseE e)
                                           | (i,x,e) <- alts]
         _ -> descendTyped env g reuseV under expr

enumType :: VType -> Bool
enumType (VSum ts) = not (null ts) && all ((== VUnit) . snd) ts
enumType _ = False

reuseV :: VVal -> Reuse VVal
reuseV = descendV reuseA reuseV

reuseA :: AVal -> Reuse AVal
reuseA val
  = case val of
      BoxAt r v -> do (_,g,facts,src) <- ask
                      v' <- reuseV v
                      t <- liftE (inferVar g r)
                      return (BoxAt r (case t of
                        V (VReuse _ _ (Just (Contents _ old _))) -> restore g facts src old v'
                        _ -> v'))
      Lam ps r e -> Lam ps r <$> local (\(env,g,_,src) -> (env,lamGamma ps g,M.empty,src)) (reuseE e)
      _ -> descendA pure reuseA reuseV val

-- Prefer the old field's variable, or one with its bits, only where the branch proves it
-- equals the new constant. Description names may be out of scope, and must not become
-- runtime uses.
restore :: Gamma -> Values -> Sources -> VVal -> VVal -> VVal
restore g facts src old new
  | Var x <- old
  , (y:_) <- [y | y <- x : M.keys facts, y == x || sameBits src y == x, Just (V t) <- [M.lookup y g], enumType t, M.lookup y facts == Just new]
  = Var y
  | Tuple ws <- new, Just xs <- mapM (\i -> project old [SField i (posField i)]) [0 .. length ws - 1]
  = Tuple (zipWith (restore g facts src) xs ws)
  | otherwise = new
