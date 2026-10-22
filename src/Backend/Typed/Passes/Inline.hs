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
  equal constructor constant. Only fields still in scope are used; enum values carry no
  ownership. Descriptions and the checking rules stay unchanged.

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
import Data.Functor.Identity( Identity(..) )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env, Gamma, envOf, bindAll, inferV, inferVar, altTypes, unboxRuBinds )

-- the structural values bound by lets
type Values = M.Map Path VVal

inlineProgram :: Program -> (Program,[String])
inlineProgram prog
  = let inlined = prog{ progDefs = map inlineDef (progDefs prog) }
        run d = case evalM (reuseE (defBody d)) (envOf inlined,params d,M.empty) () of
                  Right e -> (d{ defBody = e },[])
                  Left err -> (d,[show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs inlined))
    in (inlined{ progDefs = defs },concat errs)
  where
    params DefFun{ defArgs = ps } = M.fromList [(x,V t) | (x,_,t) <- ps]
    params DefVal{} = M.empty

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
      Pair a b -> structural a && structural b
      Inj _ _ w -> structural w
      UnitV -> True
      Lit _ -> True
      _ -> False

valuesE :: VExpr -> (Values,S.Set Path)
valuesE expr = here <> getConst (descendE (const (Const mempty)) (Const . valuesV) (\_ e -> Const (valuesE e)) expr)
  where
    here = case expr of
             Let x _ (Ret v) _ | structural v -> (M.singleton x v,S.empty)
             Deref _ (Var x) _ _ -> (M.empty,S.singleton x)
             Dup x _ _ -> (M.empty,S.singleton x)
             _ -> mempty

valuesV :: VVal -> (Values,S.Set Path)
valuesV = getConst . descendV (Const . valuesA) (Const . valuesV)

valuesA :: AVal -> (Values,S.Set Path)
valuesA val
  = case val of
      Lam _ _ e -> valuesE e
      _ -> getConst (descendA (const (Const mempty)) (Const . valuesA) (Const . valuesV) val)

-- remove the lets of the inlined values, and the forms that use them as a whole
inlineE :: Values -> VExpr -> VExpr
inlineE vals expr
  = case expr of
      Let x _ _ e | M.member x vals -> inlineE vals e
      Proj _ (Var z) ss _ e | Just w@Pair{} <- known vals z, Just _ <- project w ss -> inlineE vals e
      CaseV _ (Var z) alts | Just (Inj i _ _) <- known vals z -> inlineE vals (snd (alts !! i))
      _ -> runIdentity (descendE Identity (Identity . inlineV vals) (\_ e -> Identity (inlineE vals e)) expr)

inlineV :: Values -> VVal -> VVal
inlineV vals = mapV (inlineA vals) (inlineV vals)

inlineA :: Values -> AVal -> AVal
inlineA vals val
  = case val of
      Lam ps r e -> Lam ps r (inlineE vals e)
      _ -> mapA id (inlineA vals) (inlineV vals) val

-- The enum facts are local to a branch, unlike the structural lets above.
type Reuse a = M (Env,Gamma,Values) () a

bindReuse :: [(Path,Ty)] -> Reuse a -> Reuse a
bindReuse bs = local (\(env,g,facts) -> (env,bindAll bs g,facts))

reuseE :: VExpr -> Reuse VExpr
reuseE expr
  | Just ds <- destructAOf expr
  = do (env,g,_) <- ask
       t <- liftE (inferVar g (dsScrut ds))
       tss <- liftE (altTypes env t expr)
       es <- sequence [bindReuse (zip xs ts) (reuseE e) | ((xs,e),ts) <- zip (dsAlts ds) tss]
       return (dsBuild ds (dsMode ds) (dsScrut ds) es)
  | Just ds <- destructVOf expr
  = do (env,g,_) <- ask
       t <- liftE (inferV env g (dsScrut ds))
       tss <- liftE (altTypes env (V t) expr)
       let enumBranch :: Int -> Reuse a -> Reuse a
           enumBranch i = case expr of
             CaseV _ (Var z) _ | enumType t -> local (\(env,g,facts) -> (env,g,M.insert z (Inj i t UnitV) facts))
             _ -> id
       v <- reuseV (dsScrut ds)
       es <- sequence [bindReuse (zip xs ts) (enumBranch i (reuseE e)) | (i,((xs,e),ts)) <- zip [0..] (zip (dsAlts ds) tss)]
       return (dsBuild ds (dsMode ds) v es)
reuseE expr
  = case expr of
      Let x t e1 e2 -> Let x t <$> reuseE e1 <*> bindReuse [(x,V t)] (reuseE e2)
      LetYield x t e1 e2 e3 -> LetYield x t <$> reuseE e1 <*> bindReuse [(x,V t)] (reuseE e2) <*> reuseE e3
      Join j ps e1 e2 -> Join j ps <$> bindReuse [(x,V t) | (x,_,t) <- ps] (reuseE e1) <*> reuseE e2
      UnboxRu z r e -> do (_,g,_) <- ask
                          bs <- liftE (unboxRuBinds g z r)
                          UnboxRu z r <$> bindReuse bs (reuseE e)
      Dup x y e -> do (_,g,_) <- ask
                      t <- liftE (inferVar g x)
                      Dup x y <$> bindReuse [(y,t)] (reuseE e)
      _ -> descendE pure reuseV (\_ -> reuseE) expr

enumType :: VType -> Bool
enumType (VSum ts) = not (null ts) && all (== VUnit) ts
enumType _ = False

reuseV :: VVal -> Reuse VVal
reuseV = descendV reuseA reuseV

reuseA :: AVal -> Reuse AVal
reuseA val
  = case val of
      BoxAt r v -> do (_,g,facts) <- ask
                      v' <- reuseV v
                      t <- liftE (inferVar g r)
                      return (BoxAt r (case t of
                        V (VReuse _ _ (Just (Contents _ old _))) -> restore g facts old v'
                        _ -> v'))
      Lam ps r e -> Lam ps r <$> bindReuse [(x,V t) | (x,_,t) <- ps]
                                  (local (\(env,g,_) -> (env,g,M.empty)) (reuseE e))
      _ -> descendA pure reuseA reuseV val

-- Prefer the old field's variable only where the branch proves it equals the new
-- constant. Description names may be out of scope, and must not become runtime uses.
restore :: Gamma -> Values -> VVal -> VVal -> VVal
restore g facts old new
  | Var x <- old, Just (V t) <- M.lookup x g, enumType t, M.lookup x facts == Just new = Var x
  | Pair a b <- new, Just x <- project old [SFst], Just y <- project old [SSnd]
  = Pair (restore g facts x a) (restore g facts y b)
  | otherwise = new
