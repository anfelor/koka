-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Establish path names once, at the Core-to-typed-IR boundary.

  The binder of a destructuring of a variable `z` becomes `z` followed by the step of the
  destructuring form (`descendB`), so that its name says where it comes from. Every other
  binder is a root, and a root name is bound only once in a definition: a root that is bound
  again gets a fresh name. Every subsequent pass preserves these invariants; its
  output is checked directly, without repairing its binders.

  A path denotes one value, so it is bound at most once in a scope (`Check`): a destructuring
  of a variable whose binders in one of its alternatives are already in scope is that
  alternative. The default alternative of `[case-a]` is only that if the default binder in
  scope comes from a `[case-a]` with the same alternatives, since its type depends on them.

  The names in a description need not be in scope (see `Contents`). A name out of scope is
  renamed like its first binder in the definition, so the pass runs twice: once to find the
  new names of the binders and once to rename. All binders of a name in a description are
  aliases (`Linear`), but their paths may differ.
-}
module Backend.Typed.Passes.Paths( pathsProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad( when )
import Data.Maybe( listToMaybe )
import Data.Functor.Const( Const(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common

-- the new names of the variables in scope
type Ren = M.Map Path Path

-- `rsUsed`: the root names bound so far; `rsBound`: each binder with its new name, newest first;
-- `rsRests`: the alternatives of the `[case-a]` that last bound each default binder
data RS = RS{ rsUniq :: Int, rsUsed :: S.Set Name, rsBound :: [(Path,Path)], rsRests :: M.Map Path [Int] }

-- the new names of the first binders of the variables of the definition (for descriptions)
type Global = M.Map Path Path

type R a = State RS a

pathsProgram :: Program -> Program
pathsProgram prog = prog{ progDefs = map pathsDef (progDefs prog) }

pathsDef :: Def -> Def
pathsDef def
  = let (_,st) = run M.empty
    in fst (run (M.fromList (rsBound st)))   -- the oldest binder wins
  where
    run global = runState (renDef global def) (RS 0 S.empty [] M.empty)

renDef :: Global -> Def -> R Def
renDef global def
  = case def of
      DefFun f tvs args res body
        -> do xs <- mapM (\(x,_,_) -> bindRoot x) args
              let ren = M.fromList (zip [x | (x,_,_) <- args] xs)
                  sub = described global ren
              body' <- renE global ren body
              return (DefFun f tvs [(x',m,replaceVType sub t) | (x',(_,m,t)) <- zip xs args] (replaceVType sub res) body')
      DefVal x tvs t body
        -> DefVal x tvs (replaceVType (described global M.empty) t) <$> renE global M.empty body

-- the substitution for descriptions: the variables in scope, and the others by their binders
described :: Global -> Ren -> M.Map Path VVal
described global ren = M.map Var (M.union ren global)

look :: Ren -> Path -> Path
look ren x = M.findWithDefault x x ren

record :: Path -> Path -> R Path
record x x' = do modify (\st -> st{ rsBound = (x,x') : rsBound st })
                 return x'

-- a root keeps its name unless it is already bound
bindRoot :: Path -> R Path
bindRoot x
  = do used <- gets rsUsed
       case x of
         Path n [] | not (S.member n used) -> use n
         _ -> fresh >>= use
  where
    use n = do modify (\st -> st{ rsUsed = S.insert n (rsUsed st) })
               record x (root n)
    fresh = do st <- get
               let n = newHiddenName ("path" ++ show (rsUniq st))
               put st{ rsUniq = rsUniq st + 1 }
               if S.member n (rsUsed st) then fresh else return n

renE :: Global -> Ren -> VExpr -> R VExpr
renE global ren expr
  = do rests <- gets rsRests
       case known rests of
         Just (bs,e) -> do mapM_ (uncurry record) bs
                           renE global (M.union (M.fromList bs) ren) e
         Nothing -> descendB (pure . look ren) (renV global ren) alt annotated
  where
    -- an alternative whose binders are in scope
    known rests
          = do z <- scrut
               m <- case destructAOf expr of
                      Just ds -> Just (dsMode ds)
                      Nothing -> dsMode <$> destructVOf expr
               let inScope = S.fromList (M.elems ren)
                   alts = getConst (descendB (const (Const [])) (const (Const [])) (\bs e -> Const [(bs,e)]) expr)
               listToMaybe [(zip (map fst bs) ps, e) | m /= Unique, (bs@(_:_),e) <- alts
                           , Just ss <- [mapM snd bs], SRest `notElem` ss || M.lookup (child z SRest) rests == Just indices
                           , let ps = map (child z) ss, all (`S.member` inScope) ps]
    indices = case expr of
                CaseA _ _ as _ -> [i | (i,_,_) <- as]
                _ -> []
    sub = described global ren
    scrut = look ren <$> scrutVar expr
    alt bs e = do xs <- mapM bind bs
                  e' <- renE global (M.union (M.fromList (zip (map fst bs) xs)) ren) e
                  return (xs,e')
    bind (x,s) = case pathOf scrut s of
                   Just x' -> do when (s == Just SRest) (modify (\st -> st{ rsRests = M.insert x' indices (rsRests st) }))
                                 record x x'
                   Nothing -> bindRoot x
    annotated = case expr of
      Let x t e1 e2 -> Let x (replaceVType sub t) e1 e2
      LetYield x t e1 e2 e3 -> LetYield x (replaceVType sub t) e1 e2 e3
      Yielded t -> Yielded (replaceVType sub t)
      Call f ts vs -> Call f (map (replaceAType sub) ts) vs
      Join j ps e1 e2 -> Join j [(x,m,replaceVType sub t) | (x,m,t) <- ps] e1 e2
      _ -> expr

renV :: Global -> Ren -> VVal -> R VVal
renV global ren val
  = case val of
      Var x -> pure (Var (look ren x))
      Glob x ts -> pure (Glob x (map tyA ts))
      Inj i t v -> Inj i (tyV t) <$> renV global ren v
      Ptr a v -> Ptr (tyA a) <$> renA global ren v
      Pack t ts v -> Pack (tyV t) (map tyA ts) <$> renV global ren v
      TyApp v ts -> (`TyApp` map tyA ts) <$> renV global ren v
      Context b v -> Context (tyA b) <$> renV global ren v
      NoReuse n p -> pure (NoReuse n (fmap (replaceContents sub) p))
      _ -> descendV (renA global ren) (renV global ren) val
  where
    sub = described global ren
    tyV = replaceVType sub
    tyA = replaceAType sub

renA :: Global -> Ren -> AVal -> R AVal
renA global ren val
  = case val of
      Lam ps r e -> do xs <- mapM (\(x,_,_) -> bindRoot x) ps
                       let ren' = M.union (M.fromList (zip [x | (x,_,_) <- ps] xs)) ren
                           sub = described global ren'
                       Lam [(x',m,replaceVType sub t) | (x',(_,m,t)) <- zip xs ps] (replaceVType sub r) <$> renE global ren' e
      InjA i a v -> InjA i (tyA a) <$> renA global ren v
      Roll a v -> Roll (tyA a) <$> renA global ren v
      OpenCon c ts v -> OpenCon c (map tyA ts) <$> renV global ren v
      _ -> descendA (pure . look ren) (renA global ren) (renV global ren) val
  where
    tyA = replaceAType (described global ren)
