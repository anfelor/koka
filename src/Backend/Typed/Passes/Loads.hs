-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Loads of the contents of boxes (before Perceus).

  `[case]`, `[deref]` and a use of a value as a whole only read a loaded value, never one in
  the contents of a box (a place). A case on a place `x` becomes a case on its copy:

    case_q x of { injᵢ x.injᵢ -> eᵢ }  ~>  let^ load x.load = x in case_q x.load of { injᵢ x.load.injᵢ -> eᵢ' }

  where eᵢ' uses `x.load` for `x`, and likewise for a dereference and for the places that a
  value uses as a whole (as an argument, a result, a field or a capture). A projection or
  unpack of a place binds a part of it without reading it. Perceus then treats the copy as a
  part of `x`, borrowed from the box like `x`, and does not load it again.

  A place is loaded where it is first read, so that it is read once: before a `let` whose
  bound expression and continuation both read it (for `[let-yield]`, either continuation),
  and otherwise at its first read in each branch.
-}
module Backend.Typed.Passes.Loads( loadsProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe( isJust )
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Backend.Typed.Syntax
import Backend.Typed.Common

loadsProgram :: Program -> Program
loadsProgram prog = prog{ progDefs = [d{ defBody = loadE (defBody d) } | d <- progDefs prog] }

loadE :: VExpr -> VExpr
loadE expr
  = case S.toList (readsAt expr `S.union` shared) of
      [] -> runIdentity (descendE Identity (Identity . loadV) (\_ e -> Identity (loadE e)) expr)
      xs -> loadAt xs expr
  where
    shared = case expr of
               Let _ _ e1 e2 -> readsE e1 `S.intersection` readsE e2
               LetYield _ _ e1 e2 e3 -> readsE e1 `S.intersection` (readsE e2 `S.union` readsE e3)
               _ -> S.empty

-- Load the places `xs` before an expression, which uses the loads instead: the parts of a
-- place that are bound in the expression are parts of its load, while those in scope keep
-- their names.
loadAt :: [Path] -> VExpr -> VExpr
loadAt xs expr
  = compose [Load x (child x SLoad) | x <- xs]
            (loadE (renameE (M.union (M.fromList [(x,child x SLoad) | x <- xs])
                                     (M.fromList [(p,p) | p <- S.toList (fvE expr), any (\x -> p /= x && p `within` x) xs]))
                            expr))

-- the places that an expression reads itself (not in its subexpressions)
readsAt :: VExpr -> S.Set Path
readsAt expr
  = S.filter (isJust . placeOf) $
    case expr of
      Fst _ (Var _) _ _ -> S.empty
      Snd _ (Var _) _ _ -> S.empty
      Unpack _ (Var _) _ _ _ -> S.empty
      _ -> getConst (descendE (const (Const S.empty)) (Const . fvV) (\_ _ -> Const S.empty) expr)

-- the places that an expression reads, that are not bound in it
readsE :: VExpr -> S.Set Path
readsE expr = readsAt expr `S.union` getConst (descendE (const (Const S.empty)) (const (Const S.empty)) inner expr)
  where inner xs e = Const (S.filter (\p -> not (any (p `within`) xs)) (readsE e))

loadV :: VVal -> VVal
loadV = mapV loadA loadV

loadA :: AVal -> AVal
loadA val
  = case val of
      Lam ps r e -> Lam ps r (loadE e)
      _ -> mapA id loadA loadV val
