-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Self tail calls become loops (right after Perceus).

  A function whose body calls itself in tail position becomes a recursive join point
  (`[join-rec]`) whose parameters are those of the function, with the same modes:

    fun f⟨ā⟩(x̄ :q̄ V̄) : W = e   ~>   fun f⟨ā⟩(ȳ :q̄ V̄) : W = join rec j⟨b̄⟩(x̄ :q̄ V̄) : W = e' in jump j[b̄](ȳ)

  where e' replaces the self tail calls `f[B̄](v̄)` of e by `jump j[B̄ restricted to b̄](v̄)`.
  The join point quantifies over the type parameters b̄ of f that the calls change (for
  polymorphic recursion). These must not occur in W (`[join-rec]` requires b̄ ∉ ftv(W)), so
  a call can only become a jump if it passes the parameters in W unchanged. The others stay
  those of f, so that `JoinArgs` can capture variables whose types mention them. The body
  of the function only has its parameters in scope, so the join point is closed.
-}
module Backend.Typed.Passes.TailRec( tailRecProgram ) where

import Data.Functor.Identity( Identity(..) )
import Common.Name( Name )
import Backend.Typed.Syntax
import Backend.Typed.Types( Types(..) )
import Backend.Typed.Traversal( descendE, jumps )
import Backend.Typed.Passes.Common( freshFor, substJump, freshNameFrom, freshPathFrom, mentionedT )

tailRecProgram :: Program -> Program
tailRecProgram prog = prog{ progDefs = map tailRecDef (progDefs prog) }

tailRecDef :: Def -> Def
tailRecDef def
  = case def of
      DefFun f tvs args res body
        | all (\(_,_,t) -> null (mentionedT t)) args     -- the parameters are renamed
        , body0 <- selfJumps f j tvs cands body, body0 /= body
        -> let (ys,_) = foldr (\_ (ps,s) -> let (p,s') = freshPathFrom "arg" s in (p:ps,s')) ([],supply') args
               -- the candidates that some jump changes
               bs = [b | (i,b) <- zip [0..] cands, any (\(ts,_) -> ts !! i /= AVar b) (jumps j body0)]
               body' = substJump j (\ts -> Jump j [t | (t,b) <- zip ts cands, b `elem` bs]) body0
           in def{ defArgs = [(y,m,t) | (y,(_,m,t)) <- zip ys args]
                 , defBody = Join (Rec res) j bs args body' (Jump j (map AVar bs) (map Var ys)) }
      _ -> def
  where
    (j,supply') = freshNameFrom "loop" (freshFor def)
    -- the type parameters that a loop over the body may quantify over
    cands = [a | a <- defParams def, a `notElem` ftv (defRes def)]

-- replace the self tail calls of `f` by jumps to `j`, which quantifies over `bs`
selfJumps :: Name -> Name -> [TVar] -> [TVar] -> VExpr -> VExpr
selfJumps f j tvs bs = go
  where
    go expr
      = case expr of
          Call g tys vs
            | g == f, length tys == length tvs
            , and [ty == AVar a | (a,ty) <- zip tvs tys, a `notElem` bs]
            -> Jump j [ty | (a,ty) <- zip tvs tys, a `elem` bs] vs
          -- not in tail position
          Let x t e1 e2 -> Let x t e1 (go e2)
          LetYield x t e1 e2 e3 -> LetYield x t e1 (go e2) (go e3)
          Gen _ _ -> expr
          Join rc@Rec{} k ks ps e1 e2 -> Join rc k ks ps e1 (go e2)
          _ -> runIdentity (descendE pure pure (\_ e -> Identity (go e)) expr)
