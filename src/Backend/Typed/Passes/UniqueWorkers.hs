-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Workers with unique contexts (right after TailRec, before UniqueJoins).

  A call never returns a unique value unless its function has a unique result. A function
  that returns a context and takes owned contexts therefore gets a worker `f!` (`workerName`)
  whose context parameters and result are unique:

    fun (++)(acc : ctx, t) : ctx = ... let c = ctx-copy acc in c ++ ctx K ... ret acc
    ~> fun (++)!(acc :! ctx, t) : !ctx = ... acc ++ ctx K ... ret acc

  The body of the worker is that of `f` with its context parameters unique, rewritten by
  `UniqueJoins.uniqueScope`. A parameter that does not remain unique there (as a borrowed use
  demotes it) stays owned. A result that is a value but not unique is copied; a call is not
  copied, so every call in a tail position must have a unique result. The worker is only
  created if it has fewer copies than `f`. Functions in which an effect may yield are left
  out, as are functions with a unique result already.

  `f` itself is unchanged, for callers that cannot pass unique contexts and for other
  modules. `UniqueJoins` calls the worker where the arguments of its unique parameters are
  unique, and `CheckLinear` validates the result.
-}
module Backend.Typed.Passes.UniqueWorkers( uniqueWorkersProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Data.Maybe( maybeToList )
import Data.Monoid( Any(..) )
import Backend.Typed.Syntax
import Backend.Typed.Env( Env, envOf )
import Backend.Typed.Traversal( descendE )
import Control.Monad.State( evalState )
import Backend.Typed.Passes.Common( freshFor )
import Backend.Typed.Passes.UniqueJoins( uniqueScope, Flow(..), tails, uniq, uniqF, copyCount, isCtx, workerName )

uniqueWorkersProgram :: Program -> Program
uniqueWorkersProgram prog
  = prog{ progDefs = concat [d : maybeToList w | (d,w) <- ws]
        , progSigs = M.union (M.fromList [(defName w, sigOf w) | (_,Just w) <- ws]) (progSigs prog) }
  where
    env = envOf prog
    ws = [(d, worker env d) | d <- progDefs prog]
    sigOf w = SigFun (defParams w) [(m,t) | (_,m,t) <- defArgs w] (defResMode w) (defRes w)

worker :: Env -> Def -> Maybe Def
worker env def
  = case def of
      DefFun{ defResMode = Owned, defRes = VCtx{}, defBody = body }
        | not (yields body) -> promote [x | (x,Owned,t) <- defArgs def, isCtx t]
      _ -> Nothing
  where
    -- the greatest set of context parameters that remain unique in the body
    promote [] = Nothing
    promote cs
      | kept /= cs = promote kept
      | all result (tails body') && copyCount body'' < copyCount (defBody def)
      = Just def{ defName = workerName (defName def), defArgs = ps, defResMode = Unique, defBody = body'' }
      | otherwise = Nothing
      where
        ps = [(x,if x `elem` cs then Unique else m,t) | (x,m,t) <- defArgs def]
        (u,body') = evalState (uniqueScope env ps (defBody def)) (freshFor def)
        kept = filter (`S.member` u) cs
        result r = case r of
                     FVal _ -> True
                     _ -> uniqF env u r
        body'' = mapRets (\v -> if uniq u v then Ret v else CtxCopy v) body'

-- whether an effect may yield in an expression, outside of closures
yields :: VExpr -> Bool
yields expr
  = case expr of
      LetYield{} -> True
      Yielded{} -> True
      _ -> getAny (getConst (descendE (const (Const mempty)) (const (Const mempty)) (\_ e -> Const (Any (yields e))) expr))

-- replace the values in the tail positions of an expression (see `UniqueJoins.tails`)
mapRets :: (VVal -> VExpr) -> VExpr -> VExpr
mapRets f expr
  = case expr of
      Ret v -> f v
      Let x t e1 e2 -> Let x t e1 (mapRets f e2)
      LetYield x t e1 e2 e3 -> LetYield x t e1 (mapRets f e2) (mapRets f e3)
      Gen{} -> expr
      _ -> runIdentity (descendE pure pure (\_ e -> Identity (mapRets f e)) expr)
