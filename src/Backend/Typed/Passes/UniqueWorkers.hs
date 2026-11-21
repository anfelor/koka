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
  created if it has fewer copies than `f`. Functions with a unique result already are left out.

  A function in which an effect may yield returns `ctx?`; its worker returns `:! ctx?` (the
  dummy `null` is unique enough). A tail `some v` with a `v` that is not unique becomes
  `let c = ctx-copy v in ret (some c)`.

  `f` itself is unchanged, for callers that cannot pass unique contexts and for other
  modules. `UniqueJoins` calls the worker where the arguments of its unique parameters are
  unique, and `CheckLinear` validates the result.
-}
module Backend.Typed.Passes.UniqueWorkers( uniqueWorkersProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe( maybeToList )
import Backend.Typed.Syntax
import Backend.Typed.Env( Env, envOf )
import Backend.Typed.Traversal( descendE )
import Backend.Typed.Types( unNull, yields )
import Control.Monad.State( State, evalState, state )
import Backend.Typed.Passes.Common( NameSupply, freshFor, freshPathFrom )
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
      DefFun{ defResMode = Owned }
        | isCtx ctxT -> promote [x | (x,Owned,t) <- defArgs def, isCtx t]
      _ -> Nothing
  where
    ctxT = unNull (defRes def)
    -- the greatest set of context parameters that remain unique in the body
    promote [] = Nothing
    promote cs
      | kept /= cs = promote kept
      | all result (tails body') && copyCount body'' < copyCount (defBody def)
      = Just def{ defName = workerName (defName def), defArgs = ps, defResMode = Unique, defBody = body'' }
      | otherwise = Nothing
      where
        ps = [(x,if x `elem` cs then Unique else m,t) | (x,m,t) <- defArgs def]
        ((u,body'),body'') = evalState (do r@(u0,b) <- uniqueScope env ps (defBody def)
                                           (,) r <$> mapRets (copy u0) b) (freshFor def)
        kept = filter (`S.member` u) cs
        result r = case r of
                     FVal v -> copyable v
                     _ -> uniqF env u r
        copyable v = uniq u v || not (yields (defRes def)) || isSome v
        isSome v = case v of
                     Some _ -> True
                     _ -> False
        -- a value that is not unique is copied (`copyable`)
        copy :: S.Set Path -> VVal -> State NameSupply VExpr
        copy u0 v = case v of
                      _ | uniq u0 v -> return (Ret v)
                      Some w -> do c <- state (freshPathFrom "copy")
                                   return (Let c ctxT (CtxCopy w) (Ret (Some (Var c))))
                      _ -> return (CtxCopy v)

-- replace the values in the tail positions of an expression (see `UniqueJoins.tails`)
mapRets :: (VVal -> State NameSupply VExpr) -> VExpr -> State NameSupply VExpr
mapRets f expr
  = case expr of
      Ret v -> f v
      Let x t e1 e2 -> Let x t e1 <$> mapRets f e2
      Gen{} -> return expr
      CastEv{} -> return expr
      _ -> descendE pure pure (\_ e -> mapRets f e) expr
