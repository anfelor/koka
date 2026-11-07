-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
-- Licensed under the Apache License, Version 2.0.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Local rewrites for the C code generator, as ordinary typed-IR transformations, checked
-- before any C is emitted: bound C expression nesting (`hoistDeep`), and remove projections
-- whose binder is not used.
module Backend.Typed.Passes.Peephole( peepholeProgram ) where

import Backend.Typed.Syntax
import Backend.Typed.Passes.Common( defGamma, typedChildren, NameSupply, freshFor, freshPathFrom, perBody )
import Backend.Typed.Traversal( fvE, within )
import Backend.Typed.Env( Env, envOf, M, ask, evalM, liftE, state )
import Backend.Typed.Query( Gamma, inferV )

type H a = M (Env,Gamma) NameSupply a

peepholeProgram :: Program -> (Program,[String])
peepholeProgram prog = perBody (\d -> evalM (expr (defBody d)) (envOf prog,defGamma d) (freshFor d)) prog

expr :: VExpr -> H VExpr
expr e
  | Just (v,mk) <- hoistDeep e = do
      (env,g) <- ask
      t <- liftE (inferV env g v)
      x <- state (freshPathFrom "hoist")
      expr (Let x t (Ret v) (mk (Var x)))
  -- a later pass may remove every use (DropSpec removes the drop of a field that reuse overwrites)
  | Just (x,b) <- projection e, not (any (`within` x) (fvE b)) = expr b
  | otherwise = typedChildren expr e

projection :: VExpr -> Maybe (Path,VExpr)
projection (Proj _ _ x b) = Just (x,b)
projection _ = Nothing

-- bind deeply nested values first (C compilers limit the nesting of brackets)
hoistDeep :: VExpr -> Maybe (VVal, VVal -> VExpr)
hoistDeep expr
  = case expr of
      Ret v -> one v Ret
      Call f ts vs -> many vs (Call f ts)
      App f vs -> many vs (App f)
      Memoize c d k w -> one w (Memoize c d k)
      _ -> Nothing
  where
    one v k = do (w,mk) <- deep 0 v
                 return (w,k . mk)
    many vs k = case [(i,r) | (i,v) <- zip [0..] vs, Just r <- [deep 0 v]] of
                  ((i,(w,mk)):_) -> Just (w, \x -> k (take i vs ++ [mk x] ++ drop (i+1) vs))
                  [] -> Nothing
    deep :: Int -> VVal -> Maybe (VVal, VVal -> VVal)
    -- only whole values of named types, whose tags have no offset in an enclosing sum
    deep d v
      | d >= 24 && depth v > 8, Ptr _ _ <- v = Just (v,id)
      | otherwise = case [(replace,r) | (w,replace) <- childrenV v, Just r <- [deep (d+1) w]] of
                      ((replace,(u,mk)):_) -> Just (u, replace . mk)
                      [] -> Nothing

-- nesting depth of value constructors
depth :: VVal -> Int
depth v
  = case childrenV v of
      [] -> 0
      ws -> 1 + maximum (map (depth . fst) ws)

-- Unboxed children reached through boxed constructors, with typed rebuild functions.
childrenV :: VVal -> [(VVal, VVal -> VVal)]
childrenV v = case v of
  Inj i t w -> [(w,Inj i t)]
  Tuple ws -> [(w,\x -> Tuple (before ++ x : after)) | (before,w:after) <- [splitAt i ws | i <- [0 .. length ws - 1]]]
  Ptr a w -> [(u,Ptr a . rebuild) | (u,rebuild) <- childrenA w]
  Pack t ts w -> [(w,Pack t ts)]
  TyApp w ts -> [(w,\x -> TyApp x ts)]
  DupV w -> [(w,DupV)]
  _ -> []

childrenA :: AVal -> [(VVal, VVal -> AVal)]
childrenA v = case v of
  InjA i a w -> [(u,InjA i a . rebuild) | (u,rebuild) <- childrenA w]
  Roll a w -> [(u,Roll a . rebuild) | (u,rebuild) <- childrenA w]
  InjLazy d a w -> [(u,InjLazy d a . rebuild) | (u,rebuild) <- childrenA w]
  Box w -> [(w,Box)]
  OpenCon c ts ws -> [(w,\x -> OpenCon c ts (take i ws ++ [x] ++ drop (i+1) ws)) | (i,w) <- zip [0..] ws]
  BoxAt r w -> [(w,BoxAt r)]
  _ -> []

