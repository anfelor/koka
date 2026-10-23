-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
-- Licensed under the Apache License, Version 2.0.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Bound C expression nesting before computing backend plans. Hoisting is an
-- ordinary typed-IR transformation, checked before any C is emitted.
module Backend.Typed.Passes.Hoist( hoistProgram ) where

import qualified Data.Map as M
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query

type H a = M (Env,Gamma) NameSupply a

hoistProgram :: Program -> (Program,[String])
hoistProgram prog = (prog{ progDefs = map fst results },concatMap snd results)
  where
    results = map run (progDefs prog)
    run d = case evalM (expr (defBody d)) (envOf prog,params d) (freshFor d) of
      Left err -> (d,[show (defName d) ++ ": " ++ err])
      Right e -> (d{ defBody = e },[])
    params (DefFun _ _ ps _ _) = M.fromList [(x,V t) | (x,_,t) <- ps]
    params DefVal{} = M.empty

bind :: [(Path,Ty)] -> H a -> H a
bind bs = local (\(env,g) -> (env,bindAll bs g))

expr :: VExpr -> H VExpr
expr e
  | Just (v,mk) <- hoistDeep e = do
      (env,g) <- ask
      t <- liftE (inferV env g v)
      x <- state (freshPathFrom "hoist")
      a <- expr (Ret v)
      b <- bind [(x,V t)] (expr (mk (Var x)))
      return (Let x t a b)
  | Just ds <- destructAOf e = do
      (env,g) <- ask
      t <- liftE (inferVar g (dsScrut ds))
      ts <- liftE (altTypes env t e)
      bs <- sequence [bind (zip xs ss) (expr b) | ((xs,b),ss) <- zip (dsAlts ds) ts]
      return (dsBuild ds (dsMode ds) (dsScrut ds) bs)
  | Just ds <- destructVOf e = do
      (env,g) <- ask
      t <- liftE (inferV env g (dsScrut ds))
      ts <- liftE (altTypes env (V t) e)
      v <- value (dsScrut ds)
      bs <- sequence [bind (zip xs ss) (expr b) | ((xs,b),ss) <- zip (dsAlts ds) ts]
      return (dsBuild ds (dsMode ds) v bs)
expr e = case e of
  Let x t a b -> Let x t <$> expr a <*> bind [(x,V t)] (expr b)
  LetYield x t a b c -> LetYield x t <$> expr a <*> bind [(x,V t)] (expr b) <*> expr c
  Join j ps a b -> Join j ps <$> bind [(x,V t) | (x,_,t) <- ps] (expr a) <*> expr b
  UnboxRu z r b -> do
    (env,g) <- ask
    g' <- liftE (unboxRuGamma g z r)
    UnboxRu z r <$> local (const (env,g')) (expr b)
  Dup x y b -> do
    (_,g) <- ask
    t <- liftE (inferVar g x)
    Dup x y <$> bind [(y,t)] (expr b)
  IfFull r a b -> do
    (_,g) <- ask
    rt <- liftE (inferVar g r)
    case rt of
      V (VReuse _ n p) -> IfFull r <$> bind [(r,V (VReuse Full n p))] (expr a) <*> expr b
      _ -> fail "hoist: test of a non-credit"
  _ -> descendE pure value (\_ -> expr) e

value :: VVal -> H VVal
value = descendV atom value

atom :: AVal -> H AVal
atom (Lam ps r e) = Lam ps r <$> bind [(x,V t) | (x,_,t) <- ps] (expr e)
atom a = descendA pure atom value a

-- bind deeply nested values first (C compilers limit the nesting of brackets)
hoistDeep :: VExpr -> Maybe (VVal, VVal -> VExpr)
hoistDeep expr
  = case expr of
      Ret v -> one v Ret
      Call f ts vs -> many vs (Call f ts)
      App f vs -> many vs (App f)
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
  Pair u w -> [(u,\x -> Pair x w),(w,Pair u)]
  Ptr a w -> [(u,Ptr a . rebuild) | (u,rebuild) <- childrenA w]
  Pack t ts w -> [(w,Pack t ts)]
  TyApp w ts -> [(w,\x -> TyApp x ts)]
  DupV w -> [(w,DupV)]
  _ -> []

childrenA :: AVal -> [(VVal, VVal -> AVal)]
childrenA v = case v of
  InjA i a w -> [(u,InjA i a . rebuild) | (u,rebuild) <- childrenA w]
  Roll a w -> [(u,Roll a . rebuild) | (u,rebuild) <- childrenA w]
  Box w -> [(w,Box)]
  OpenCon c ts ws -> [(w,\x -> OpenCon c ts (take i ws ++ [x] ++ drop (i+1) ws)) | (i,w) <- zip [0..] ws]
  BoxAt r w -> [(w,BoxAt r)]
  BoxIn x w -> [(w,BoxIn x)]
  _ -> []

