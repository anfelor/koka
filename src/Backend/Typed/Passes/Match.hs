-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Shape boxed dispatch after the ownership passes, without moving or copying
   branch bodies. Exhaustive cases become binary partitions: prefer a boundary
   separating immediates from heap blocks (even for two alternatives), otherwise
   balance by alternative count down to two-way cases.
   Sparse cases can split off an immediate default from heap alternatives. The
   default's residual sum keeps its original indices; its body is never copied.
-}
module Backend.Typed.Passes.Match( matchProgram ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List( sortOn )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env, Gamma, envOf, bindAll, inferVar, inferV, altTypes, boxContents, reuseSize )
import Backend.Typed.Layout( shapeIsHeap )

type Match a = M (Env,Gamma) (Int,Set.Set Name) a

matchProgram :: Program -> (Program,[String])
matchProgram prog
  = let run d = case evalM (matchE (defBody d)) (envOf prog,params d)
                          (0,Set.fromList (bindersE (defBody d)) `Set.union` fvE (defBody d)) of
                  Right e -> (d{ defBody = e },[])
                  Left err -> (d,[show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs prog))
    in (prog{ progDefs = defs },concat errs)
  where
    params DefFun{ defArgs = ps } = Map.fromList [(x,V t) | (x,_,t) <- ps]
    params DefVal{} = Map.empty

fresh :: Match Name
fresh = do (n,used) <- get
           let x = newHiddenName ("match" ++ show n)
           put (n+1,Set.insert x used)
           if Set.member x used then fresh else return x

bind :: [(Name,Ty)] -> Match a -> Match a
bind bs = local (\(env,g) -> (env,bindAll bs g))

matchE :: VExpr -> Match VExpr
matchE expr
  | Just ds <- destructAOf expr
  = do (env,g) <- ask
       t <- liftE (inferVar g (dsScrut ds))
       tss <- liftE (altTypes env t expr)
       es <- sequence [bind (zip xs ts) (matchE e) | ((xs,e),ts) <- zip (dsAlts ds) tss]
       let result = dsBuild ds (dsMode ds) (dsScrut ds) es
       case (result,t) of
         (CaseA m v alts def,A (ASum ts))
           -> partition m v ts (sortOn (\(i,_,_) -> i) alts) def
         _ -> return result
  | Just ds <- destructVOf expr
  = do (env,g) <- ask
       t <- liftE (inferV env g (dsScrut ds))
       tss <- liftE (altTypes env (V t) expr)
       v <- matchV (dsScrut ds)
       es <- sequence [bind (zip xs ts) (matchE e) | ((xs,e),ts) <- zip (dsAlts ds) tss]
       return (dsBuild ds (dsMode ds) v es)
matchE expr
  = case expr of
      Let x t e1 e2 -> Let x t <$> matchE e1 <*> bind [(x,V t)] (matchE e2)
      Join j ps e1 e2 -> Join j ps <$> local (\(env,_) -> (env,Map.fromList [(x,V t) | (x,_,t) <- ps])) (matchE e1)
                                 <*> matchE e2
      Dup x y e -> do (_,g) <- ask
                      t <- liftE (inferVar g x)
                      Dup x y <$> bind [(y,t)] (matchE e)
      UnboxRu v x r e
        -> do (_,g) <- ask
              A a <- liftE (inferVar g v)
              t <- liftE (boxContents a)
              n <- liftE (reuseSize t)
              UnboxRu v x r <$> bind [(x,V t),(r,V (VReuse n (Just (Var x))))] (matchE e)
      _ -> descendE pure matchV (\_ -> matchE) expr

partition :: Mode -> Name -> [(Int,AType)] -> [(Int,Name,VExpr)] -> Maybe (Name,VExpr) -> Match VExpr
partition _ v _ [] (Just (d,e)) = return (renameE (Map.singleton d v) e)
partition m v ts alts def
  = case splitAtIndex ts of
      Just k | canSplit k -> do
        let (ls,rs) = span ((< k) . fst) ts
            (left,right) = span (\(i,_,_) -> i < k) alts
            defaultFor ss = if any (\(i,_) -> i `notElem` selected) ss then def else Nothing
        x <- fresh
        y <- fresh
        e1 <- partition m x ls left (defaultFor ls)
        e2 <- partition m y rs right (defaultFor rs)
        return (SplitA m v k (x,e1) (y,e2))
      _ -> return (CaseA m v alts def)
  where
    selected = [i | (i,_,_) <- alts]
    -- A sparse default must fit wholly on the immediate side. This avoids
    -- copying its body and keeps an effect-yield dummy on the default path.
    canSplit _ | Nothing <- def = True
    canSplit k = let (ls,rs) = span ((< k) . fst) ts
                     immediate ss = shapeIsHeap (ASum ss) == Just False
                                    && all (\(i,_) -> i `notElem` selected) ss
                     heap ss = shapeIsHeap (ASum ss) == Just True
                               && all (\(i,_) -> i `elem` selected) ss
                 in (immediate ls && heap rs) || (heap ls && immediate rs)

-- Only contiguous groups preserve the runtime tag order. A pointer split is
-- useful when there is exactly one change of representation; otherwise use a
-- balanced tree, without guessing which constructors are hot.
splitAtIndex :: [(Int,AType)] -> Maybe Int
splitAtIndex ts
  = case mapM (shapeIsHeap . snd) ts of
      Just (b:bs) -> let (same,rest) = span (== b) bs
                    in if not (null rest) && all (/= b) rest
                       then Just (fst (ts !! (1 + length same))) else balanced
      _ -> balanced
  where balanced | length ts > 2 = Just (fst (ts !! (length ts `div` 2)))
                 | otherwise = Nothing

matchV :: VVal -> Match VVal
matchV = descendV matchA matchV

matchA :: AVal -> Match AVal
matchA (Lam ps r e) = Lam ps r <$> bind [(x,V t) | (x,_,t) <- ps] (matchE e)
matchA a = descendA pure matchA matchV a
