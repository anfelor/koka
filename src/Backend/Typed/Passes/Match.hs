-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Shape boxed dispatch after the ownership passes, without moving or copying
   branch bodies. Exhaustive cases become binary partitions: prefer a boundary
   separating immediates from heap blocks (even for two alternatives), otherwise
   balance by alternative count down to two-way cases.
   Sparse cases can split off a default on one side of a pointer test from the
   alternatives on the other. The default's residual sum keeps its original
   indices; its body is never copied.
-}
module Backend.Typed.Passes.Match( matchProgram ) where

import qualified Data.Map as Map
import Data.List( sortOn )
import Data.Functor.Identity( Identity(..) )
import Backend.Typed.Syntax
import Backend.Typed.Traversal( child, descendE )
import Backend.Typed.Passes.Common( mapLams, defGamma, typedChildren, Scope, bindScope, defScope, knownAlt, nameParts, perDef, renameE, reuseParts, scopeOf )
import Backend.Typed.Monad
import Backend.Typed.Query( Env, Gamma, envOf, inferVar )
import Backend.Typed.Layout( shapeIsHeap )

type Match a = M (Env,Gamma) () a

matchProgram :: Program -> (Program,[String])
matchProgram prog = perDef (\d -> (\e -> d{ defBody = reuseEstablished (defScope d) e }) <$> evalM (matchE (defBody d)) (envOf prog,defGamma d) ()) prog

matchE :: VExpr -> Match VExpr
matchE expr
  = do e <- typedChildren matchE expr
       case e of
         CaseA m v alts def
           -> do (_,g) <- ask
                 t <- liftE (inferVar g v)
                 case t of
                   A (ASum ts) -> partition m v ts (sortOn (\(i,_,_) -> i) alts) def
                   _ -> return e
         _ -> return e

partition :: Mode -> Path -> [(Int,AType)] -> [(Int,Path,VExpr)] -> Maybe (Path,VExpr) -> Match VExpr
partition _ v _ [] (Just (d,e)) = return (renameE (Map.singleton d v) e)
partition m v ts alts def
  = case splitAtIndex ts of
      Just k | canSplit k -> do
        let (ls,rs) = span ((< k) . fst) ts
            (left,right) = span (\(i,_,_) -> i < k) alts
            defaultFor ss = if any (\(i,_) -> i `notElem` selected) ss then def else Nothing
        let x = child v SLo
            y = child v SHi
        e1 <- partition m x ls left (defaultFor ls)
        e2 <- partition m y rs right (defaultFor rs)
        return (SplitA m v k (x,e1) (y,e2))
      _ -> return (nameParts (CaseA m v alts def))
  where
    selected = [i | (i,_,_) <- alts]
    -- A sparse default must fit wholly on one side of a pointer test, so that
    -- its body is not copied.
    canSplit _ | Nothing <- def = True
    canSplit k = let (ls,rs) = span ((< k) . fst) ts
                     pointer = case (shapeIsHeap (ASum ls),shapeIsHeap (ASum rs)) of
                                 (Just l,Just r) -> l /= r
                                 _ -> False
                     defaults ss = all (\(i,_) -> i `notElem` selected) ss
                     matched ss = all (\(i,_) -> i `elem` selected) ss
                 in pointer && ((defaults ls && matched rs) || (matched ls && defaults rs))

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

-- Partitioning changes the paths of branch binders. A continuation may already
-- destructure that same part; select its established alternative instead of
-- binding the path twice. Unique eliminations must retain their ownership use.
reuseEstablished :: Scope -> VExpr -> VExpr
reuseEstablished scope e
  | Just _ <- knownAlt scope e = reuseEstablished scope (reuseParts scope e)
  | otherwise = runIdentity (descendE Identity (Identity . value) branch e)
  where
    branch xs b = Identity (reuseEstablished (bindScope e xs scope) b)
    value = mapLams (\ps _ b -> reuseEstablished (Map.union (scopeOf [x | (x,_,_) <- ps]) scope) b)
