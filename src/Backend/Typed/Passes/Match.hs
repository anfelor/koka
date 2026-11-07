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

   Finally, the tests of a nested pattern are scheduled by level. A chain is a nest
   of tests with two alternatives that share one failure, interleaved with
   the reads that bring their operands into scope: projections,
   dereferences, rolls, unboxes and cases with one alternative. Elaboration reads a
   field where it is first used, but unboxes a payload as soon as its tag is known,
   so the tests of sibling patterns are separated by reads, and the reads of their
   fields by tests. Like Koka's C backend, which tests a pattern one nesting level at
   a time, the steps are ordered by level: the number of tests that a step depends on
   through its bindings. Each level performs the reads that its tests need and then
   the tests, which code generation joins into one condition (`failingTo`), so that
   the C compiler issues their loads together. Reads that no test needs move behind
   the last test. Reads and tests are pure and defined once their operands are in
   scope, and the failure is outside the scope of the chain, so any order that
   respects the bindings is equivalent.
-}
module Backend.Typed.Passes.Match( matchProgram ) where

import qualified Data.Map as Map
import qualified Data.Set as S
import Data.List( sortOn )
import Data.Maybe( listToMaybe )
import Data.Functor.Identity( Identity(..) )
import Backend.Typed.Syntax
import Backend.Typed.Traversal( TestSide(..), child, descendE, failingTo, fvE, testSides, within )
import Backend.Typed.Passes.Common( mapAll, mapLams, defGamma, typedChildren, Scope, bindScope, defScope, knownAlt, nameParts, perDef, renameE, reuseParts, scopeOf )
import Backend.Typed.Env( Env, envOf, M, ask, evalM, liftE )
import Backend.Typed.Query( Gamma, inferVar )
import Backend.Typed.Layout( shapeIsHeap )

type Match a = M (Env,Gamma) () a

matchProgram :: Program -> (Program,[String])
matchProgram prog = perDef (\d -> (\e -> d{ defBody = levelE (reuseEstablished (defScope d) e) }) <$> evalM (matchE (defBody d)) (envOf prog,defGamma d) ()) prog

matchE :: VExpr -> Match VExpr
matchE expr
  = do e <- typedChildren matchE expr
       case e of
         CaseA v alts def
           -> do (_,g) <- ask
                 t <- liftE (inferVar g v)
                 case t of
                   A (ASum ts) -> partition v ts (sortOn (\(i,_,_) -> i) alts) def
                   _ -> return e
         _ -> return e

partition :: Path -> [(Int,AType)] -> [(Int,Path,VExpr)] -> Maybe (Path,VExpr) -> Match VExpr
partition v _ [] (Just (d,e)) = return (renameE (Map.singleton d v) e)
partition v ts alts def
  = case splitAtIndex ts of
      Just k | canSplit k -> do
        let (ls,rs) = span ((< k) . fst) ts
            (left,right) = span (\(i,_,_) -> i < k) alts
            defaultFor ss = if any (\(i,_) -> i `notElem` selected) ss then def else Nothing
        let x = child v SLo
            y = child v SHi
        e1 <- partition x ls left (defaultFor ls)
        e2 <- partition y rs right (defaultFor rs)
        return (SplitA v k (x,e1) (y,e2))
      _ -> return (nameParts (CaseA v alts def))
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
-- binding the path twice.
reuseEstablished :: Scope -> VExpr -> VExpr
reuseEstablished scope e
  | Just _ <- knownAlt scope e = reuseEstablished scope (reuseParts scope e)
  | otherwise = runIdentity (descendE Identity (Identity . value) branch e)
  where
    branch xs b = Identity (reuseEstablished (bindScope e xs scope) b)
    value = mapLams (\ps _ b -> reuseEstablished (Map.union (scopeOf [x | (x,_,_) <- ps]) scope) b)

-- test levels

-- a read or a test, with its binders and free variables
data Op = Op{ opTest :: Bool, opBuild :: VExpr -> VExpr, opBinds :: [Path], opUses :: S.Set Path }

levelE :: VExpr -> VExpr
levelE expr
  = case chain expr of
      Just (failure,ops,body) -> schedule (map ($ levelE failure) ops) (levelE body)
      Nothing -> mapAll (const levelE) expr

-- A chain of at least two tests, starting at a test. Its steps still need the failure.
chain :: VExpr -> Maybe (VExpr,[VExpr -> Op],VExpr)
chain expr
  = listToMaybe [ (failure,test s : ops,body)
                | s <- testSides expr
                , let (y,failure) = sideOther s
                , not (any (`within` y) (fvE failure))
                , let (ops,body) = collect failure (snd (sideTaken s))
                , any (\o -> opTest (o failure)) ops ]

-- the steps up to the first expression that is neither a read nor a test with this failure
collect :: VExpr -> VExpr -> ([VExpr -> Op],VExpr)
collect failure expr
  = case (readStep expr, failingTo failure expr) of
      (Just (x,build,next),_) -> continue (const (op False build [x])) next
      (_,Just s) -> continue (test s) (snd (sideTaken s))
      _ -> ([],expr)
  where
    continue o next = let (ops,body) = collect failure next in (o : ops,body)

test :: TestSide -> VExpr -> Op
test s failure = op True (\success -> sideRebuild s success failure) [fst (sideTaken s)]

op :: Bool -> (VExpr -> VExpr) -> [Path] -> Op
op isTest build xs = Op isTest build xs (fvE (build (Unreachable VUnit)))

-- Reads of variables cannot fail, call, yield, force or allocate.
readStep :: VExpr -> Maybe (Path,VExpr -> VExpr,VExpr)
readStep expr
  = case expr of
      Proj v@(Var _) i x b -> Just (x,Proj v i x,b)
      Deref v@(Var _) x b -> Just (x,Deref v x,b)
      Unroll v x b -> Just (x,Unroll v x,b)
      Unbox v x b -> Just (x,Unbox v x,b)
      CaseA v [(i,x,b)] Nothing -> Just (x,\b' -> CaseA v [(i,x,b')] Nothing,b)
      _ -> Nothing

-- Level by level: the reads that the tests of a level need first needed there, then those
-- tests, each in its original order; finally the reads that no test needs.
schedule :: [Op] -> VExpr -> VExpr
schedule ops body
  = foldr (opBuild . (ops !!)) body order
  where
    indexed = zip [0..] ops
    deps i = [j | (j,o) <- take i indexed, any (\b -> any (`within` b) (opUses (ops !! i))) (opBinds o)]
    levels = [maximum (0 : [levels !! j + fromEnum (opTest (ops !! j)) | j <- deps i]) | (i,_) <- indexed]
    reads = [S.unions [S.insert j (reads !! j) | j <- deps i, not (opTest (ops !! j))] | (i,_) <- indexed]
    tests = [i | (i,o) <- indexed, opTest o]
    needed i = [levels !! t | t <- tests, i `S.member` (reads !! t)]
    order = concat [ [i | (i,o) <- indexed, not (opTest o), minimum' (needed i) == Just k]
                     ++ [t | t <- tests, levels !! t == k]
                   | k <- [0 .. maximum (map (levels !!) tests)] ]
            ++ [i | (i,o) <- indexed, not (opTest o), null (needed i)]
    minimum' ns = if null ns then Nothing else Just (minimum ns)
