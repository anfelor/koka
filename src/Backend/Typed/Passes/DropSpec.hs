-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Drop specialization (after Perceus, before reuse).

  Perceus takes the parts of the contents of a box `z` that it gives up by duplicating them
  and dropping the box:

    dup x₁; ..; dup xₙ; drop z; e

  If the box is unique, the dups and the drop cancel out: the parts are taken without
  reference counting, and the block becomes a reuse credit, which still contains them. The
  other parts of the contents are dropped. Both branches leave the parts owned, and continue
  at a join point that takes the credit:

    join j(r : ◇n[k; z.contents : V]) = free r; e
    if-unique z then (let @ r' = z in drop ..; jump j(r'))
    else (dup x₁; ..; dup xₙ; drop z; jump j(no-reuse n [k; z.contents : V]))

  The description of the credit names the contents and the tag k of the block, which
  follows from the path of `z`. The empty credit of the shared branch has the same description, so that the jumps agree on it
  (and `FillCredits` may fill it with a copy of the block). The shared branch is the
  original code. Freeing the credit releases the block, unless `Reuse` uses it for an
  allocation in `e`.

  As in Koka's Parc, a part that is under a pointer in the contents is duplicated in the
  unique branch as well, and the box on the way to it is dropped, which is specialized in turn: the
  unique branch of a nested pattern reuses the inner block too.
-}
module Backend.Typed.Passes.DropSpec( dropSpecProgram ) where

import qualified Data.Map as M
import Control.Monad( foldM, guard )
import Data.List( nub, partition )
import Backend.Typed.Syntax
import Backend.Typed.Build( compose )
import Backend.Typed.Traversal( boxTag, child, fieldsAt, stepsFrom, within )
import Backend.Typed.Passes.Common( trivialTy, defGamma, typedChildren, NameSupply, dropValue, freshFor, freshNameFrom, freshPathFrom, perBody, projectAll, scopeOf )
import Backend.Typed.Env( Env, envOf, boxContents, reuseSize, M, ask, evalM, liftE, local, state )
import Backend.Typed.Query( Gamma, bindAll, inferAVar, unboxRuGamma )

type D a = M (Env,Gamma) NameSupply a

fresh :: String -> D Path
fresh s = state (freshPathFrom ("ds" ++ s))

bind :: [(Path,Ty)] -> D a -> D a
bind bs = local (\(env,g) -> (env,bindAll bs g))

withGamma :: Gamma -> D a -> D a
withGamma g = local (\(env,_) -> (env,g))

dropSpecProgram :: Program -> (Program,[String])
dropSpecProgram prog = perBody (\d -> evalM (dsE (defBody d)) (envOf prog,defGamma d) (freshFor d)) prog

dsE :: VExpr -> D VExpr
dsE expr
  = do (_,g) <- ask
       case transferOf g expr of
         Just (others,inside,z,s,n,e) | Just ways <- mapM (wayTo (child z SContents) inside) inside
           -> compose (map Dup others) <$> specialize (zip inside ways) z s n e
         _ -> typedChildren dsE expr

-- The dups of parts of the contents of a box `z` (among other dups) that Perceus makes
-- before it drops `z`, with the type of the contents and the size of the block.
transferOf :: Gamma -> VExpr -> Maybe ([Path],[Path],Path,VType,Int,VExpr)
transferOf g expr
  = do (xs,z,e) <- dupsThenDrop expr
       let (inside,others) = partition (`within` child z SContents) xs
       guard (not (null inside))
       s <- either (const Nothing) Just (inferAVar g z >>= boxContents)
       n <- either (const Nothing) Just (reuseSize s)
       return (others,inside,z,s,n,e)
  where
    dupsThenDrop (Dup x e) = (\(xs,z,r) -> (x:xs,z,r)) <$> dupsThenDrop e
    dupsThenDrop (Drop z e) = Just ([],z,e)
    dupsThenDrop _ = Nothing

-- How the unique branch takes a duplicated part of the contents
data Way = Moved             -- passed on
         | Covered           -- duplicated, as a part of another duplicated part
         | Under Path Path   -- duplicated, under a pointer in the contents: the pointer and the
                             -- box on the way (its dereference, through destructurings that keep it)

-- the way of a duplicated part `x` of the contents `p` with duplicated parts `xs`, unless
-- there is no box on the way to it under a pointer.
wayTo :: Path -> [Path] -> Path -> Maybe Way
wayTo p xs x
  | any (\y -> y /= x && x `within` y) xs = Just Covered
  | otherwise = case break (== SDeref) (stepsFrom p x) of
                  (_,[]) -> Just Moved
                  (as,rest) -> case break (== SContents) rest of
                                 (bs,_:_) -> Just (Under (foldl child p as) (foldl child p (as ++ bs)))
                                 _ -> Nothing

-- In the unique branch, a part under a pointer is duplicated, and its box is dropped after
-- the dups of its parts (so that the drop is specialized as well).
specialize :: [(Path,Way)] -> Path -> VType -> Int -> VExpr -> D VExpr
specialize parts z s n e
  = do (_,g) <- ask
       j <- state (freshNameFrom "dsj")
       r <- fresh "r"
       let p = child z SContents
           r' = child z SCredit
           payload = Just (Contents (Just (boxTag z)) (Var p) s)
           t = VReuse MaybeEmpty n payload
           moved = [x | (x,Moved) <- parts]
           unders = [(q,b) | (_,Under q b) <- parts]
           covered = [Dup x | (x,Covered) <- parts]
           dups b = [Dup x | (x,Under _ b') <- parts, b' == b]
       g' <- liftE (unboxRuGamma g z)
       taken <- withGamma g' (dropExcept (moved ++ nub (map fst unders)) p s
                  (compose covered (compose [compose (dups b) . Drop b | b <- nub (map snd unders)] (Jump j [] [Var r']))))
       unique <- dsE (UnboxRu z taken)
       let shared = compose (map (Dup . fst) parts) (Drop z (Jump j [] [NoReuse n payload]))
       body <- bind [(r,V t)] (dsE (Free r e))
       return (Join NonRec j [] [(r,Owned,t)] body (IsUnique z unique shared))

-- Drop `v : t` except for its parts `xs`, which the unique branch passes on.
dropExcept :: [Path] -> Path -> VType -> VExpr -> D VExpr
dropExcept xs v t e
  = do (env,g) <- ask
       case t of
         _ | any (v `within`) xs -> return e
           | not (any (`within` v) xs) -> dropValue (trivialTy env) (fresh "d") (scopeOf (M.keys g)) v (V t) e
         VProd{} -> do let fields = fieldsAt v t
                       body <- bind [(y,V s) | (y,_,s) <- fields] (foldM (\rest (y,_,s) -> dropExcept xs y s rest) e (reverse fields))
                       return (projectAll (scopeOf (M.keys g)) Borrowed v fields body)
         _ -> case [(y,s) | (y,V s) <- M.toList g, y `within` v, length (stepsFrom v y) == 1, any (`within` y) xs] of
                [(y,s)] -> dropExcept xs y s e
                _ -> fail ("cannot drop the rest of " ++ show v)
