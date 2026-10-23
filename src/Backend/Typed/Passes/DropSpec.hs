-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Drop specialization (after Perceus, before reuse).

  Perceus takes the parts of the contents of a box `z` that it gives up by copying them and
  dropping the box:

    val y₁ = dup x₁; ..; val yₙ = dup xₙ; drop z; e

  If the box is unique, the copies and the drop cancel out: the parts are taken without
  reference counting, and the block becomes a reuse credit, which still contains them. The
  other parts of the contents are dropped. The two branches continue at a join point that
  takes the parts and the credit:

    join j(y₁,..,yₙ,r : ◇n[k; z.contents : V]) = free r; e
    if-unique z then (let @ r' = z in drop ..; jump j(x₁',..,xₙ',r'))
    else (val y₁' = dup x₁; ..; val yₙ' = dup xₙ; drop z; jump j(y₁',..,yₙ',no-reuse n [k; z.contents : V]))

  In the unique branch the contents are renamed to `z.taken` (`[unbox-ru]`), so xᵢ' is the
  part of `z.taken` at the steps of xᵢ from `z.contents`.
  The description of the credit names the contents and the tag k of the block, which follows
  from the path of `z`. The empty credit of the shared branch has the same description, so that
  the jumps agree on it. The shared branch is the original code. Freeing the credit releases
  the block, unless `Reuse` uses it for an allocation in `e`.

  As in Koka's Parc, a part that is under a pointer in the contents is copied in the unique
  branch as well, and the box on the way to it is dropped, which is specialized in turn: the
  unique branch of a nested pattern reuses the inner block too.
-}
module Backend.Typed.Passes.DropSpec( dropSpecProgram ) where

import qualified Data.Map as M
import Control.Monad( foldM, guard )
import Data.List( nub, partition )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env, Gamma, envOf, bindAll, inferVar, inferAVar, inferV, altTypes, unboxRuGamma, boxContents, reuseSize, trivialTy )

type D a = M (Env,Gamma) NameSupply a

fresh :: String -> D Path
fresh s = state (freshPathFrom ("ds" ++ s))

bind :: [(Path,Ty)] -> D a -> D a
bind bs = local (\(env,g) -> (env,bindAll bs g))

withGamma :: Gamma -> D a -> D a
withGamma g = local (\(env,_) -> (env,g))

dropSpecProgram :: Program -> (Program,[String])
dropSpecProgram prog
  = let run d = case evalM (dsE (defBody d)) (envOf prog,params d) (freshFor d) of
                  Right e -> (d{ defBody = e },[])
                  Left err -> (d,[show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs prog))
    in (prog{ progDefs = defs },concat errs)
  where
    params DefFun{ defArgs = ps } = M.fromList [(x,V t) | (x,_,t) <- ps]
    params DefVal{} = M.empty

dsE :: VExpr -> D VExpr
dsE expr
  = do (_,g) <- ask
       case transferOf g expr of
         Just (others,inside,z,s,n,e) | Just ways <- mapM (wayTo (child z SContents) (map fst inside) . fst) inside
           -> compose [Dup x y | (x,y) <- others] <$> specialize (zip inside ways) z s n e
         _ -> dsPlain expr

-- The copies of parts of the contents of a box `z` (among other copies) that Perceus makes
-- before it drops `z`, with the type of the contents and the size of the block.
transferOf :: Gamma -> VExpr -> Maybe ([(Path,Path)],[(Path,Path)],Path,VType,Int,VExpr)
transferOf g expr
  = do (cs,z,e) <- copiesThenDrop expr
       let (inside,others) = partition ((`within` child z SContents) . fst) cs
       guard (not (null inside))
       s <- either (const Nothing) Just (inferAVar g z >>= boxContents)
       n <- either (const Nothing) Just (reuseSize s)
       return (others,inside,z,s,n,e)
  where
    copiesThenDrop (Dup x y e) = (\(cs,z,r) -> ((x,y):cs,z,r)) <$> copiesThenDrop e
    copiesThenDrop (Drop z e) = Just ([],z,e)
    copiesThenDrop _ = Nothing

-- How the unique branch takes a copied part of the contents
data Way = Moved             -- passed on
         | Covered           -- copied, as a part of another copied part
         | Under Path Path   -- copied, under a pointer in the contents: the pointer and the
                             -- box on the way (its dereference, through destructurings that keep it)

-- the way of a copied part `x` of the contents `p` with copied parts `xs`, unless there is
-- no box on the way to it under a pointer
wayTo :: Path -> [Path] -> Path -> Maybe Way
wayTo p xs x
  | any (\y -> y /= x && x `within` y) xs = Just Covered
  | otherwise = case break (== SDeref) (stepsFrom p x) of
                  (_,[]) -> Just Moved
                  (as,rest) -> case break (== SContents) rest of
                                 (bs,_:_) -> Just (Under (foldl child p as) (foldl child p (as ++ bs)))
                                 _ -> Nothing

-- In the unique branch, a part under a pointer is copied, and its box is dropped after the
-- copies of its parts (so that the drop is specialized as well).
specialize :: [((Path,Path),Way)] -> Path -> VType -> Int -> VExpr -> D VExpr
specialize parts z s n e
  = do (_,g) <- ask
       j <- state (freshNameFrom "dsj")
       r <- fresh "r"
       r' <- fresh "c"
       let p = child z SContents
           payload = Just (Contents (Just (boxTag z)) (Var p) s)
           t = VReuse MaybeEmpty n payload
           ps = [(y,Owned,ty) | ((x,y),_) <- parts, Just (V ty) <- [M.lookup x g]] ++ [(r,Owned,t)]
       -- the unique branch names the contents `z.taken`
       let tk = rebase z
       uniqueCopies <- mapM (\((x,_),way) -> case way of Moved -> return (tk x); _ -> fresh "u") parts
       let moved = [tk x | ((x,_),Moved) <- parts]
           unders = [(tk q,tk b) | (_,Under q b) <- parts]
           covered = [Dup (tk x) c | (((x,_),Covered),c) <- zip parts uniqueCopies]
           copies b = [Dup (tk x) c | (((x,_),Under _ b'),c) <- zip parts uniqueCopies, tk b' == b]
       g' <- liftE (unboxRuGamma g z r')
       taken <- withGamma g' (dropExcept (moved ++ nub (map fst unders)) (tk p) s
                  (compose covered (compose [compose (copies b) . Drop b | b <- nub (map snd unders)] (Jump j (map Var uniqueCopies ++ [Var r'])))))
       unique <- dsE (UnboxRu z r' taken)
       sharedCopies <- mapM (const (fresh "u")) parts
       let shared = compose [Dup x c | (((x,_),_),c) <- zip parts sharedCopies]
                      (Drop z (Jump j (map Var sharedCopies ++ [NoReuse n payload])))
       body <- bind [(y,V ty) | (y,_,ty) <- ps] (dsE (Free r e))
       return (Join j ps body (IsUnique z unique shared))

-- Drop `v : t` except for its parts `xs`, which the unique branch passes on.
dropExcept :: [Path] -> Path -> VType -> VExpr -> D VExpr
dropExcept xs v t e
  | any (v `within`) xs = return e
  | not (any (`within` v) xs)
  = do (env,g) <- ask
       dropValue (trivialTy env) (fresh "d") (scopeOf (M.keys g)) v (V t) e
  | VProd{} <- t
  = do (_,g) <- ask
       let fields = fieldsAt v t
       body <- bind [(y,V s) | (y,_,s) <- fields] (foldM (\rest (y,_,s) -> dropExcept xs y s rest) e (reverse fields))
       return (projectAll (scopeOf (M.keys g)) Borrowed v fields body)
  | otherwise
  = do (_,g) <- ask
       case [(y,s) | (y,V s) <- M.toList g, y `within` v, length (stepsFrom v y) == 1, any (`within` y) xs] of
         [(y,s)] -> dropExcept xs y s e
         _ -> fail ("cannot drop the rest of " ++ show v)

dsPlain :: VExpr -> D VExpr
dsPlain expr
  | Just ds <- destructAOf expr
  = do (env,g) <- ask
       t <- liftE (inferVar g (dsScrut ds))
       tss <- liftE (altTypes env t expr)
       es <- sequence [bind (zip xs ts) (dsE e) | ((xs,e),ts) <- zip (dsAlts ds) tss]
       return (dsBuild ds (dsMode ds) (dsScrut ds) es)
  | Just ds <- destructVOf expr
  = do (env,g) <- ask
       t <- liftE (inferV env g (dsScrut ds))
       tss <- liftE (altTypes env (V t) expr)
       v <- dsV (dsScrut ds)
       es <- sequence [bind (zip xs ts) (dsE e) | ((xs,e),ts) <- zip (dsAlts ds) tss]
       return (dsBuild ds (dsMode ds) v es)
dsPlain expr
  = case expr of
      Let x t e1 e2 -> Let x t <$> dsE e1 <*> bind [(x,V t)] (dsE e2)
      LetYield x t e1 e2 e3 -> LetYield x t <$> dsE e1 <*> bind [(x,V t)] (dsE e2) <*> dsE e3
      Join j ps e1 e2 -> Join j ps <$> bind [(x,V t) | (x,_,t) <- ps] (dsE e1) <*> dsE e2
      UnboxRu v r e -> do (_,g) <- ask
                          g' <- liftE (unboxRuGamma g v r)
                          UnboxRu v r <$> withGamma g' (dsE e)
      Dup x y e -> do (_,g) <- ask
                      t <- liftE (inferVar g x)
                      Dup x y <$> bind [(y,t)] (dsE e)
      _ -> descendE pure dsV (\_ e -> dsE e) expr

dsV :: VVal -> D VVal
dsV = descendV dsA dsV

dsA :: AVal -> D AVal
dsA (Lam ps r e) = Lam ps r <$> bind [(x,V t) | (x,_,t) <- ps] (dsE e)
dsA v = descendA pure dsA dsV v
