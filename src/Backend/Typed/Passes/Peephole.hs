-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
-- Licensed under the Apache License, Version 2.0.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Local rewrites for the C code generator, as ordinary typed-IR transformations, checked
-- before any C is emitted: bound C expression nesting (`hoistDeep`), read a box in memory
-- order (`inMemoryOrder`), and remove projections whose binder is not used.
module Backend.Typed.Passes.Peephole( peepholeProgram ) where

import qualified Data.Map as M
import Data.List( sortOn, groupBy, findIndex )
import Data.Function( on )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query
import Backend.Typed.Layout( CT(..), layout, leaves )

type H a = M (Env,Gamma) NameSupply a

peepholeProgram :: Program -> (Program,[String])
peepholeProgram prog = (prog{ progDefs = map fst results },concatMap snd results)
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
  | Load{} <- e = do
      (_,g) <- ask
      let (ls,b) = loadRun e
      ts <- liftE (mapM (inferVar g . fst) ls)
      b' <- bind (zip (map snd ls) ts) (expr b)
      return (foldr (uncurry Load) b' (inMemoryOrder g ls))
  -- a later pass may remove every use (DropSpec removes the drop of a field that reuse overwrites)
  | Just (x,b) <- projection e, not (any (`within` x) (fvE b)) = expr b
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
  Join j tvs ps a b -> Join j tvs ps <$> bind [(x,V t) | (x,_,t) <- ps] (expr a) <*> expr b
  UnboxRu z r b -> do
    (env,g) <- ask
    g' <- liftE (unboxRuGamma g z r)
    UnboxRu z r <$> local (const (env,g')) (expr b)
  Lock z c b -> do
    (env,g) <- ask
    g' <- liftE (lockGamma g z c)
    Lock z c <$> local (const (env,g')) (expr b)
  IsUnique x a b -> do
    (env,g) <- ask
    IsUnique x <$> local (const (env,uniqueGamma g x)) (expr a) <*> expr b
  Dup x y b -> do
    (_,g) <- ask
    t <- liftE (inferVar g x >>= dupType x)
    Dup x y <$> bind [(y,t)] (expr b)
  IfFull r a b -> do
    (_,g) <- ask
    rt <- liftE (inferVar g r)
    case rt of
      V (VReuse _ n p) -> IfFull r <$> bind [(r,V (VReuse Full n p))] (expr a) <*> expr b
      _ -> fail "peephole: test of a non-credit"
  _ -> descendE pure value (\_ -> expr) e

projection :: VExpr -> Maybe (Path,VExpr)
projection (Fst _ _ x b) = Just (x,b)
projection (Snd _ _ x b) = Just (x,b)
projection _ = Nothing

-- A run of loads, each a copy of a value's bits; its references are still held by the block.
loadRun :: VExpr -> ([(Path,Path)], VExpr)
loadRun (Load x y e) = let (ls,e') = loadRun e in ((x,y) : ls, e')
loadRun e = ([], e)

-- The loads of a run are independent (a load binder is not a place), so the loads of
-- adjacent places of one box can read it in memory order, for clang to pair the reads (`ldp`).
inMemoryOrder :: Gamma -> [(Path,Path)] -> [(Path,Path)]
inMemoryOrder g = concatMap (sortOn (slot . fst)) . groupBy ((==) `on` (box . fst))
  where box x = placeOf x <$ slot x
        slot x = do (i,w) <- firstLeaf g x
                    CProd _ fs <- Just (layout w)
                    findIndex ((== i) . fst) fs

-- the first leaf of a place in the contents of its box, and the type of the contents
firstLeaf :: Gamma -> Path -> Maybe (Int,VType)
firstLeaf g x@(Path r ss)
  = case reverse ss of
      SContents : _ | Right (V w) <- inferVar g x -> Just (0,w)
      SFst : rest -> firstLeaf g (Path r (reverse rest))
      SPack : rest -> firstLeaf g (Path r (reverse rest))
      SSnd : rest -> do let p = Path r (reverse rest)
                        Right (V (VProd a _)) <- Just (inferVar g p)
                        (i,w) <- firstLeaf g p
                        Just (i + length (leaves a),w)
      _ -> Nothing

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
  Memoize c d k w -> [(w,Memoize c d k)]
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

