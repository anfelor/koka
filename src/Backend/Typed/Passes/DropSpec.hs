-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Drop specialization (after Perceus, before reuse).

  Perceus takes the contents of a box `z` that it gives up by duplicating them and
  dropping the box:

    dup z.contents; drop z; e

  If the box is unique, the dup and the drop cancel out: its contents are taken without
  reference counting, and its block becomes a reuse credit, which still contains them:

    let r : ◇n[k; z.contents : V] = if-unique z then (let @ r' = z in ret r')
                                    else (dup z.contents; drop z; ret no-reuse n [k; z.contents : V])
    in free r; e

  Both branches leave `z.contents` owned (see `[unbox-ru]`). The description of `r` names
  the contents and the tag k of the block, which follows from the path of `z`. The
  empty credit of the shared branch has the same description, so that the branches agree on
  it. The shared branch is the original code. Freeing the credit releases the block, unless
  `Reuse` uses it for an allocation in `e`.

  As in Koka's Parc, the parts of the contents that `e` drops right away are not duplicated
  at all. The destructurings of the contents at the start of `e` move before the test (they
  only read), and the drops of parts among them move into the unique branch, while the
  shared branch duplicates only the other parts:

    let^ (z.contents.fst, z.contents.snd) = z.contents in
    let r = if-unique z then (let @ r' = z in drop z.contents.fst; ret r')
            else (dup z.contents.snd; drop z; ret no-reuse n [k; z.contents : V])
    in free r; e'
-}
module Backend.Typed.Passes.DropSpec( dropSpecProgram ) where

import qualified Data.Map as M
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env, Gamma, envOf, bindAll, inferVar, inferAVar, inferV, altTypes, unboxRuBinds, boxContents, reuseSize )

type D a = M (Env,Gamma) Int a

fresh :: String -> D Path
fresh s = state (\n -> (root (newHiddenName ("ds" ++ s ++ show n)), n+1))

bind :: [(Path,Ty)] -> D a -> D a
bind bs = local (\(env,g) -> (env,bindAll bs g))

dropSpecProgram :: Program -> (Program,[String])
dropSpecProgram prog
  = let run d = case evalM (dsE (defBody d)) (envOf prog,params d) 0 of
                  Right e -> (d{ defBody = e },[])
                  Left err -> (d,[show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs prog))
    in (prog{ progDefs = defs },concat errs)
  where
    params DefFun{ defArgs = ps } = M.fromList [(x,V t) | (x,_,t) <- ps]
    params DefVal{} = M.empty

dsE :: VExpr -> D VExpr
dsE (Dup p (Drop z e))
  | p == child z SContents
  = do (_,g) <- ask
       s <- liftE (inferAVar g z >>= boxContents)
       case reuseSize s of
         Right n -> let (frames,dead,others,rest) = taken p e
                        bound = concat [xs | f <- frames, Just ds <- [destructOf f], (xs,_) <- dsAlts ds]
                    in case cover bound (map canonical dead) p of
                         Just live | not (null dead) -> transfer n frames live dead (others rest)
                         _ -> transfer n [] [p] [] e
         Left _ -> Dup p . Drop z <$> dsE e
  where
    transfer n frames live dead cont
      = under frames $
        do (_,g) <- ask
           s <- liftE (inferAVar g z >>= boxContents)
           r  <- fresh "r"
           r' <- fresh "r"
           let payload = Just (Contents (boxTag z) (Var p) s)
               t = VReuse n payload
               unique = UnboxRu z r' (foldr Drop (Ret (Var r')) dead)
               shared = foldr Dup (Drop z (Ret (NoReuse n payload))) live
           cont' <- bind [(r,V t)] (dsE cont)
           return (Let r t (IsUnique z unique shared) (Free r cont'))
dsE expr
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
dsE expr
  = case expr of
      Let x t e1 e2 -> Let x t <$> dsE e1 <*> bind [(x,V t)] (dsE e2)
      Join j ps e1 e2 -> Join j ps <$> bind [(x,V t) | (x,_,t) <- ps] (dsE e1) <*> dsE e2
      UnboxRu v r e -> do (_,g) <- ask
                          bs <- liftE (unboxRuBinds g v r)
                          UnboxRu v r <$> bind bs (dsE e)
      _ -> descendE pure dsV (\_ e -> dsE e) expr

-- The destructurings of parts of `p` at the start of an expression, the parts of `p` that it
-- drops among them, and its drops of other variables.
taken :: Path -> VExpr -> ([VExpr],[Path],K,VExpr)
taken p expr
  = case expr of
      Drop w e | w `within` p -> let (fs,ds,k,r) = taken p e in (fs,w:ds,k,r)
               | otherwise -> let (fs,ds,k,r) = taken p e in (fs,ds,Drop w . k,r)
      _ | Just ds <- destructOf expr, Var x <- dsScrut ds, x `within` p, dsMode ds /= Unique
        , [(_,e)] <- dsAlts ds, not (isLazy expr)
        -> let (fs,dd,k,r) = taken p e in (expr:fs,dd,k,r)
      _ -> ([],[],id,expr)
  where
    isLazy UnboxLazy{} = True
    isLazy _ = False

-- a destructuring form, with a variable as its scrutinee
destructOf :: VExpr -> Maybe (Destruct VVal)
destructOf expr
  = case destructAOf expr of
      Just ds -> Just ds{ dsScrut = Var (dsScrut ds), dsBuild = \m v es -> dsBuild ds m (varOf v) es }
      Nothing -> destructVOf expr

-- The parts of `v` that are not dead, where `bound` are the parts in scope: a variable with
-- a dead part is split into its parts.
cover :: [Path] -> [Path] -> Path -> Maybe [Path]
cover bound dead v
  | any (v `within`) dead = Just []
  | any (`within` v) dead = case [x | x <- bound, x `within` v, length (stepsFrom v x) == 1] of
                              [] -> Nothing
                              xs -> concat <$> mapM (cover bound dead) xs
  | otherwise = Just [v]

-- the destructurings `fs` (with one alternative each) around an expression in the scope of their binders
under :: [VExpr] -> D VExpr -> D VExpr
under [] k = k
under (f:fs) k
  | Just ds <- destructOf f
  = do (env,g) <- ask
       t <- case destructAOf f of
              Just da -> liftE (inferVar g (dsScrut da))
              Nothing -> V <$> liftE (inferV env g (dsScrut ds))
       [ts] <- liftE (altTypes env t f)
       let [(xs,_)] = dsAlts ds
       e <- bind (zip xs ts) (under fs k)
       return (dsBuild ds (dsMode ds) (dsScrut ds) [e])
under _ _ = fail "DropSpec.under: not a destructuring"

dsV :: VVal -> D VVal
dsV = descendV dsA dsV

dsA :: AVal -> D AVal
dsA (Lam ps r e) = Lam ps r <$> bind [(x,V t) | (x,_,t) <- ps] (dsE e)
dsA v = descendA pure dsA dsV v
