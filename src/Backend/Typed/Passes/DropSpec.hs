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
  only read; an owned read of a scalar becomes a borrowed one and a drop), and the drops of parts among them move into the unique branch, while the
  shared branch duplicates only the other parts:

    let^ (z.contents.fst, z.contents.snd) = z.contents in
    let r = if-unique z then (let @ r' = z in drop z.contents.fst; ret r')
            else (dup z.contents.snd; drop z; ret no-reuse n [k; z.contents : V])
    in free r; e'
-}
module Backend.Typed.Passes.DropSpec( dropSpecProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( guard, foldM )
import Data.List( nub )
import Data.Maybe( listToMaybe )
import Backend.Typed.Types( inst )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env, Gamma, envOf, bindAll, inferVar, inferAVar, inferV, altTypes, unboxRuBinds, boxContents, reuseSize, trivialTy )

type D a = M (Env,Gamma) NameSupply a

fresh :: String -> D Path
fresh s = state (freshPathFrom ("ds" ++ s))

bind :: [(Path,Ty)] -> D a -> D a
bind bs = local (\(env,g) -> (env,bindAll bs g))

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
  = do (env,g) <- ask
       case transferOf env g expr of
         Just (z,p,n,e) -> specialize z p n e
         Nothing -> dsPlain expr

-- Recognize the derived duplication of whole box contents followed by their box's
-- drop. Borrowed destructurings may already be in scope or still wrap the dups.
transferOf :: Env -> Gamma -> VExpr -> Maybe (Path,Path,Int,VExpr)
transferOf env g expr = do
  x <- firstRead expr
  listToMaybe [ (z,p,n,e)
              | p@(Path r ss) <- reverse (prefixes x ++ [x]), not (null ss), last ss == SContents
              , let z = Path r (init ss)
              , Right s <- [inferAVar g z >>= boxContents]
              , Right n <- [reuseSize s]
              , Just (Drop y e) <- [stripDup env g (scopeOf (M.keys g)) p (V s) expr]
              , y == z ]
  where
    firstRead (Dup x _) = Just x
    firstRead (Let _ VUnit e _) = firstRead e
    firstRead e = do ds <- destructVOf e
                     case dsScrut ds of Var x -> Just x; _ -> Nothing

-- Strip precisely one structural duplication, whose borrowed destructurings
-- remain local to its unit-valued let.
stripDup :: Env -> Gamma -> Scope -> Path -> Ty -> VExpr -> Maybe VExpr
stripDup env g scope x t expr
  | trivialTy env t = Just expr
  | otherwise = case t of
      A _ -> leaf
      V (VCtx _ _ _) -> leaf
      V (VPtr a) -> sequenced $ frame [child x SDeref] (VPtr a) $ \sc e -> stripDup env g sc (child x SDeref) (A a) e
      V v@VProd{} -> let fields = [f | f@(_,_,s) <- fieldsAt x v, not (trivialTy env (V s))]
                     in sequenced $ projections fields (\sc e -> foldM (\rest (y,_,s) -> stripDup env g sc y (V s) rest) e fields) scope
      V (VSum ts) -> do
        Let _ VUnit bound rest <- Just expr
        case [i | i <- [0..length ts-1], M.member (child x (SInjV i)) scope] of
          (i:_) -> unit (child x (SInjV i)) (ts !! i) bound
          [] -> do CaseV Borrowed (Var z) alts <- Just bound
                   guard (z == x && length alts == length ts)
                   sequence_ [guard (y == child x (SInjV i)) >> unit y s e | (i,((y,e),s)) <- zip [0..] (zip alts ts)]
        return rest
      V (VExists tvs s) -> do
        Let _ VUnit bound rest <- Just expr
        let y = child x SPack
        if M.member y scope
          then do V ty <- M.lookup y g
                  unit y ty bound
          else do Unpack Borrowed (Var z) bs w body <- Just bound
                  guard (z == x && w == y && length bs == length tvs)
                  unit y (inst tvs (map AVar bs) s) body
        return rest
      _ -> Nothing
  where
    leaf = case expr of Dup y e | x == y -> Just e; _ -> Nothing
    projections [] k sc bound = k sc bound
    projections ((y,_,_):fs) k sc bound
      | M.member y sc = projections fs k sc bound
      | otherwise = do ds <- destructVOf bound
                       guard (dsMode ds == Borrowed && dsScrut ds == Var x)
                       [([z],e)] <- Just (dsAlts ds)
                       guard (z == y)
                       projections fs k (M.insert y Nothing sc) e
    unit y s e = do Ret UnitV <- stripDup env g (M.insert y Nothing scope) y (V s) e
                    return ()
    sequenced k = do Let _ VUnit bound rest <- Just expr
                     Ret UnitV <- k bound
                     return rest
    frame ys s k bound
      | all (`M.member` scope) ys = k scope bound
      | Just ds <- destructVOf bound, dsMode ds == Borrowed, dsScrut ds == Var x
      , [(zs,e)] <- dsAlts ds, zs == ys
      , correct s bound = k (M.union (scopeOf ys) scope) e
      | otherwise = Nothing
    correct VPtr{} Deref{} = True
    correct _ _ = False

specialize :: Path -> Path -> Int -> VExpr -> D VExpr
specialize z p n e
  = do (_,g) <- ask
       let (frames,dead,others,rest) = taken p e
           -- Scheduled projections may already be in scope before the transfer.
           -- They expose the same parts as the leading destructurings in `e`.
           bound = S.toList (M.keysSet g `S.union` S.fromList
                     (concat [xs | f <- frames, Just ds <- [destructOf f], (xs,_) <- dsAlts ds]))
       case cover bound (map canonical dead) p of
         Just live | not (null dead) -> transfer frames live dead (others rest)
         _ -> transfer [] [p] [] e
  where
    transfer frames live dead cont
      = under frames $
        do (env,g) <- ask
           s <- liftE (inferAVar g z >>= boxContents)
           r <- fresh "r"
           let r' = child z SCredit
               payload = Just (Contents (Just (boxTag z)) (Var p) s)
               t = VReuse MaybeEmpty n payload
               unique = UnboxRu z r' (foldr Drop (Ret (Var r')) dead)
           ks <- mapM (\x -> do
                          tx <- liftE (inferVar g x)
                          dupValue (trivialTy env) (fresh "u") (scopeOf (M.keys g)) x tx) live
           let shared = compose ks (Drop z (Ret (NoReuse n payload)))
           cont' <- bind [(r,V t)] (dsE cont)
           return (Let r t (IsUnique z unique shared) (Free r cont'))

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
      -- an owned read of a scalar consumes it: it moves as a read and a drop
      Unscalar m w x e | owning m, w `within` p
        -> let (fs,ds,k,r) = taken p e in (Unscalar Borrowed w x e:fs,w:ds,k,r)
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
-- a dead part is split into its parts only when all of them are available.
cover :: [Path] -> [Path] -> Path -> Maybe [Path]
cover bound dead v
  | any (v `within`) dead = Just []
  | any (`within` v) dead = case immediate of
                              [] -> Nothing
                              xs -> do guard (complete (map (stepsFrom v) xs))
                                       concat <$> mapM (cover bound dead) xs
  | otherwise = Just [v]
  where
    -- the bound parts of `v` with no bound part between them and `v` (a projection binds a
    -- field at several steps)
    below = [x | x <- bound, x `within` v, x /= v]
    immediate = [x | x <- below, not (any (\y -> y /= x && x `within` y) below)]
    -- A projection exposes only one field; the parts must make up all of `v`.
    complete sss
      | [] `elem` sss = all null sss
      | otherwise = all part heads
      where
        heads = nub (map head sss)
        part s = maybe True (`elem` heads) (sibling s) && complete [ss | (t:ss) <- sss, t == s]

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
