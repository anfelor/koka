-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Drop specialization (after Perceus, before reuse).

  Perceus destructures a box that is still needed by borrowing its contents,
  duplicating them and then dropping the box:

    let^ box p = z in let y = dup p in drop z; e

  If the box is unique, the dup and the drop cancel out: its contents are taken
  without reference counting and its block becomes a reuse credit, which still contains them:

    let (y, r : ◇n[k; y : V]) = if-unique z then let box y @ r' = z in ret (y, r')
                                            else let^ box y = z in let y' = dup y in drop z; ret (y', no-reuse n [k; y : V])
    in free r; e

  The description of `r` names the `y` of the branches, of which the `y` it binds is an alias
  (see `Linear`), and the tag k of the block, which follows from the position of `z` (see
  `[unbox-ru]`). The empty credit of the shared branch has the same description, so that the
  branches agree on it.

  As in Koka's Parc, the parts of `y` that `e` drops right away are not duplicated at all: the
  destructuring of `y` at the start of `e` (renames, owned unpairs, and drops of its pointer
  parts) moves into both branches. The unique branch drops the dead parts, the shared branch
  duplicates only the live ones, and both return the live parts:

    let ((a, b), r : ◇n[k; (d, (a, b)) : V]) = if-unique z then let box y @ r' = z in let (d, (a, b)) = y in drop d; ret ((a, b), r')
                                  else let^ box y = z in let^ (d, (a, b)) = y in
                                       let a' = dup a in let b' = dup b in drop z; ret ((a', b'), no-reuse n [k; (d, (a, b)) : V])
    in free r; e'

  The shared branch is the original code. Freeing the credit releases the block, unless
  `Reuse` uses it for an allocation in `e`.
-}
module Backend.Typed.Passes.DropSpec( dropSpecProgram ) where

import qualified Data.Map as M
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env, Gamma, envOf, bindAll, inferVar, inferV, altTypes, unboxRuBinds, reuseSize )

type D a = M (Env,Gamma) Int a

fresh :: String -> D Name
fresh s = state (\n -> (newHiddenName ("ds" ++ s ++ show n), n+1))

bind :: [(Name,Ty)] -> D a -> D a
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
dsE (Unbox Borrowed z p (Let y s (Ret (DupV (Var p'))) (Drop z' e)))
  | p == p', z == z', Right n <- reuseSize s
  = do (_,g) <- ask
       tz <- liftE (inferVar g z)
       let (parts,rest) = case taken (Leaf y s) e of
                            (t,e') | hasDead t -> (t,e')
                            _ -> (Leaf y s, e)
           x = nameOf parts
           live = leaves parts
       q  <- fresh "q"
       r  <- fresh "r"
       r' <- fresh "r"
       copies <- mapM copy live
       (l,unpack) <- bindTuple (map fst live)
       kept <- dropDead parts (Ret (Pair (tuple (map (Var . fst) live)) (Var r')))
       let payload = Just (Contents (offset (position tz) + 1) (described parts) s)
           shared = Unbox Borrowed z x (destructure Borrowed parts (compose (map snd copies)
                      (Drop z (Ret (Pair (tuple (map fst copies)) (NoReuse n payload))))))
       rest' <- bind ((r,V (VReuse n payload)) : [(x',V t) | (x',t) <- live]) (dsE rest)
       return (Let q (VProd (tupleType (map snd live)) (VReuse n payload))
                 (IsUnique z (UnboxRu z x r' (destructure Owned parts kept)) shared)
                 (Unpair Owned (Var q) l r (unpack (Free r rest'))))
  where
    copy (x,t) | isTrivial (V t) = return (Var x, id)
               | otherwise = do x' <- fresh "y"
                                return (Var x', Let x' t (Ret (DupV (Var x))))
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
      Dup x y e -> do (_,g) <- ask
                      t <- liftE (inferVar g x)
                      Dup x y <$> bind [(y,t)] (dsE e)
      UnboxRu v x r e -> do (_,g) <- ask
                            bs <- liftE (unboxRuBinds g v x r)
                            UnboxRu v x r <$> bind bs (dsE e)
      _ -> descendE pure dsV (\_ e -> dsE e) expr

-- The parts of a payload: a part that is still needed, a pointer that is dropped, or a pair
-- that is destructured.
data Parts = Leaf Name VType | Dead Name VType | Node Name Parts Parts

nameOf :: Parts -> Name
nameOf (Leaf x _) = x
nameOf (Dead x _) = x
nameOf (Node x _ _) = x

-- the payload in terms of its parts, which the credit of its block describes
described :: Parts -> VVal
described (Node _ a b) = Pair (described a) (described b)
described parts = Var (nameOf parts)

leaves :: Parts -> [(Name,VType)]
leaves (Leaf x t) = [(x,t)]
leaves (Dead _ _) = []
leaves (Node _ a b) = leaves a ++ leaves b

hasDead :: Parts -> Bool
hasDead (Leaf _ _) = False
hasDead (Dead _ _) = True
hasDead (Node _ a b) = hasDead a || hasDead b

-- Replace the leaf `x`.
at :: Name -> (VType -> Maybe Parts) -> Parts -> Maybe Parts
at x f parts
  = case parts of
      Leaf y t | x == y -> f t
      Node y a b -> case at x f a of
                      Just a' -> Just (Node y a' b)
                      Nothing -> Node y a <$> at x f b
      _ -> Nothing

-- Take the destructuring of a payload from the start of its continuation: renames, owned
-- unpairs and drops of pointers among its parts, also behind drops of other variables.
taken :: Parts -> VExpr -> (Parts,VExpr)
taken parts expr
  = case expr of
      Let x _ (Ret (Var w)) e
        | Just parts' <- at w (Just . Leaf x) parts -> taken parts' e
      Unpair Owned (Var w) a b e
        | Just parts' <- at w (split w a b) parts -> taken parts' e
      Deref Owned (Var w) d (Drop d' e)
        | d == d', Just parts' <- at w (Just . Dead w) parts -> taken parts' e
      Drop x e -> Drop x <$> taken parts e
      _ -> (parts,expr)
  where
    split w a b (VProd s t) = Just (Node w (Leaf a s) (Leaf b t))
    split _ _ _ _ = Nothing

destructure :: Mode -> Parts -> K
destructure m (Node x a b) = Unpair m (Var x) (nameOf a) (nameOf b) . destructure m a . destructure m b
destructure _ _ = id

dropDead :: Parts -> VExpr -> D VExpr
dropDead (Dead x t) e = dropValue (fresh "d") x (V t) e
dropDead (Node _ a b) e = dropDead b e >>= dropDead a
dropDead (Leaf _ _) e = return e

tuple :: [VVal] -> VVal
tuple [] = UnitV
tuple vs = foldr1 Pair vs

tupleType :: [VType] -> VType
tupleType [] = VUnit
tupleType ts = foldr1 VProd ts

-- Bind the names from a tuple: the name of the tuple and its destructuring.
bindTuple :: [Name] -> D (Name,K)
bindTuple [] = do u <- fresh "u"
                  return (u, id)
bindTuple [x] = return (x, id)
bindTuple (x:xs) = do l <- fresh "l"
                      (l',k) <- bindTuple xs
                      return (l, Unpair Owned (Var l) x l' . k)

dsV :: VVal -> D VVal
dsV = descendV dsA dsV

dsA :: AVal -> D AVal
dsA (Lam ps r e) = Lam ps r <$> bind [(x,V t) | (x,_,t) <- ps] (dsE e)
dsA v = descendA pure dsA dsV v
