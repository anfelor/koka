-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Extraction of closed ground values (after Perceus and reuse).

  A function that builds a ground value (`Lidar.Ground`: literals, boxes, injections, tuples,
  and calls that the client folds) builds it afresh on every call. This pass moves such values
  into top-level values, which C generation writes as static data: every ground `let` and every
  maximal ground operand of non-ground code, if the value allocates (a box, a string, or a
  folded call) and has a pointer type without type variables. Each becomes a `DefVal`
  `f@closed<n>` whose body is a single value (or folded call): the extracted values it is built
  from appear as their own globals, the other ground values it is built from as their values.
  Structurally equal values share one global.

  The pass runs after `Reuse`, so a construction that takes a reuse credit (`box@r`) is not
  ground and stays: only fresh allocations move, and no allocation moves to a consumer that
  would have reused it. Every allocating ground value is in an owned position after Perceus, so
  it becomes `dup g`. The values that it consumed lose a consumption: a ground `let` whose
  occurrences were all in replaced values is removed, any other gets a `drop` in place of the
  consumption (on a static block if it was extracted).

  Ground values cannot have effects or diverge. The pass also extracts closed calls: calls with
  ground arguments of functions that the client declares extractable (pure; an action takes
  the effect token, which is never ground). Such a global is initialised on demand, at its
  first use, as is every global built from one; its body passes an extracted argument as
  `dup g` to an owned parameter and as `g` to a borrowed one. A call that refers to the
  recursive group of its function, directly or through its arguments, is not extracted, as
  its initialisation could need itself. The extracted values refer to no global but each other
  and the functions they call, and come first in the program, so a client that cannot write
  one statically can initialise it before any other value.
-}
module Lidar.Passes.Closed( closedProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( foldM, zipWithM )
import Control.Monad.State( State, runState, state )
import Data.Functor.Const( Const(..) )
import Data.Graph( flattenSCC, stronglyConnComp )
import Data.Functor.Identity( Identity(..) )
import Data.List( sortOn )
import Data.Monoid( Any(..) )
import Lidar.Name
import Lidar.Syntax
import Lidar.Types( Types(ftv), isPtr )
import Lidar.Traversal( descendA, descendV, descendAll, descendE, fvE, fvV, globalsE, globalsV, mapA, mapV )
import Lidar.Ground( GroundBind(..), groundV )
import Lidar.Env( Env, envOf, M, ask, evalM )
import Lidar.Query( Gamma )
import Lidar.Passes.Common( paramModes, trivialTy, defGamma, typedChildren, NameSupply, dropValue, freshFor, freshPathFrom, scopeOf )

-- | Extract the closed ground values and calls of the functions of a program, given the
-- functions whose calls the client folds and those whose calls it can initialise on demand.
closedProgram :: (Name -> Bool) -> (Name -> Bool) -> Program -> (Program,[String])
closedProgram foldable extractable prog
  = ( prog{ progSigs = M.union (progSigs prog) (M.fromList [(x,SigVal [] t) | DefVal x _ _ t _ <- new])
          , progDefs = new ++ map fst results }
    , concatMap snd results )
  where
    (results,st) = runState (mapM closedDef (progDefs prog)) (St M.empty [] 0 S.empty)
    new = reverse (stDefs st)
    groups = recGroups prog
    closedDef def = case def of
                      DefFun{} -> do let group = M.findWithDefault S.empty (defName def) groups
                                     r <- closedBody (envOf prog) foldable (closedCall group) group def
                                     return (either (\err -> (def,[show (defName def) ++ ": " ++ err]))
                                                    (\body -> (def{ defBody = body },[])) r)
                      DefVal{} -> return (def,[])
    closedCall group g tys = extractable g && not (S.member g group) && all (null . ftv) tys

-- the recursive group of each definition: its strongly connected component in the graph of
-- the globals that definitions refer to
recGroups :: Program -> M.Map Name (S.Set Name)
recGroups prog
  = M.fromList [ (f,group) | scc <- stronglyConnComp [(d,defName d,S.toList (globalsE (defBody d))) | d <- progDefs prog]
                           , let group = S.fromList (map defName (flattenSCC scc)), f <- S.toList group ]

-- the globals made so far by their bodies, the new definitions (last first), the next number,
-- and the new globals initialised on demand
data St = St{ stKeys :: M.Map String Name, stDefs :: [Def], stNext :: Int, stOnDemand :: S.Set Name }

-- the ground `let`s of a function: their types, values, and index in the order of binding
type Grounds = M.Map Path (VType,GroundBind,Int)

-- the variables that the ground `let`s of folded calls drop after the call
type Dropped = M.Map Path [Path]

closedBody :: Env -> (Name -> Bool) -> (Name -> [AType] -> Bool) -> S.Set Name -> Def -> State St (Either String VExpr)
closedBody env foldable closedCall group def
  = do -- the extracted lets, in the order of binding, so that each finds its dependencies
       letNames <- foldM (\m x -> case letBody env foldable gs m x of
                                    Just b -> do g <- global foldable f b (fst3 (gs M.! x))
                                                 return (M.insert x g m)
                                    Nothing -> return m)
                         M.empty (sortOn index (filter (extractable gs) (M.keys gs)))
       let (body',operands) = extractOperands gs letNames (defBody def)
       opNames <- mapM (\(_,v,t) -> global foldable f (Ret v) t) operands
       let ops = M.fromList (zip (map placeholder [0 ..]) (zip opNames [v | (v,_,_) <- operands]))
           kept = keptLets gs letNames body'
       return (evalM (rewrite env gs dropped kept letNames ops body') (env,defGamma def) (freshFor def))
  where
    f = defName def
    (gs,dropped) = groundLets foldable closedCall group (defBody def)
    index x = let (_,_,i) = gs M.! x in i

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a

rootOf :: Path -> Path
rootOf (Path x _) = root x

-- The ground lets of a body, in the order of binding (with lambdas): a let is ground if its
-- value is, or if it calls a folded function with ground arguments (then drops the arguments
-- that it passes to borrowed parameters), given those bound before. A closed call (of an
-- extractable function, given its type arguments) counts as a folded call unless its arguments
-- refer to the recursive group, also through the values of the ground lets they use.
groundLets :: (Name -> Bool) -> (Name -> [AType] -> Bool) -> S.Set Name -> VExpr -> (Grounds,Dropped)
groundLets foldable closedCall group body = (grounds,drops)
  where
    (grounds,drops,_) = foldl add (M.empty,M.empty,S.empty) (zip [0..] (lets body))
    -- the ground lets so far, their drops, and those that refer to the recursive group
    add (gs,ds,recs) (i,(x,t,e1))
      = let ground v = groundV S.empty (M.keysSet gs) v
            refers v = not (S.disjoint group (globalsV v)) || any (`S.member` recs) (S.toList (fvV v))
            mark vs = if any refers vs then S.insert x recs else recs
        in case e1 of
             Ret v | ground v -> (M.insert x (t,GValue v,i) gs,ds,mark [v])
             _ | Just (g,tys,vs,zs) <- callThenDrops e1, all ground vs && all (`M.member` gs) zs
               , foldable g || (closedCall g tys && not (any refers vs))
                 -> (M.insert x (t,GCall g tys vs,i) gs, M.insert x zs ds, mark vs)
             _ -> (gs,ds,recs)
    lets e = case e of
               Let x t e1 e2 | Just _ <- callThenDrops e1 -> (x,t,e1) : lets e2
               Let x t e1 _ -> (x,t,e1) : descend e
               _ -> descend e
    descend e = concat (getConst (descendAll (\_ e' -> Const [lets e']) e))

-- A call, or a call bound to a variable, then drops of variables (as Perceus drops arguments at
-- borrowed parameters after the call), then the variable: the call and the dropped variables.
callThenDrops :: VExpr -> Maybe (Name,[AType],[VVal],[Path])
callThenDrops e
  = case e of
      Call g tys vs -> Just (g,tys,vs,[])
      Let r _ (Call g tys vs) rest -> do zs <- drops r rest
                                         Just (g,tys,vs,zs)
      _ -> Nothing
  where
    drops r rest = case rest of
                     Ret (Var r') | r' == r -> Just []
                     Drop z e' -> (z:) <$> drops r e'
                     Deref (Var z) y (Drop y' e') | y == y' -> (z:) <$> drops r e'
                     _ -> Nothing

bindVals :: GroundBind -> [VVal]
bindVals b = case b of
               GValue v -> [v]
               GCall _ _ vs -> vs

-- the ground variables of a ground let's value
depsOf :: Grounds -> Path -> [Path]
depsOf gs x = let (_,b,_) = gs M.! x in S.toList (S.unions (map fvV (bindVals b)))

-- A ground let is a candidate for extraction if it allocates and has a pointer type without
-- type variables, as have the lets it is built from.
extractable :: Grounds -> Path -> Bool
extractable gs x = isPtr (fst3 (gs M.! x)) && closedTypes gs [x] && allocates gs (Var x)

closedTypes :: Grounds -> [Path] -> Bool
closedTypes gs xs = all (\y -> null (ftv (fst3 (gs M.! y)))) (S.toList (reach gs xs))

-- the ground lets that the given ones are built from, including themselves
reach :: Grounds -> [Path] -> S.Set Path
reach gs = go S.empty
  where
    go seen [] = seen
    go seen (x:xs)
      | S.member x seen = go seen xs
      | otherwise = go (S.insert x seen) (depsOf gs x ++ xs)

-- whether building a ground value allocates
allocates :: Grounds -> VVal -> Bool
allocates gs val
  = case val of
      Var x -> case M.lookup x gs of
                 Just (_,GValue v,_) -> allocates gs v
                 Just (_,GCall{},_) -> True
                 Nothing -> False
      Ptr _ a -> allocatesA a
      _ -> getAny (getConst (descendV (Const . Any . allocatesA) (Const . Any . allocates gs) val))
  where
    allocatesA a = case a of
                     Box _ -> True
                     Constant _ -> True
                     _ -> getAny (getConst (descendA (const (Const (Any False))) (Const . Any . allocatesA) (Const . Any . allocates gs) a))

-- The value of a ground value in the body of a global: the extracted lets it is built from as
-- (owned references to) their globals, the other ground lets as their values. Nothing if it
-- needs a folded call that is not extracted.
expand :: Grounds -> M.Map Path Name -> VVal -> Maybe VVal
expand gs names = go
  where
    go val = case val of
               Var x | Just g <- M.lookup x names -> Just (DupV (Glob g []))
                     | Just (_,GValue v,_) <- M.lookup x gs -> go v
                     | otherwise -> Nothing
               DupV v -> go v
               _ -> descendV goA go val
    goA = descendA pure goA go

-- The body of the global of a ground let, given the globals of the lets extracted before. A
-- closed call passes an extracted value to a borrowed parameter as its global (without `dup`),
-- and to a unique one nothing that allocates; Nothing if it cannot.
letBody :: Env -> (Name -> Bool) -> Grounds -> M.Map Path Name -> Path -> Maybe VExpr
letBody env foldable gs names x
  = case gs M.! x of
      (_,GValue v,_) -> Ret <$> expand gs names v
      (_,GCall g tys vs,_)
        | foldable g -> Call g tys <$> mapM (expand gs names) vs
        | otherwise -> Call g tys <$> zipWithM arg (paramModes env g (length vs)) vs
  where
    arg m v = case (m,v) of
                (Owned,_) -> expand gs names v
                _ | not (allocates gs v) -> expand gs names v
                (Borrowed,Var y) | Just g <- M.lookup y names -> Just (Glob g [])
                _ -> Nothing

-- The global of an extracted value with a body and a type: an existing one with the same body,
-- or a new one, initialised on demand if its body calls a function that is not folded or reads
-- a global initialised on demand.
global :: (Name -> Bool) -> Name -> VExpr -> VType -> State St Name
global foldable f body t
  = state $ \st ->
      case M.lookup key (stKeys st) of
        Just g -> (g,st)
        Nothing -> let g = makeHiddenName ("closed" ++ show (stNext st)) f
                       onDemand = case body of
                                    Call h _ _ | not (foldable h) -> True
                                    _ -> not (S.disjoint (stOnDemand st) (globalsE body))
                   in (g, st{ stKeys = M.insert key g (stKeys st)
                            , stDefs = DefVal g [] (if onDemand then OnDemand else AtLoad) t body : stDefs st
                            , stNext = stNext st + 1
                            , stOnDemand = (if onDemand then S.insert g else id) (stOnDemand st) })
  where
    key = show body ++ show t

-- A placeholder for the global of the i-th extracted operand.
placeholder :: Int -> Name
placeholder i = newHiddenName ("closed-operand" ++ show i)

-- The maximal ground operands of non-ground code that allocate and have a closed pointer type
-- (a string, or a pointer to a block), replaced by placeholders, in order, with their values
-- in the body of their global and their types.
extractOperands :: Grounds -> M.Map Path Name -> VExpr -> (VExpr,[(VVal,VVal,VType)])
extractOperands gs names body = (body',reverse ops)
  where
    (body',ops) = runState (goE body) []
    goE :: VExpr -> State [(VVal,VVal,VType)] VExpr
    goE e = case e of
              Let x t e1 e2 | M.member x gs -> Let x t e1 <$> goE e2
              _ -> descendE pure goV (\_ e' -> goE e') e
    goV :: VVal -> State [(VVal,VVal,VType)] VVal
    goV v = case operandType v of
              Just t | groundV S.empty (M.keysSet gs) v
                       && allocates gs v && closed v t
                     , Just v' <- expand gs names v
                -> state (\os -> (Glob (placeholder (length os)) [], (v,v',t) : os))
              _ -> descendV goA goV v
    goA :: AVal -> State [(VVal,VVal,VType)] AVal
    goA a = case a of
              Lam ps r e -> Lam ps r <$> goE e
              _ -> descendA pure goA goV a
    closed v t = null (ftv t) && closedTypes gs (S.toList (fvV v))

operandType :: VVal -> Maybe VType
operandType v = case v of
                  Ptr t _ -> Just (VPtr t)
                  _ -> Nothing

-- The ground lets that stay: those that non-ground code still uses after the extraction of its
-- operands, and the values that those not extracted are built from.
keptLets :: Grounds -> M.Map Path Name -> VExpr -> S.Set Path
keptLets gs names body = go S.empty (S.toList used)
  where
    used = S.filter (`M.member` gs) (S.map rootOf (fvE (strip body)))
    go seen [] = seen
    go seen (x:xs)
      | S.member x seen = go seen xs
      | M.member x names = go (S.insert x seen) xs
      | otherwise = go (S.insert x seen) (depsOf gs x ++ xs)
    -- the body without its ground lets
    strip e = case e of
                Let x _ _ e2 | M.member x gs -> strip e2
                _ -> runIdentity (descendAll (\_ e' -> Identity (strip e')) e)

-- the variables that a value consumes: those not under a `dup`
consumed :: VVal -> [Path]
consumed val
  = case val of
      Var x -> [x]
      DupV _ -> []
      _ -> getConst (descendV (Const . consumedA) (Const . consumed) val)
  where
    consumedA a = getConst (descendA (const (Const [])) (Const . consumedA) (Const . consumed) a)

-- the placeholders in a value, outside lambdas
placeholdersIn :: VVal -> [Name]
placeholdersIn val
  = case val of
      Glob p [] -> [p]
      _ -> getConst (descendV (Const . inA) (Const . placeholdersIn) val)
  where
    inA a = getConst (descendA (const (Const [])) (Const . inA) (Const . placeholdersIn) a)

type R = M (Env,Gamma) NameSupply

-- The body with the extracted lets binding their globals, the lets that are not kept removed,
-- and the globals of the extracted operands, with a drop of each kept let that lost a
-- consumption before the node that lost it.
rewrite :: Env -> Grounds -> Dropped -> S.Set Path -> M.Map Path Name -> M.Map Name (Name,VVal) -> VExpr -> R VExpr
rewrite env gs dropped kept letNames ops = go
  where
    go e = case e of
             Let x t _ e2 | Just (_,b,_) <- M.lookup x gs ->
               case M.lookup x letNames of
                 _ | not (S.member x kept) -> lose (consumedBy x b) =<< go e2
                 Just g -> lose (consumedBy x b) =<< typedChildren go (Let x t (Ret (DupV (Glob g []))) e2)
                 Nothing -> typedChildren go e
             _ -> do let vals = getConst (descendE (const (Const [])) (\v -> Const [v]) (\_ _ -> Const []) e)
                         lost = [v | p <- concatMap placeholdersIn vals, Just (_,v) <- [M.lookup p ops]]
                     lose lost =<< typedChildren go (runIdentity (descendE pure (Identity . replaceV) (\_ e' -> Identity e') e))
    -- the values that a ground let consumes: a folded call's arguments at owned parameters and
    -- the variables it drops after the call
    consumedBy x b = case b of
                       GValue v -> [v]
                       GCall g _ vs -> [v | (m,v) <- zip (paramModes env g (length vs)) vs, owning m]
                                       ++ map Var (M.findWithDefault [] x dropped)
    replaceV v = case v of
                   Glob p [] | Just (g,_) <- M.lookup p ops -> DupV (Glob g [])
                   _ -> mapV replaceA replaceV v
    replaceA = mapA id replaceA replaceV
    -- drop the kept lets that the removed values consumed
    lose :: [VVal] -> VExpr -> R VExpr
    lose vals e = foldM dropLet e [z | z <- concatMap consumed vals, S.member z kept]
    -- Drop a let through a fresh variable, as a let can lose several consumptions in one scope.
    dropLet e z
      | trivialTy env (V t) = return e
      | otherwise = do (_,g) <- ask
                       y <- fresh
                       Let y t (Ret (Var z)) <$> dropValue (trivialTy env) fresh (scopeOf (M.keys g)) y (V t) e
      where t = fst3 (gs M.! z)
    fresh = state (freshPathFrom "cd")
