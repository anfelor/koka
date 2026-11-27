-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Extraction of closed values (after Perceus and reuse).

  A function that builds a closed value builds it afresh on every call. A value is closed if it
  is ground (`Lidar.Ground`: literals, boxes, injections, tuples, and calls that the client
  folds), except that it may also read globals outside the recursive group of the function and
  build closures whose captures are closed. This pass moves such values into top-level values:
  every closed `let` and every maximal closed operand of non-closed code, if the value allocates
  (a box, a string, a closure with captures, or a folded call) and has a pointer type without
  type variables. Each becomes a `DefVal` `f@closed<n>` whose body is a single value (or folded
  call): the extracted values it is built from appear as their own globals, a `let` that reads a
  global as that global, and the other closed values it is built from as their values. A closure
  binds its captures that way at the start of its body, so that it has no captures left.
  Structurally equal values share one global. C generation writes a ground global as static
  data.

  The pass runs after `Reuse`, so a construction that takes a reuse credit (`box@r`) is not
  ground and stays: only fresh allocations move, and no allocation moves to a consumer that
  would have reused it. Every allocating ground value is in an owned position after Perceus, so
  it becomes `dup g`. The values that it consumed lose a consumption: a ground `let` whose
  occurrences were all in replaced values is removed, any other gets a `drop` in place of the
  consumption (on a static block if it was extracted).

  Closed values cannot have effects or diverge. The pass also extracts closed calls: calls with
  closed arguments of functions that the client declares extractable (pure; an action takes
  the effect token, which is never closed). The globals that closed values may read are also
  those the client declares extractable. A global is initialised on demand, at its first use,
  if it calls a function that is not folded or reads a global other than one of the values
  extracted before that are initialised when the program is loaded; its body passes an
  extracted argument (or a read global) as `dup g` to an owned parameter and as `g` to a
  borrowed one. A call that refers to the recursive group of its function, directly or through
  its arguments, is not extracted, as its initialisation could need itself, and a value never
  reads a global of the group. The extracted values come first in the program; those
  initialised when it is loaded read no global but each other, so a client that cannot write
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
import Data.Monoid( All(..), Any(..) )
import Lidar.Name
import Lidar.Syntax
import Lidar.Types( Types(ftv), isPtr )
import Lidar.Traversal( descendA, descendV, descendAll, descendE, fvA, fvE, fvV, globalsE, globalsV, mapA, mapV )
import Lidar.Ground( GroundBind(..), globsV )
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
                                     r <- closedBody (envOf prog) foldable extractable group def
                                     return (either (\err -> (def,[show (defName def) ++ ": " ++ err]))
                                                    (\body -> (def{ defBody = body },[])) r)
                      DefVal{} -> return (def,[])

-- the recursive group of each definition: its strongly connected component in the graph of
-- the globals that definitions refer to
recGroups :: Program -> M.Map Name (S.Set Name)
recGroups prog
  = M.fromList [ (f,group) | scc <- stronglyConnComp [(d,defName d,S.toList (globalsE (defBody d))) | d <- progDefs prog]
                           , let group = S.fromList (map defName (flattenSCC scc)), f <- S.toList group ]

-- the globals made so far by their bodies, the new definitions (last first), the next number,
-- and the new globals initialised when the program is loaded
data St = St{ stKeys :: M.Map String Name, stDefs :: [Def], stNext :: Int, stAtLoad :: S.Set Name }

-- the closed `let`s of a function: their types, values, and index in the order of binding
type Grounds = M.Map Path (VType,GroundBind,Int)

-- the variables that the closed `let`s of folded calls drop after the call
type Dropped = M.Map Path [Path]

closedBody :: Env -> (Name -> Bool) -> (Name -> Bool) -> S.Set Name -> Def -> State St (Either String VExpr)
closedBody env foldable extractable group def
  = do -- the globals that lets stand for: those they read, then the extracted lets, in the
       -- order of binding, so that each finds its dependencies
       letNames <- foldM (\m x -> case letBody env foldable gs m x of
                                    Just b -> do g <- global foldable f b (fst3 (gs M.! x))
                                                 return (M.insert x g m)
                                    Nothing -> return m)
                         (M.mapMaybe readOf gs) (sortOn index (filter (candidate gs) (M.keys gs)))
       let (body',operands) = extractOperands (readable extractable group) gs letNames (defBody def)
       opNames <- mapM (\(_,v,t) -> global foldable f (Ret v) t) operands
       let ops = M.fromList (zip (map placeholder [0 ..]) (zip opNames [v | (v,_,_) <- operands]))
           kept = keptLets gs letNames body'
       return (evalM (rewrite env gs dropped kept letNames ops body') (env,defGamma def) (freshFor def))
  where
    f = defName def
    (gs,dropped) = closedLets foldable extractable group (defBody def)
    index x = let (_,_,i) = gs M.! x in i
    readOf (_,b,_) = case b of
                       GValue (DupV (Glob g [])) -> Just g
                       _ -> Nothing

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a

rootOf :: Path -> Path
rootOf (Path x _) = root x

-- The closed lets of a body, in the order of binding (with lambdas): a let is closed if its
-- value is, or if it calls a folded function with closed arguments (then drops the arguments
-- that it passes to borrowed parameters), given those bound before. A closed call (of an
-- extractable function, given its type arguments) counts as a folded call unless its arguments
-- refer to the recursive group, also through the values of the closed lets they use.
closedLets :: (Name -> Bool) -> (Name -> Bool) -> S.Set Name -> VExpr -> (Grounds,Dropped)
closedLets foldable extractable group body = (grounds,drops)
  where
    (grounds,drops,_) = foldl add (M.empty,M.empty,S.empty) (zip [0..] (lets body))
    closedCall g tys = extractable g && not (S.member g group) && all (null . ftv) tys
    -- the closed lets so far, their drops, and those that refer to the recursive group
    add (gs,ds,recs) (i,(x,t,e1))
      = let ground v = closedV (readable extractable group) (M.keysSet gs) v
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

-- the globals that closed values may read: the extractable ones outside the recursive group
readable :: (Name -> Bool) -> S.Set Name -> Name -> Bool
readable extractable group g = extractable g && not (S.member g group)

-- | Whether a value is closed, given the globals it may read and the closed lets in scope: it is
-- ground (`Lidar.Ground.groundV`), except that it may read those globals (at closed types) and
-- build closures whose captures are closed lets.
closedV :: (Name -> Bool) -> S.Set Path -> VVal -> Bool
closedV readableGlob bound = cv
  where
    cv val = case val of
               Var x -> S.member x bound
               Glob g tys -> readableGlob g && all (null . ftv) tys
               Lit (LitFloat _) -> False
               Hole -> False
               Context _ _ -> False
               NoReuse _ _ -> False
               Null _ -> False
               _ -> getAll (getConst (descendV (Const . All . ca) (Const . All . cv) val))
    ca a = case a of
             Lam{} -> fvA a `S.isSubsetOf` bound
             Scalar _ -> False
             OpenCon{} -> False
             BoxAt{} -> False
             _ -> getAll (getConst (descendA (const (Const (All False))) (Const . All . ca) (Const . All . cv) a))

bindVals :: GroundBind -> [VVal]
bindVals b = case b of
               GValue v -> [v]
               GCall _ _ vs -> vs

-- the closed variables of a closed let's value
depsOf :: Grounds -> Path -> [Path]
depsOf gs x = let (_,b,_) = gs M.! x in S.toList (S.unions (map fvV (bindVals b)))

-- A closed let is a candidate for extraction if it allocates and has a pointer type without
-- type variables, as have the lets it is built from.
candidate :: Grounds -> Path -> Bool
candidate gs x = isPtr (fst3 (gs M.! x)) && closedTypes gs [x] && allocates gs (Var x)

closedTypes :: Grounds -> [Path] -> Bool
closedTypes gs xs = all (\y -> null (ftv (fst3 (gs M.! y)))) (S.toList (reach gs xs))

-- the closed lets that the given ones are built from, including themselves
reach :: Grounds -> [Path] -> S.Set Path
reach gs = go S.empty
  where
    go seen [] = seen
    go seen (x:xs)
      | S.member x seen = go seen xs
      | otherwise = go (S.insert x seen) (depsOf gs x ++ xs)

-- whether building a closed value allocates (a closure allocates if it has captures)
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
                     Lam{} -> not (S.null (fvA a))
                     _ -> getAny (getConst (descendA (const (Const (Any False))) (Const . Any . allocatesA) (Const . Any . allocates gs) a))

-- The value of a closed value in the body of a global: the lets it is built from that stand for
-- globals as (owned references to) those globals, the other closed lets as their values; the
-- globals it reads stay as they are.
-- A closure binds its captures so at the start of its body, which owns them. Nothing if it
-- needs a folded call that is not extracted.
expand :: Grounds -> M.Map Path Name -> VVal -> Maybe VVal
expand gs names = go
  where
    go val = case val of
               Var x | Just g <- M.lookup x names -> Just (DupV (Glob g []))
                     | Just (_,GValue v,_) <- M.lookup x gs -> go v
                     | otherwise -> Nothing
               DupV Glob{} -> Just val
               DupV v -> go v
               _ -> descendV goA go val
    goA a = case a of
              Lam ps r e -> do caps <- mapM (\x -> (,) x <$> go (Var x)) (S.toList (fvA a))
                               Just (Lam ps r (foldr (\(x,v) -> Let x (fst3 (gs M.! x)) (Ret v)) e caps))
              _ -> descendA pure goA go a

-- The body of the global of a closed let, given the globals that the lets before stand for. A
-- closed call passes a let that stands for a global to a borrowed parameter as the global
-- (without `dup`), another value only without a `ptr` (which is owned, as a nullary constructor
-- is), and to a unique one nothing that allocates or reads a global; Nothing if it cannot.
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
                (Borrowed,Var y) | Just g <- M.lookup y names -> Just (Glob g [])
                (Borrowed,_) | not (allocates gs v), Just v' <- expand gs names v, noPtr v' -> Just v'
                (Unique,_) | not (allocates gs v), Just v' <- expand gs names v, null (globsV v') -> Just v'
                _ -> Nothing

-- whether a value has no `ptr`
noPtr :: VVal -> Bool
noPtr val
  = case val of
      Ptr _ _ -> False
      _ -> getAll (getConst (descendV (const (Const (All True))) (Const . All . noPtr) val))

-- The global of an extracted value with a body and a type: an existing one with the same body,
-- or a new one, initialised on demand if its body calls a function that is not folded or reads
-- (outside closures) a global other than those made before that are initialised when the
-- program is loaded.
global :: (Name -> Bool) -> Name -> VExpr -> VType -> State St Name
global foldable f body t
  = state $ \st ->
      case M.lookup key (stKeys st) of
        Just g -> (g,st)
        Nothing -> let g = makeHiddenName ("closed" ++ show (stNext st)) f
                       reads vs = not (all (`S.member` stAtLoad st) (concatMap globsV vs))
                       onDemand = case body of
                                    Call h _ vs -> not (foldable h) || reads vs
                                    Ret v -> reads [v]
                                    _ -> True
                   in (g, st{ stKeys = M.insert key g (stKeys st)
                            , stDefs = DefVal g [] (if onDemand then OnDemand else AtLoad) t body : stDefs st
                            , stNext = stNext st + 1
                            , stAtLoad = (if onDemand then id else S.insert g) (stAtLoad st) })
  where
    key = show body ++ show t

-- A placeholder for the global of the i-th extracted operand.
placeholder :: Int -> Name
placeholder i = newHiddenName ("closed-operand" ++ show i)

-- The maximal closed operands of non-closed code that allocate and have a closed pointer type
-- (a string, or a pointer to a block), replaced by placeholders, in order, with their values
-- in the body of their global and their types, given the globals that values may read.
extractOperands :: (Name -> Bool) -> Grounds -> M.Map Path Name -> VExpr -> (VExpr,[(VVal,VVal,VType)])
extractOperands readableGlob gs names body = (body',reverse ops)
  where
    (body',ops) = runState (goE body) []
    goE :: VExpr -> State [(VVal,VVal,VType)] VExpr
    goE e = case e of
              Let x t e1 e2 | M.member x gs -> Let x t e1 <$> goE e2
              _ -> descendE pure goV (\_ e' -> goE e') e
    goV :: VVal -> State [(VVal,VVal,VType)] VVal
    goV v = case operandType v of
              Just t | closedV readableGlob (M.keysSet gs) v
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

-- The closed lets that stay: those that non-closed code still uses after the extraction of its
-- operands, and the values that those that stand for no global are built from.
keptLets :: Grounds -> M.Map Path Name -> VExpr -> S.Set Path
keptLets gs names body = go S.empty (S.toList used)
  where
    used = S.filter (`M.member` gs) (S.map rootOf (fvE (strip body)))
    go seen [] = seen
    go seen (x:xs)
      | S.member x seen = go seen xs
      | M.member x names = go (S.insert x seen) xs
      | otherwise = go (S.insert x seen) (depsOf gs x ++ xs)
    -- the body without its closed lets
    strip e = case e of
                Let x _ _ e2 | M.member x gs -> strip e2
                _ -> runIdentity (descendAll (\_ e' -> Identity (strip e')) e)

-- the variables that a value consumes: those not under a `dup`, and the captures of closures
consumed :: VVal -> [Path]
consumed val
  = case val of
      Var x -> [x]
      DupV _ -> []
      _ -> getConst (descendV (Const . consumedA) (Const . consumed) val)
  where
    consumedA a = case a of
                    Lam{} -> S.toList (fvA a)
                    _ -> getConst (descendA (const (Const [])) (Const . consumedA) (Const . consumed) a)

-- the placeholders in a value, outside lambdas
placeholdersIn :: VVal -> [Name]
placeholdersIn val
  = case val of
      Glob p [] -> [p]
      _ -> getConst (descendV (Const . inA) (Const . placeholdersIn) val)
  where
    inA a = getConst (descendA (const (Const [])) (Const . inA) (Const . placeholdersIn) a)

type R = M (Env,Gamma) NameSupply

-- The body with the lets that stand for globals binding them, the lets that are not kept removed,
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
    -- the values that a closed let consumes: a folded call's arguments at owned parameters and
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
