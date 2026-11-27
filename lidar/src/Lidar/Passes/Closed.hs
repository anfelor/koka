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
  folds), except that it may also read globals outside the recursive group of the function (by
  a `let glob`) and build closures whose captures are closed. This pass moves such values into
  top-level values: every closed `let` and every maximal closed operand of non-closed code, if
  the value allocates (a box, a string, a closure with captures, or a folded call) and has a
  pointer type without type variables. Each becomes a `DefVal` `f@closed<n>` whose body is a
  single value (or folded call): the extracted values and the globals it is built from are read
  by `let glob`s (`[let-glob]`), the other closed values it is built from appear as their
  values. A closure reads or binds its captures that way at the start of its body, so that it
  has no captures left. Structurally equal values share one global. C generation writes a
  ground global as static data.

  The pass runs after `Reuse`, so a construction that takes a reuse credit (`box@r`) is not
  ground and stays: only fresh allocations move, and no allocation moves to a consumer that
  would have reused it. An extracted `let` becomes a `let glob` of its global, and an extracted
  operand is read by a `let glob` before the node that uses it. Their variables are persistent,
  so their owned uses need no `dup`: the pass removes the dups and drops that Perceus gave an
  extracted `let`, and the uniqueness tests of it (`persist`). The values that an extracted value
  consumed lose a consumption: a closed `let` whose occurrences were all in replaced values is
  removed, any other that is not persistent gets a `drop` in place of the consumption.

  Closed values cannot have effects or diverge. The pass also extracts closed calls: calls with
  closed arguments of functions that the client declares extractable (pure; an action takes
  the effect token, which is never closed). The globals that closed values may read are also
  those the client declares extractable. A global is initialised on demand, at its first use,
  if it calls a function that is not folded or reads (outside closures) a global other than one
  of the values extracted before that are initialised when the program is loaded; its body
  reads an extracted argument by a `let glob`, for an owned parameter as for a borrowed one. A
  call that refers to the recursive group of its function, directly or through its arguments,
  is not extracted, as its initialisation could need itself, and a value never reads a global
  of the group. The extracted values come first in the program; those initialised when it is
  loaded read no global but each other, so a client that cannot write one statically can
  initialise it before any other value.
-}
module Lidar.Passes.Closed( closedProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( foldM, zipWithM )
import Control.Monad.State( State, gets, runState, state )
import Data.Functor.Const( Const(..) )
import Data.Graph( flattenSCC, stronglyConnComp )
import Data.Functor.Identity( Identity(..) )
import Data.List( sortOn )
import Data.Monoid( All(..), Any(..) )
import Lidar.Name
import Lidar.Syntax
import Lidar.Types( Types(ftv), inst, isPtr )
import Lidar.Traversal( descendA, descendV, descendAll, descendE, fvA, fvE, fvV, globalsE, globalsV, sameBlock, stepsFrom, within )
import Lidar.Ground( GroundBind(..), bindVals )
import Lidar.Env( Env(..), envOf, M, ask, evalM )
import Lidar.Query( Gamma )
import Lidar.Passes.Common( paramModes, trivialTy, defGamma, typedChildren, NameSupply, dropValue, freshFor, freshPathFrom, mapAll, renameE, renameV, scopeOf )

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

-- the closed `let`s (and `let glob`s) of a function: their types, values, and index in the
-- order of binding
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
       let (body',operands) = extractOperands gs letNames (defBody def)
       opNames <- mapM (\(_,v,t) -> global foldable f (Ret v) t) operands
       let ops = M.fromList (zip (map placeholder [0 ..]) (zip opNames [v | (v,_,_) <- operands]))
           kept = keptLets gs letNames body'
       -- the rewritten body reads the new globals
       sigs <- gets (\st -> M.fromList [(x,SigVal [] t) | DefVal x _ _ t _ <- stDefs st])
       let env' = env{ envSigs = M.union (envSigs env) sigs }
       return (evalM (rewrite env' gs dropped kept letNames ops body') (env',defGamma def) (freshFor def))
  where
    f = defName def
    (gs,dropped) = closedLets (envSigs env) foldable extractable group (defBody def)
    index x = let (_,_,i) = gs M.! x in i
    readOf (_,b,_) = case b of
                       GGlob g [] -> Just g
                       _ -> Nothing

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a

rootOf :: Path -> Path
rootOf (Path x _) = root x

-- The closed lets of a body, in the order of binding (with lambdas): a let is closed if its
-- value is, or if it calls a folded function with closed arguments (then drops the arguments
-- that it passes to borrowed parameters), given those bound before; a `let glob` is closed if
-- it reads a global that closed values may read, without type arguments. A closed call (of an
-- extractable function, given its type arguments) counts as a folded call unless its arguments
-- refer to the recursive group, also through the values of the closed lets they use.
closedLets :: Sigs -> (Name -> Bool) -> (Name -> Bool) -> S.Set Name -> VExpr -> (Grounds,Dropped)
closedLets sigs foldable extractable group body = (grounds,drops)
  where
    (grounds,drops,_) = foldl add (M.empty,M.empty,S.empty) (zip [0..] (lets body))
    closedCall g tys = extractable g && not (S.member g group) && all (null . ftv) tys
    -- the closed lets so far, their drops, and those that refer to the recursive group
    add (gs,ds,recs) (i,(x,t,e1))
      = let ground v = closedV (M.keysSet gs) v
            refers v = not (S.disjoint group (globalsV v)) || any (`S.member` recs) (S.toList (fvV v))
            mark vs = if any refers vs then S.insert x recs else recs
        in case e1 of
             Left (g,[]) | readable extractable group g -> (M.insert x (t,GGlob g [],i) gs,ds,recs)
             Left _ -> (gs,ds,recs)
             Right (Ret v) | ground v -> (M.insert x (t,GValue v,i) gs,ds,mark [v])
             Right e | Just (g,tys,vs,zs) <- callThenDrops e, all ground vs && all (`M.member` gs) zs
                     , foldable g || (closedCall g tys && not (any refers vs))
                 -> (M.insert x (t,GCall g tys vs,i) gs, M.insert x zs ds, mark vs)
             Right _ -> (gs,ds,recs)
    lets e = case e of
               Let x t e1 e2 | Just _ <- callThenDrops e1 -> (x,t,Right e1) : lets e2
               Let x t e1 _ -> (x,t,Right e1) : descend e
               LetGlob x g tys e2 | Just (SigVal tvs t) <- M.lookup g sigs -> (x,inst tvs tys t,Left (g,tys)) : lets e2
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

-- | Whether a value is closed, given the closed lets in scope: it is ground
-- (`Lidar.Ground.groundV`), except that it may build closures whose captures are closed lets.
closedV :: S.Set Path -> VVal -> Bool
closedV bound = cv
  where
    cv val = case val of
               Var x -> S.member x bound
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
                 Just (_,GGlob{},_) -> False
                 Nothing -> False
      Ptr _ a -> allocatesA a
      _ -> getAny (getConst (descendV (Const . Any . allocatesA) (Const . Any . allocates gs) val))
  where
    allocatesA a = case a of
                     Box _ -> True
                     Constant _ -> True
                     Lam{} -> not (S.null (fvA a))
                     _ -> getAny (getConst (descendA (const (Const (Any False))) (Const . Any . allocatesA) (Const . Any . allocates gs) a))

-- The value of a closed value in the body of a global: the lets it is built from that stand
-- for globals as variables named after those globals (`readGlobals` reads them), the other
-- closed lets as their values. A closure binds its captures so at the start of its body, which
-- owns them (a persistent one needs no `drop`, see `persist`), and reads the globals there.
-- Nothing if it needs a folded call that is not extracted.
expand :: Grounds -> M.Map Path Name -> VVal -> Maybe VVal
expand gs names = go
  where
    go val = case val of
               Var x | Just g <- M.lookup x names -> Just (Var (root g))
                     | Just (_,GValue v,_) <- M.lookup x gs -> go v
                     | otherwise -> Nothing
               _ -> descendV goA go val
    goA a = case a of
              Lam ps r e -> do e' <- foldM capture e (S.toList (fvA a))
                               Just (Lam ps r (readGlobals "c" (`elem` M.elems names) e'))
              _ -> descendA pure goA go a
    capture e x = case M.lookup x names of
                    Just g -> Just (LetGlob x g [] (persist x e))
                    Nothing -> do v <- go (Var x)
                                  Just (Let x (fst3 (gs M.! x)) (Ret v) e)

-- The body of the global of a closed let, given the globals that the lets before stand for (see
-- `expand`). A closed call passes a let that stands for a global to a borrowed parameter,
-- another value only without a `ptr` (which is owned, as a nullary constructor is), and to a
-- unique one nothing that allocates or reads a global; Nothing if it cannot.
letBody :: Env -> (Name -> Bool) -> Grounds -> M.Map Path Name -> Path -> Maybe VExpr
letBody env foldable gs names x
  = case gs M.! x of
      (_,GValue v,_) -> Ret <$> expand gs names v
      (_,GCall g tys vs,_)
        | foldable g -> Call g tys <$> mapM (expand gs names) vs
        | otherwise -> Call g tys <$> zipWithM arg (paramModes env g (length vs)) vs
      (_,GGlob{},_) -> Nothing
  where
    arg m v = case (m,v) of
                (Owned,_) -> expand gs names v
                (Borrowed,Var y) | Just g <- M.lookup y names -> Just (Var (root g))
                (Borrowed,_) | not (allocates gs v), Just v' <- expand gs names v, noPtr v' -> Just v'
                (Unique,_) | not (allocates gs v), Just v' <- expand gs names v, S.null (fvV v') -> Just v'
                _ -> Nothing

-- whether a value has no `ptr`
noPtr :: VVal -> Bool
noPtr val
  = case val of
      Ptr _ _ -> False
      _ -> getAll (getConst (descendV (const (Const (All True))) (Const . All . noPtr) val))

-- The global of an extracted value with a body (from `expand`) and a type: an existing one with
-- the same body, or a new one, initialised on demand if its body calls a function that is not
-- folded or reads (outside closures) a global other than those made before that are
-- initialised when the program is loaded.
global :: (Name -> Bool) -> Name -> VExpr -> VType -> State St Name
global foldable f marked t
  = state $ \st ->
      case M.lookup key (stKeys st) of
        Just g -> (g,st)
        Nothing -> let g = makeHiddenName ("closed" ++ show (stNext st)) f
                       reads = not (all (\(Path h _) -> S.member h (stAtLoad st)) (S.toList (fvE marked)))
                       onDemand = reads || case marked of
                                             Call h _ _ -> not (foldable h)
                                             _ -> False
                   in (g, st{ stKeys = M.insert key g (stKeys st)
                            , stDefs = DefVal g [] (if onDemand then OnDemand else AtLoad) t body : stDefs st
                            , stNext = stNext st + 1
                            , stAtLoad = (if onDemand then id else S.insert g) (stAtLoad st) })
  where
    body = readGlobals "g" (const True) marked
    key = show body ++ show t

-- An expression in which `expand` named the globals it reads after them (its free variables
-- with names that satisfy the predicate), with `let glob`s that read them into variables with
-- the given prefix (a closure in the body of a global has its own, so that it shadows none).
readGlobals :: String -> (Name -> Bool) -> VExpr -> VExpr
readGlobals prefix isGlobal e = foldr (\(y,g) -> LetGlob y g []) (renameE (M.fromList [(root g,y) | (y,g) <- reads]) e) reads
  where
    reads = [(root (newHiddenName (prefix ++ show i)),g) | (i,g) <- zip [0 :: Int ..] [g | Path g [] <- S.toList (fvE e), isGlobal g]]

-- A placeholder for the global of the i-th extracted operand.
placeholder :: Int -> Name
placeholder i = newHiddenName ("closed-operand" ++ show i)

-- The maximal closed operands of non-closed code that allocate and have a closed pointer type
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
              Just t | closedV (M.keysSet gs) v
                       && allocates gs v && closed v t
                     , Just v' <- expand gs names v
                -> state (\os -> (Var (root (placeholder (length os))), (v,v',t) : os))
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

-- The body of a `let glob` that binds `x` in place of an owned variable: without the dups and
-- drops of `x` and of the variables below it with its blocks, which are persistent, and with each
-- uniqueness test of one replaced by its shared branch, as a persistent block is never unique.
-- The dups of the contents of its boxes stay, as these are still counted.
persist :: Path -> VExpr -> VExpr
persist x = go
  where
    mine p = p `within` x && all sameBlock (stepsFrom x p)
    go e = case e of
             Dup _ p e' | mine p -> go e'
             Drop p e' | mine p -> go e'
             IsUnique p _ e2 | mine p -> go e2
             _ -> mapAll (const go) e

-- the variables that a value consumes, with the captures of its closures
consumed :: VVal -> [Path]
consumed val
  = case val of
      Var x -> [x]
      _ -> getConst (descendV (Const . consumedA) (Const . consumed) val)
  where
    consumedA a = case a of
                    Lam{} -> S.toList (fvA a)
                    _ -> getConst (descendA (const (Const [])) (Const . consumedA) (Const . consumed) a)

-- the placeholders in a value, outside lambdas
placeholdersIn :: M.Map Name a -> VVal -> [Name]
placeholdersIn ops = go
  where
    go val = case val of
               Var (Path p []) | M.member p ops -> [p]
               _ -> getConst (descendV (Const . inA) (Const . go) val)
    inA a = getConst (descendA (const (Const [])) (Const . inA) (Const . go) a)

type R = M (Env,Gamma) NameSupply

-- The body with the extracted lets reading their globals (`[let-glob]`), the lets that are not
-- kept removed, and each node with extracted operands reading their globals before it, with a
-- drop of each kept let that lost a consumption before the node that lost it.
rewrite :: Env -> Grounds -> Dropped -> S.Set Path -> M.Map Path Name -> M.Map Name (Name,VVal) -> VExpr -> R VExpr
rewrite env gs dropped kept letNames ops = go
  where
    go e = case e of
             Let x _ _ e2 | Just (_,b,_) <- M.lookup x gs ->
               case M.lookup x letNames of
                 _ | not (S.member x kept) -> lose (consumedBy x b) =<< go e2
                 Just g -> lose (consumedBy x b) =<< typedChildren go (LetGlob x g [] (persist x e2))
                 Nothing -> typedChildren go e
             _ -> do let vals = getConst (descendE (const (Const [])) (\v -> Const [v]) (\_ _ -> Const []) e)
                         ps = concatMap (placeholdersIn ops) vals
                         lost = [v | p <- ps, Just (_,v) <- [M.lookup p ops]]
                     ys <- mapM (const (state (freshPathFrom "cg"))) ps
                     let ren = M.fromList (zip (map root ps) ys)
                         e' = runIdentity (descendE pure (Identity . renameV ren) (\_ e1 -> Identity e1) e)
                         reads = [(y,fst (ops M.! p)) | (y,p) <- zip ys ps]
                     lose lost =<< typedChildren go (foldr (\(y,g) -> LetGlob y g []) e' reads)
    -- the values that a closed let consumes: a folded call's arguments at owned parameters and
    -- the variables it drops after the call
    consumedBy x b = case b of
                       GValue v -> [v]
                       GCall g _ vs -> [v | (m,v) <- zip (paramModes env g (length vs)) vs, owning m]
                                       ++ map Var (M.findWithDefault [] x dropped)
                       GGlob{} -> []
    -- drop the kept lets that the removed values consumed, except the extracted ones, which
    -- are persistent
    lose :: [VVal] -> VExpr -> R VExpr
    lose vals e = foldM dropLet e [z | z <- concatMap consumed vals, S.member z kept, M.notMember z letNames]
    -- Drop a let through a fresh variable, as a let can lose several consumptions in one scope.
    dropLet e z
      | trivialTy env (V t) = return e
      | otherwise = do (_,g) <- ask
                       y <- fresh
                       Let y t (Ret (Var z)) <$> dropValue (trivialTy env) fresh (scopeOf (M.keys g)) y (V t) e
      where t = fst3 (gs M.! z)
    fresh = state (freshPathFrom "cd")
