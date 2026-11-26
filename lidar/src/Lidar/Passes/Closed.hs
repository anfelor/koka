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

  Ground values cannot have effects or diverge, so no call is moved except the folded ones,
  which the client declares pure. The extracted values refer to no global but each other, and
  come first in the program, so a client that cannot write one statically can initialise it
  before any other value.
-}
module Lidar.Passes.Closed( closedProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( foldM )
import Control.Monad.State( State, runState, state )
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Data.List( sortOn )
import Data.Monoid( Any(..) )
import Lidar.Name
import Lidar.Syntax
import Lidar.Types( Types(ftv), isPtr )
import Lidar.Traversal( descendA, descendV, descendAll, descendE, fvE, fvV, mapA, mapV )
import Lidar.Ground( GroundBind(..), groundV )
import Lidar.Env( Env, envOf, M, ask, evalM )
import Lidar.Query( Gamma )
import Lidar.Passes.Common( paramModes, trivialTy, defGamma, typedChildren, NameSupply, dropValue, freshFor, freshPathFrom, scopeOf )

-- | Extract the closed ground values of the functions of a program, given the functions whose
-- calls the client folds.
closedProgram :: (Name -> Bool) -> Program -> (Program,[String])
closedProgram foldable prog
  = ( prog{ progSigs = M.union (progSigs prog) (M.fromList [(x,SigVal [] t) | DefVal x _ _ t _ <- new])
          , progDefs = new ++ map fst results }
    , concatMap snd results )
  where
    (results,(_,newRev,_)) = runState (mapM closedDef (progDefs prog)) (M.empty,[],0)
    new = reverse newRev
    closedDef def = case def of
                      DefFun{} -> do r <- closedBody (envOf prog) foldable def
                                     return (either (\err -> (def,[show (defName def) ++ ": " ++ err]))
                                                    (\body -> (def{ defBody = body },[])) r)
                      DefVal{} -> return (def,[])

-- the globals made so far by their bodies, the new definitions (last first), and the next number
type St = (M.Map String Name, [Def], Int)

-- the ground `let`s of a function: their types, values, and index in the order of binding
type Grounds = M.Map Path (VType,GroundBind,Int)

-- the variables that the ground `let`s of folded calls drop after the call
type Dropped = M.Map Path [Path]

closedBody :: Env -> (Name -> Bool) -> Def -> State St (Either String VExpr)
closedBody env foldable def
  = do -- the extracted lets, in the order of binding, so that each finds its dependencies
       letNames <- foldM (\m x -> case letBody gs m x of
                                    Just b -> do g <- global f b (fst3 (gs M.! x))
                                                 return (M.insert x g m)
                                    Nothing -> return m)
                         M.empty (sortOn index (filter (extractable gs) (M.keys gs)))
       let (body',operands) = extractOperands gs letNames (defBody def)
       opNames <- mapM (\(_,v,t) -> global f (Ret v) t) operands
       let ops = M.fromList (zip (map placeholder [0 ..]) (zip opNames [v | (v,_,_) <- operands]))
           kept = keptLets gs letNames body'
       return (evalM (rewrite env gs dropped kept letNames ops body') (env,defGamma def) (freshFor def))
  where
    f = defName def
    (gs,dropped) = groundLets foldable (defBody def)
    index x = let (_,_,i) = gs M.! x in i

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a

rootOf :: Path -> Path
rootOf (Path x _) = root x

-- The ground lets of a body, in the order of binding (with lambdas): a let is ground if its
-- value is, or if it calls a folded function with ground arguments (then drops the arguments
-- that it passes to borrowed parameters), given those bound before.
groundLets :: (Name -> Bool) -> VExpr -> (Grounds,Dropped)
groundLets foldable body = foldl add (M.empty,M.empty) (zip [0..] (lets body))
  where
    add (gs,ds) (i,(x,t,e1))
      = let ground v = groundV S.empty (M.keysSet gs) v
        in case e1 of
             Ret v | ground v -> (M.insert x (t,GValue v,i) gs,ds)
             _ | Just (g,tys,vs,zs) <- callThenDrops e1, foldable g && all ground vs && all (`M.member` gs) zs
                 -> (M.insert x (t,GCall g tys vs,i) gs, M.insert x zs ds)
             _ -> (gs,ds)
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

-- the body of the global of a ground let, given the globals of the lets extracted before
letBody :: Grounds -> M.Map Path Name -> Path -> Maybe VExpr
letBody gs names x
  = case gs M.! x of
      (_,GValue v,_) -> Ret <$> expand gs names v
      (_,GCall g tys vs,_) -> Call g tys <$> mapM (expand gs names) vs

-- The global of an extracted value with a body and a type: an existing one with the same body,
-- or a new one.
global :: Name -> VExpr -> VType -> State St Name
global f body t
  = state $ \(keys,defs,n) ->
      case M.lookup key keys of
        Just g -> (g,(keys,defs,n))
        Nothing -> let g = makeHiddenName ("closed" ++ show n) f
                   in (g,(M.insert key g keys, DefVal g [] AtLoad t body : defs, n + 1))
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
