-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Extraction of closed ground values (before Perceus).

  A function that builds a ground value (`Lidar.Ground`: literals, boxes, injections, tuples,
  and calls that the client folds) builds it afresh on every call. This pass moves such values
  into top-level values, which C generation writes as static data: a ground `let` that
  non-ground code uses, and a maximal ground operand of non-ground code, if the value
  allocates (a box, a string, or a folded call) and has a pointer type without type variables.
  Each becomes a `DefVal` `f@closed<n>` whose body is the chain of ground `let`s it is built
  from; the `let` binds the global instead, and the operand is the global. Structurally equal
  values share one global. Ground `let`s that only extracted values used are removed.

  Ground values cannot have effects or diverge, so no call is moved except the folded ones,
  which the client declares pure. Nor is a value of a datatype that the client declares fresh,
  or a value built from one: those must be allocated every time (Lean's results of `IO`, which
  carry the state of the world, as each allocation counts a heartbeat). Perceus then treats the globals as borrowed values,
  duplicated where they are consumed: the first consumer that needs a value unique copies it,
  so extraction never adds an allocation.

  The extracted values refer to no global but each other, and come first in the program, so a
  client that cannot write one statically can initialise it before any other value.
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
import Lidar.Traversal( descendA, descendV, descendAll, descendE, fvE, fvV )
import Lidar.Ground( GroundBind(..), groundV )

-- | Extract the closed ground values of the functions of a program, given the functions whose
-- calls the client folds and the datatypes whose values it builds afresh.
closedProgram :: (Name -> Bool) -> (Name -> Bool) -> Program -> Program
closedProgram foldable fresh prog
  = prog{ progSigs = M.union (progSigs prog) (M.fromList [(x,SigVal [] t) | DefVal x _ t _ <- new])
        , progDefs = new ++ defs }
  where
    (defs,(_,newRev,_)) = runState (mapM closedDef (progDefs prog)) (M.empty,[],0)
    new = reverse newRev
    closedDef def = case def of
                      DefFun{} -> do body <- closedBody foldable fresh (defName def) (defBody def)
                                     return def{ defBody = body }
                      DefVal{} -> return def

-- the globals made so far by their bodies, the new definitions (last first), and the next number
type St = (M.Map String Name, [Def], Int)

-- the ground `let`s of a function: their types, values, and index in the order of binding
type Grounds = M.Map Path (VType,GroundBind,Int)

closedBody :: (Name -> Bool) -> (Name -> Bool) -> Name -> VExpr -> State St VExpr
closedBody foldable fresh f body
  = do -- the ground lets used by non-ground code, the extracted ones first
       letNames <- foldM (\m x -> do g <- global f (chain gs m [x] (Var x)) (fst3 (gs M.! x))
                                     return (M.insert x g m))
                         M.empty (sortOn index (filter (extractable gs) (S.toList used)))
       opNames <- mapM (\(v,t) -> global f (chain gs letNames (S.toList (fvV v)) v) t) operands
       let opMap = M.fromList (zip placeholders opNames)
       return (rewrite gs used letNames opMap body')
  where
    gs = groundLets foldable fresh body
    index x = let (_,_,i) = gs M.! x in i
    (body',operands) = extractOperands fresh gs body
    placeholders = map placeholder [0 .. length operands - 1]
    used = usedClosure gs (S.filter (`M.member` gs) (S.map rootOf (fvE (strip gs body'))))

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a

rootOf :: Path -> Path
rootOf (Path x _) = root x

-- The ground lets of a body, in the order of binding (with lambdas): a let is ground if its
-- value is and builds no fresh value, or if it calls a folded function with ground arguments,
-- given those bound before.
groundLets :: (Name -> Bool) -> (Name -> Bool) -> VExpr -> Grounds
groundLets foldable fresh body = foldl add M.empty (zip [0..] (lets body))
  where
    add gs (i,(x,t,e1))
      = let ground v = groundV S.empty (M.keysSet gs) v && not (buildsFresh fresh v)
        in case e1 of
             Ret v | ground v -> M.insert x (t,GValue v,i) gs
             Call g tys vs | foldable g && all ground vs -> M.insert x (t,GCall g tys vs,i) gs
             _ -> gs
    lets e = here e ++ concat (getConst (descendAll (\_ e' -> Const [lets e']) e))
    here e = case e of
               Let x t e1 _ -> [(x,t,e1)]
               _ -> []

-- the ground variables of a ground let's value
depsOf :: Grounds -> Path -> [Path]
depsOf gs x = case gs M.! x of
                (_,GValue v,_) -> S.toList (fvV v)
                (_,GCall _ _ vs,_) -> S.toList (S.unions (map fvV vs))

-- the ground lets that non-ground code needs: those it uses, and the values that those it
-- keeps (as they are not extracted) are built from
usedClosure :: Grounds -> S.Set Path -> S.Set Path
usedClosure gs = go S.empty . S.toList
  where
    go seen [] = seen
    go seen (x:xs)
      | S.member x seen = go seen xs
      | extractable gs x = go (S.insert x seen) xs
      | otherwise = go (S.insert x seen) (depsOf gs x ++ xs)

-- A ground let is extracted if it allocates and has a pointer type without type variables, as
-- have the lets it is built from.
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

-- whether a value builds a block of a fresh datatype
buildsFresh :: (Name -> Bool) -> VVal -> Bool
buildsFresh fresh = fv
  where
    fv val = case val of
               Ptr (ACon t _) _ | fresh t -> True
               _ -> getAny (getConst (descendV (Const . Any . fa) (Const . Any . fv) val))
    fa a = getAny (getConst (descendA (const (Const (Any False))) (Const . Any . fa) (Const . Any . fv) a))

-- The body of an extracted value: the ground lets it is built from (in the order of binding,
-- those extracted already as their globals), then its result.
chain :: Grounds -> M.Map Path Name -> [Path] -> VVal -> VExpr
chain gs names needed result = foldr bind (Ret result) (sortOn index (S.toList (deps needed)))
  where
    index x = let (_,_,i) = gs M.! x in i
    -- an extracted dependency stops the chain
    deps = go S.empty
    go seen [] = seen
    go seen (x:xs)
      | S.member x seen = go seen xs
      | M.member x names = go (S.insert x seen) xs
      | otherwise = go (S.insert x seen) (depsOf gs x ++ xs)
    bind x e = let (t,b,_) = gs M.! x
                   e1 = case M.lookup x names of
                          Just g -> Ret (Glob g [])
                          Nothing -> case b of
                                       GValue v -> Ret v
                                       GCall g tys vs -> Call g tys vs
               in Let x t e1 e

-- The global of an extracted value with a body and a type: an existing one with the same body,
-- or a new one. The body is compared with its binders renamed by position.
global :: Name -> VExpr -> VType -> State St Name
global f body t
  = state $ \(keys,defs,n) ->
      case M.lookup key keys of
        Just g -> (g,(keys,defs,n))
        Nothing -> let g = makeHiddenName ("closed" ++ show n) f
                   in (g,(M.insert key g keys, DefVal g [] t body : defs, n + 1))
  where
    key = show (canonical body) ++ show t

-- a chain with its binders renamed by position
canonical :: VExpr -> VExpr
canonical body = rename M.empty (0 :: Int) body
  where
    rename m i e = case e of
                     Let x t e1 e2 -> let x' = root (newName ("c" ++ show i))
                                          m' = M.insert x x' m
                                      in Let x' t (subst m e1) (rename m' (i + 1) e2)
                     _ -> subst m e
    subst m e = runIdentity (descendE pure (Identity . substV m) (\_ e' -> Identity (subst m e')) e)
    substV m v = case v of
                   Var x -> Var (M.findWithDefault x x m)
                   _ -> runIdentity (descendV (Identity . substA m) (Identity . substV m) v)
    substA m a = runIdentity (descendA pure (Identity . substA m) (Identity . substV m) a)

-- A placeholder for the global of the i-th extracted operand.
placeholder :: Int -> Name
placeholder i = newHiddenName ("closed-operand" ++ show i)

-- The maximal ground operands of non-ground code that allocate, build no fresh value and have a
-- closed pointer type (a string, or a pointer to a block), replaced by placeholders, in order,
-- with their types.
extractOperands :: (Name -> Bool) -> Grounds -> VExpr -> (VExpr,[(VVal,VType)])
extractOperands fresh gs body = (body',reverse ops)
  where
    (body',ops) = runState (goE body) []
    goE :: VExpr -> State [(VVal,VType)] VExpr
    goE e = case e of
              Let x t e1 e2 | M.member x gs -> Let x t e1 <$> goE e2
              _ -> descendE pure goV (\_ e' -> goE e') e
    goV :: VVal -> State [(VVal,VType)] VVal
    goV v = case operandType v of
              Just t | groundV S.empty (M.keysSet gs) v && not (buildsFresh fresh v)
                       && allocates gs v && closed v t
                -> state (\os -> (Glob (placeholder (length os)) [], (v,t) : os))
              _ -> descendV goA goV v
    goA :: AVal -> State [(VVal,VType)] AVal
    goA a = case a of
              Lam ps r e -> Lam ps r <$> goE e
              _ -> descendA pure goA goV a
    closed v t = null (ftv t) && closedTypes gs (S.toList (fvV v))

operandType :: VVal -> Maybe VType
operandType v = case v of
                  Ptr t _ -> Just (VPtr t)
                  _ -> Nothing

-- a body without its ground lets, to find the uses of ground lets in non-ground code
strip :: Grounds -> VExpr -> VExpr
strip gs e = case e of
               Let x _ _ e2 | M.member x gs -> strip gs e2
               _ -> runIdentity (descendAll (\_ e' -> Identity (strip gs e')) e)

-- The body with the extracted lets binding their globals, the other ground lets that it needs,
-- and the globals of the extracted operands.
rewrite :: Grounds -> S.Set Path -> M.Map Path Name -> M.Map Name Name -> VExpr -> VExpr
rewrite gs used letNames opNames = go
  where
    go e = case e of
             Let x t e1 e2 | M.member x gs ->
               case M.lookup x letNames of
                 Just g -> Let x t (Ret (Glob g [])) (go e2)
                 Nothing | S.member x used -> Let x t e1 (go e2)
                         | otherwise -> go e2
             _ -> runIdentity (descendE pure (Identity . goV) (\_ e' -> Identity (go e')) e)
    goV v = case v of
              Glob p [] | Just g <- M.lookup p opNames -> Glob g []
              _ -> runIdentity (descendV (Identity . goA) (Identity . goV) v)
    goA a = case a of
              Lam ps r e -> Lam ps r (go e)
              _ -> runIdentity (descendA pure (Identity . goA) (Identity . goV) a)
