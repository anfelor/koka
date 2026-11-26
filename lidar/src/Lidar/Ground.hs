-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Ground values: the top-level values of a lowered program that C generation can write as
  static data, without code that runs when the module is initialised.

  A value is *ground* if it is built only from literals (strings, characters, and integers that
  every runtime holds without an allocation), units, injections, tuples, boxes, top-level
  functions and other ground globals, through the run-time no-ops (`ptr`, `roll`, `up`, ...).
  The body of a ground `DefVal` is a chain of `let`s of ground values, or of calls that the
  client folds at compile time (`Lean`'s `Name.mkStr`, for instance), ending in a ground value.
  The dups of the chain are left out: static data is never freed, so its reference counts are
  stuck, and a value shared by several fields is written once. A ground value cannot have
  effects or diverge, so writing it statically never changes the meaning of a program.

  Each C generator writes the bindings in order, in its runtime's format.
-}
module Lidar.Ground
  ( Ground(..), GroundBind(..)
  , groundValues, groundOrder, groundV
  ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe( mapMaybe )
import Lidar.Name
import Lidar.Syntax

-- | The body of a ground value: its bindings, in order, and its result. The values of the
-- bindings and the result only use the variables bound before them.
data Ground = Ground{ groundBinds :: [(Path,VType,GroundBind)], groundResult :: VVal }
            deriving (Show)

data GroundBind = GValue VVal               -- ^ a ground value
                | GCall Name [AType] [VVal] -- ^ a call that the client folds, with ground arguments
                deriving (Show)

-- | The ground values of a lowered program, given the functions whose calls the client folds.
-- A value is ground if its body is, given the ground values found so far: the least fixpoint,
-- so that values never refer to each other in a cycle.
groundValues :: (Name -> Bool) -> Program -> M.Map Name Ground
groundValues foldable prog = go M.empty
  where
    vals = [(x,body) | DefVal x _ _ body <- progDefs prog]
    go found
      = let found' = M.union found (M.fromList (mapMaybe (ground found) vals))
        in if M.size found' == M.size found then found else go found'
    ground found (x,body)
      | M.member x found = Nothing
      | otherwise = do g <- groundBody foldable (M.keysSet found) body
                       return (x,g)

-- | The ground values in an order in which each comes after the ground values it refers to.
groundOrder :: M.Map Name Ground -> [Name]
groundOrder gs = reverse (snd (foldl visit (S.empty,[]) (M.keys gs)))
  where
    visit (seen,acc) x
      | S.member x seen = (seen,acc)
      | otherwise = let (seen',acc') = foldl visit (S.insert x seen,acc) (globsOf (gs M.! x))
                    in (seen', x : acc')
    globsOf g = [y | v <- groundResult g : concatMap bindVals (groundBinds g), y <- globsV v, M.member y gs]
    bindVals (_,_,b) = case b of
                         GValue v -> [v]
                         GCall _ _ vs -> vs

-- the body of a value as a ground chain, given the ground globals
groundBody :: (Name -> Bool) -> S.Set Name -> VExpr -> Maybe Ground
groundBody foldable globals body
  = do (binds,res) <- chain body
       GValue v <- Just res
       _ <- checkBinds S.empty binds
       if groundV globals (S.fromList [x | (x,_,_) <- binds]) v then Just (Ground binds v) else Nothing
  where
    chain e = case e of
                Ret v -> Just ([], GValue v)
                Call f tys vs | foldable f -> Just ([], GCall f tys vs)
                Let x t e1 e2 -> do (b1,r1) <- chain e1
                                    (b2,r2) <- chain e2
                                    Just (b1 ++ [(x,t,r1)] ++ b2, r2)
                Dup _ e' -> chain e'
                _ -> Nothing
    -- each binding uses only the variables bound before it
    checkBinds bound binds
      = case binds of
          [] -> Just bound
          (x,_,b):rest | all (groundV globals bound) (bindVals b) -> checkBinds (S.insert x bound) rest
          _ -> Nothing
    bindVals b = case b of
                   GValue v -> [v]
                   GCall _ _ vs -> vs

-- | Whether a value is ground, given the ground globals and the ground variables in scope.
groundV :: S.Set Name -> S.Set Path -> VVal -> Bool
groundV globals bound = gv
  where
    gv val = case val of
               Var x -> S.member x bound
               Glob g _ -> S.member g globals
               DupV v -> gv v
               UnitV -> True
               Lit lit -> groundLit lit
               Inj _ _ v -> gv v
               Tuple vs -> all gv vs
               Ptr _ a -> ga a
               Pack _ _ v -> gv v
               TyApp v _ -> gv v
               Up v -> gv v
               Down _ v -> gv v
               Some v -> gv v
               Hole -> False
               Context _ _ -> False
               NoReuse _ _ -> False
               Null _ -> False
    ga a = case a of
             Fun _ -> True
             UnitA -> True
             InjA _ _ v -> ga v
             Roll _ v -> ga v
             InjLazy _ _ v -> ga v
             Box v -> gv v
             Scalar _ -> False
             OpenCon{} -> False
             Lam{} -> False
             BoxAt{} -> False
    groundLit lit = case lit of
                      LitSmallInt _ -> True
                      LitBigInt _ -> False
                      LitInt _ _ -> True
                      LitString _ -> True
                      LitChar _ -> True
                      LitFloat _ -> False

-- the globals that a value refers to
globsV :: VVal -> [Name]
globsV val
  = case val of
      Glob g _ -> [g]
      DupV v -> globsV v
      Inj _ _ v -> globsV v
      Tuple vs -> concatMap globsV vs
      Ptr _ a -> globsA a
      Pack _ _ v -> globsV v
      TyApp v _ -> globsV v
      Up v -> globsV v
      Down _ v -> globsV v
      Some v -> globsV v
      _ -> []
  where
    globsA a = case a of
                 InjA _ _ v -> globsA v
                 Roll _ v -> globsA v
                 InjLazy _ _ v -> globsA v
                 Box v -> globsV v
                 _ -> []
