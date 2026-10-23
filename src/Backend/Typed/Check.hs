-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Whole-program type validation; Query implements the typing rules.
module Backend.Typed.Check( checkProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Query( Env, envOf, checkE, yieldJoins )

checkProgram :: Program -> [String]
checkProgram prog
  = [show (defName d) ++ ": " ++ err | d <- progDefs prog, Left err <- [checkPaths d >> checkDef (envOf prog) d]]

-- The variables are named by their paths (see `Syntax.Path`): the binder of a destructuring
-- of a variable is the variable followed by the step of the form, every other binder is a
-- root, and a root is bound once in a definition.
checkPaths :: Def -> Either String ()
checkPaths def
  = case [err | Left err <- bs] ++ ["root bound more than once: " ++ show x | (x,n) <- M.toList counts, n > (1::Int)]
         ++ ["path bound again in its scope: " ++ show x | x <- scopeE params (defBody def)] of
      (err:_) -> Left err
      [] -> Right ()
  where
    bs = case def of
           DefFun{ defArgs = ps } -> concat [rootBinder x | (x,_,_) <- ps] ++ pathsE (defBody def)
           DefVal{} -> pathsE (defBody def)
    counts = M.fromListWith (+) [(x,1) | Right x <- bs]
    params = case def of
               DefFun{ defArgs = ps } -> S.fromList [x | (x,_,_) <- ps]
               DefVal{} -> S.empty

-- the binders of paths that are already in scope: a path denotes one value, so it is bound
-- at most once in a scope (`[unbox-ru]` renames the contents of its box)
scopeE :: S.Set Path -> VExpr -> [Path]
scopeE bound (UnboxRu z r e) = filter (== r) (S.toList bound) ++ scopeE (S.insert r (S.map (rebase z) bound)) e
scopeE bound expr = getConst (descendB (const (Const [])) (Const . scopeV bound) alt expr)
  where
    alt bs e = let xs = map fst bs
               in Const (filter (`S.member` bound) xs ++ scopeE (S.union bound (S.fromList xs)) e)

scopeV :: S.Set Path -> VVal -> [Path]
scopeV bound = getConst . descendV (Const . scopeA bound) (Const . scopeV bound)

scopeA :: S.Set Path -> AVal -> [Path]
scopeA bound val
  = case val of
      Lam ps _ e -> let xs = [x | (x,_,_) <- ps] in filter (`S.member` bound) xs ++ scopeE (S.union bound (S.fromList xs)) e
      _ -> getConst (descendA (const (Const [])) (Const . scopeA bound) (Const . scopeV bound) val)

-- each binder: its root name, or an error if it is not named by its path
pathsE :: VExpr -> [Either String Name]
pathsE expr = getConst (descendB (const (Const [])) (Const . pathsV) (\bs e -> Const (concatMap binder bs ++ pathsE e)) expr)
  where
    binder (x,s) = case pathOf (scrutVar expr) s of
                     Just p | x == p    -> []
                            | otherwise -> [Left ("binder " ++ show x ++ " is not named by its path " ++ show p)]
                     Nothing -> rootBinder x

pathsV :: VVal -> [Either String Name]
pathsV = getConst . descendV (Const . pathsA) (Const . pathsV)

pathsA :: AVal -> [Either String Name]
pathsA val
  = case val of
      Lam ps _ e -> concat [rootBinder x | (x,_,_) <- ps] ++ pathsE e
      _ -> getConst (descendA (const (Const [])) (Const . pathsA) (Const . pathsV) val)

rootBinder :: Path -> [Either String Name]
rootBinder (Path x []) = [Right x]
rootBinder x = [Left ("binder " ++ show x ++ " is not a root")]

checkDef :: Env -> Def -> Either String ()
checkDef env def
  = case def of
      DefFun _ _ args res body -> checkE env (M.fromList [(x,V t) | (x,_,t) <- args]) yieldJoins body res
      DefVal _ _ t body        -> checkE env M.empty yieldJoins body t
