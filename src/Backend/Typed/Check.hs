-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Whole-program type validation; Query implements the typing rules.
module Backend.Typed.Check( checkProgram, checkTypes ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Types( Types(..) )
import Backend.Typed.Pretty( ppr )
import Backend.Typed.Query( Env, envOf, checkE, yieldJoins )
import Backend.Typed.Layout( layout, leaves, checkLayout, memoryOrder )

-- After OrderFields the types are also in layout normal form.
checkProgram :: Program -> [String]
checkProgram prog
  = checkLayoutProgram prog ++ [show (defName d) ++ ": " ++ err | d <- progDefs prog, Left err <- [checkPaths d >> checkTypeVars d >> checkDef (envOf prog) d]]

-- The types of a program are in layout normal form and have valid layouts.
checkLayoutProgram :: Program -> [String]
checkLayoutProgram p = concatMap check (programTypes p)
  where
    check t = normal t ++ checkLayout (layout t)
    normal t = case t of
      VProd a b -> ["product is not in layout normal form" | compound a || empty b || ordered /= [0..length fs-1]]
                   ++ normal a ++ normal b
        where fs = leaves t
              ordered = memoryOrder fs
      VExists _ b -> ["nested existential in layout normal form" | exists b] ++ normal b
      VPtr a -> atomic a
      VSum ts -> concatMap normal ts
      VCtx _ a b -> atomic a ++ atomic b
      VReuse _ _ d -> maybe [] (\(Contents _ _ s) -> normal s) d
      _ -> []
    compound VProd{} = True
    compound VExists{} = True
    compound VUnit = True
    compound _ = False
    empty VUnit = True
    empty VExists{} = True
    empty _ = False
    exists VExists{} = True
    exists _ = False
    atomic a = case a of
      ABox t -> check t
      ASum ts -> concatMap (atomic . snd) ts
      AFun ps r -> concatMap check (r : map snd ps)
      AForall _ b -> atomic b
      ALam _ b -> atomic b
      ACon _ ts -> concatMap atomic ts
      AApp _ ts -> concatMap atomic ts
      _ -> []

-- The typing rules hold before the variables are named by their paths, so the
-- elaborated program is checked for types only.
checkTypes :: Program -> [String]
checkTypes prog
  = [show (defName d) ++ ": " ++ err | d <- progDefs prog, Left err <- [checkDef (envOf prog) d]]

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

-- Type variables are bound by a definition, `gen`, `unpack` and join points, and the
-- annotations only mention those in scope.
checkTypeVars :: Def -> Either String ()
checkTypeVars def
  = case outside bound sig ++ tvarsE bound (defBody def) of
      (v:_) -> Left ("type variable out of scope: " ++ ppr (AVar v))
      [] -> Right ()
  where
    bound = S.fromList (defParams def)
    sig = case def of
            DefFun{ defArgs = ps, defRes = r } -> concat [ftv t | (_,_,t) <- ps] ++ ftv r
            DefVal{ defType = t } -> ftv t

outside :: S.Set TVar -> [TVar] -> [TVar]
outside bound = filter (`S.notMember` bound)

tvarsE :: S.Set TVar -> VExpr -> [TVar]
tvarsE bound expr
  = case expr of
      Unpack _ v tvs _ e  -> tvarsV bound v ++ tvarsE (with tvs) e
      Gen tvs e           -> tvarsE (with tvs) e
      Join _ tvs ps e1 e2 -> outside (with tvs) (concat [ftv t | (_,_,t) <- ps]) ++ tvarsE (with tvs) e1 ++ tvarsE bound e2
      _ -> outside bound annotations ++ getConst (descendE (const (Const [])) (Const . tvarsV bound) (\_ e -> Const (tvarsE bound e)) expr)
  where
    with tvs = S.union bound (S.fromList tvs)
    annotations = case expr of
      Let _ t _ _        -> ftv t
      LetYield _ t _ _ _ -> ftv t
      Yielded t          -> ftv t
      Call _ ts _        -> concatMap ftv ts
      Jump _ ts _        -> concatMap ftv ts
      _                  -> []

tvarsV :: S.Set TVar -> VVal -> [TVar]
tvarsV bound val
  = outside bound annotations ++ getConst (descendV (Const . tvarsA bound) (Const . tvarsV bound) val)
  where
    annotations = case val of
      Glob _ ts   -> concatMap ftv ts
      Inj _ t _   -> ftv t
      Ptr a _     -> ftv a
      Pack t ts _ -> ftv t ++ concatMap ftv ts
      TyApp _ ts  -> concatMap ftv ts
      Context b _ -> ftv b
      NoReuse _ c -> maybe [] (\(Contents _ p t) -> tvarsV bound p ++ ftv t) c
      _           -> []

tvarsA :: S.Set TVar -> AVal -> [TVar]
tvarsA bound val
  = case val of
      Lam ps r e -> outside bound (concat [ftv t | (_,_,t) <- ps] ++ ftv r) ++ tvarsE bound e
      _ -> outside bound annotations ++ getConst (descendA (const (Const [])) (Const . tvarsA bound) (Const . tvarsV bound) val)
  where
    annotations = case val of
      InjA _ a _      -> ftv a
      Roll a _        -> ftv a
      OpenCon _ ts _  -> concatMap ftv ts
      _               -> []

checkDef :: Env -> Def -> Either String ()
checkDef env def
  = case def of
      DefFun _ _ args res body -> checkE env (M.fromList [(x,V t) | (x,_,t) <- args]) yieldJoins body res
      DefVal _ _ t body        -> checkE env M.empty yieldJoins body t
