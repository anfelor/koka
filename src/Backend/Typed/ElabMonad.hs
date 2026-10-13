-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

module Backend.Typed.ElabMonad( K, Env(..), St(..), E
                              , runE, failE, tr, env, withLocals, withTVars
                              , fresh, recordSig, note, vt, compose
                              ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Common.Name
import Type.Type
import Kind.Newtypes
import Backend.Typed.Syntax
import Backend.Typed.ElabType
import Backend.Typed.Monad

type K = VExpr -> VExpr

data Env = Env{ envNT :: Newtypes, envLocals :: S.Set Name, envTVars :: S.Set TVar, envSigs :: Sigs }

data St = St{ stUniq :: Int, stSigs :: Sigs, stNotes :: [String] }

type E a = M Env St a

runE :: E a -> Env -> St -> Either String (a,St)
runE = runM

failE :: String -> E a
failE = fail

tr :: Tr a -> E a
tr = liftE

env :: E Env
env = ask

withLocals :: [Name] -> E a -> E a
withLocals xs = local (\e -> e{ envLocals = foldr S.insert (envLocals e) xs })

withTVars :: [TVar] -> E a -> E a
withTVars tvs = local (\e -> e{ envTVars = foldr S.insert (envTVars e) tvs })

fresh :: String -> E Name
fresh s = state (\st -> (newHiddenName (s ++ show (stUniq st)), st{ stUniq = stUniq st + 1 }))

recordSig :: Name -> Sig -> E ()
recordSig name sig = modify (\st -> st{ stSigs = M.insertWith (\_ old -> old) name sig (stSigs st) })

note :: String -> E ()
note msg = modify (\st -> st{ stNotes = stNotes st ++ [msg] })

vt :: Type -> E VType
vt tp = do e <- env
           tr (elabType (envNT e) tp)

compose :: [K] -> K
compose = foldr (.) id
