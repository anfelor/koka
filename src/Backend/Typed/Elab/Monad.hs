-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

module Backend.Typed.Elab.Monad( Env(..), St(..), E
                              , runE, failE, tr, env, withLocals, withFields, withTVars, withHole, inClosure
                              , fresh, freshName, recordSig, note, vt
                              ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Common.Name
import Type.Type
import Kind.Newtypes
import Backend.Typed.Common( K )
import Backend.Typed.Syntax
import Backend.Typed.TypeInfo
import Backend.Typed.Monad

-- `envHoles`: the variables bound to the parts of a constructor context under construction:
-- a value that contains the hole, or (`Nothing`) the address of the hole. They are not bound
-- in the IR; their uses become parts of a `ctx` value.
-- `envCaptured`: the locals that the innermost closure captures.
data Env = Env{ envNT :: Newtypes, envLocals :: S.Set Name, envTVars :: S.Set TVar, envSigs :: Sigs
              , envHoles :: M.Map Name (Maybe VVal), envCaptured :: S.Set Name
              , envFields :: M.Map Name (K,VVal) }

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
withLocals xs = local (\e -> e{ envLocals = foldr S.insert (envLocals e) xs, envCaptured = foldr S.delete (envCaptured e) xs
                                           , envFields = foldr M.delete (envFields e) xs })

-- Pattern-field getters are emitted at each use, rather than eagerly at the
-- match. Paths subsequently reuses already established canonical components.
withFields :: [(Name,(K,VVal))] -> E a -> E a
withFields fs action = withLocals (map fst fs)
  (local (\e -> e{ envFields = M.union (M.fromList fs) (envFields e) }) action)

-- the body of a closure, which captures the locals in scope
inClosure :: E a -> E a
inClosure = local (\e -> e{ envCaptured = envLocals e })

withHole :: Name -> Maybe VVal -> E a -> E a
withHole x v = local (\e -> e{ envHoles = M.insert x v (envHoles e) })

withTVars :: [TVar] -> E a -> E a
withTVars tvs = local (\e -> e{ envTVars = foldr S.insert (envTVars e) tvs })

freshName :: String -> E Name
freshName s = state (\st -> (newHiddenName (s ++ show (stUniq st)), st{ stUniq = stUniq st + 1 }))

fresh :: String -> E Path
fresh s = root <$> freshName s

recordSig :: Name -> Sig -> E ()
recordSig name sig = modify (\st -> st{ stSigs = M.insertWith (\_ old -> old) name sig (stSigs st) })

note :: String -> E ()
note msg = modify (\st -> st{ stNotes = stNotes st ++ [msg] })

vt :: Type -> E VType
vt tp = do e <- env
           tr (elabType (envNT e) tp)
