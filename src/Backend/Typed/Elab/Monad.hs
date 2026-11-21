-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Backend.Typed.Elab.Monad( Env(..), St(..), E
                              , runE, failE, tr, env, withLocals, withTypedLocals, withFields, withTVars, withHole, inClosure
                              , withResult, result
                              , fresh, freshName, recordSig, note, vt
                              , currentToken, setToken, takeToken, takeTokenIf, tokenIn, branch
                              ) where

import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import Common.Name
import Type.Type( Type )
import Kind.Newtypes
import Backend.Typed.Build( K, makeToken )
import Backend.Typed.Syntax
import Backend.Typed.Elab.TypeInfo

-- `envHoles`: the variables bound to the parts of a constructor context under construction:
-- a value that contains the hole, or (`Nothing`) the address of the hole. They are not bound
-- in the IR; their uses become parts of a `ctx` value.
-- `envCaptured`: the locals that the innermost closure captures.
-- `envResult`: the type at which an expression in tail position is elaborated (`withResult`).
-- `envBinders`: the types of the binders of locals, whose uses may have other effects, and
-- which may be `V?` where the Koka type is `V` (a result that may be the dummy of a yield).
-- `envExterns`: the externals in scope. `envTrusted`: whether a `V?` is used as a `V` without a
-- test for null (`Coerce.extractNull`).
data Env = Env{ envNT :: Newtypes, envLocals :: S.Set Name, envTVars :: S.Set TVar, envSigs :: Sigs
              , envHoles :: M.Map Name (Maybe VVal), envCaptured :: S.Set Name
              , envFields :: M.Map Name (K,VVal), envResult :: VType, envBinders :: M.Map Name VType
              , envExterns :: S.Set Name, envTrusted :: Bool }

-- `stToken`: the current effect token, if the expression is token-threaded (see "The effect
-- token" in `Syntax`). Elaboration follows the order of evaluation: a call takes the token,
-- and a binder of the result of a call sets the next one.
data St = St{ stUniq :: Int, stSigs :: Sigs, stNotes :: [String], stToken :: Maybe Path }

-- Elaboration owns its environment, state and failure independently of IR passes.
newtype E a = E (ReaderT Env (StateT St (Either String)) a)
            deriving (Functor, Applicative, Monad, MonadReader Env, MonadState St)

instance MonadFail E where
  fail msg = E (lift (lift (Left msg)))

runE :: E a -> Env -> St -> Either String (a,St)
runE (E m) e st = runStateT (runReaderT m e) st

failE :: String -> E a
failE = fail

tr :: Tr a -> E a
tr = either failE return

env :: E Env
env = ask

withLocals :: [Name] -> E a -> E a
withLocals xs = local (\e -> e{ envLocals = foldr S.insert (envLocals e) xs, envCaptured = foldr S.delete (envCaptured e) xs
                                           , envFields = foldr M.delete (envFields e) xs, envBinders = foldr M.delete (envBinders e) xs })

-- locals with the types of their binders
withTypedLocals :: [(Name,VType)] -> E a -> E a
withTypedLocals xs m = withLocals (map fst xs) (local (\e -> e{ envBinders = M.union (M.fromList xs) (envBinders e) }) m)

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

-- the result type of the expressions in tail position
withResult :: VType -> E a -> E a
withResult t = local (\e -> e{ envResult = t })

result :: E VType
result = asks envResult

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

currentToken :: E (Maybe Path)
currentToken = gets stToken

setToken :: Maybe Path -> E ()
setToken k = modify (\st -> st{ stToken = k })

-- The current token, which the caller consumes. Without one (in total or `div` code), a fresh
-- token is made (`[cast-ev]`, see "The effect token" in `Syntax`).
takeToken :: E (K,VVal)
takeToken
  = do mk <- currentToken
       case mk of
         Just k -> do setToken Nothing
                      return (id, Var k)
         Nothing -> do k <- fresh "k"
                       return (makeToken k, Var k)

-- the token argument of a call, if the callee takes one (`takeToken`)
takeTokenIf :: Bool -> E (K,[VVal])
takeTokenIf False = return (id,[])
takeTokenIf True = do (k,v) <- takeToken
                      return (k,[v])

-- an elaboration with the current token `k`, after which the token is what it was before
tokenIn :: Maybe Path -> E a -> E a
tokenIn k m = do old <- currentToken
                 setToken k
                 x <- m
                 setToken old
                 return x

-- a branch, which starts with the current token, as do the other branches
branch :: E a -> E a
branch m = do k <- currentToken
              tokenIn k m
