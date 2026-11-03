-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- The global environment of a typed IR program, queries on it and on types that need no
-- typing context, and the monad for typed IR consumers.
module Backend.Typed.Env( Env(..), Q, envOf, funSig, unrollT, lazySides, openFields, boxContents, reuseSize, noHeapCredit
                        , M, runM, evalM, liftE
                        , module Control.Monad.Reader, module Control.Monad.State
                        ) where

import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as M
import Control.Monad( when )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Types
import Backend.Typed.Pretty( ppr )
import Backend.Typed.Layout( layout, blockSize )

-- The monad for typed IR consumers: an environment, state and failure message.
newtype M r s a = M (ReaderT r (StateT s (Either String)) a)
                deriving (Functor, Applicative, Monad, MonadReader r, MonadState s)

instance MonadFail (M r s) where
  fail msg = M (lift (lift (Left msg)))

runM :: M r s a -> r -> s -> Either String (a,s)
runM (M m) r s = runStateT (runReaderT m r) s

evalM :: M r s a -> r -> s -> Either String a
evalM m r s = fst <$> runM m r s

liftE :: Either String a -> M r s a
liftE = either fail return

data Env = Env{ envTypes :: TypeDefs, envSigs :: Sigs }

type Q a = Either String a

envOf :: Program -> Env
envOf prog = Env (progTypes prog) (progSigs prog)

funSig :: Env -> Name -> [AType] -> Q ([VType],VType)
funSig env f tys
  = case M.lookup f (envSigs env) of
      Just (SigFun tvs ps _ r) | length tvs == length tys
        -> return (map (inst tvs tys . snd) ps, inst tvs tys r)
      Just sig -> Left ("call of " ++ show f ++ " with " ++ show (length tys) ++ " type arguments: " ++ show sig)
      Nothing  -> Left ("unknown function: " ++ show f)

-- `unroll(τ)` of a recursive type, also by its name (δ), when the unrolling folds back to it
unrollT :: Env -> AType -> Q AType
unrollT env t
  = case t of
      AMu x vs a bs | length vs == length bs
        -> return (unrollMu (if null vs then t else ALam vs (AMu x vs a (map AVar vs))) x vs a bs)
      ACon n args -> case M.lookup n (envTypes env) of
                       Just (TypeDef _ tvs (Just body)) | length tvs == length args
                         -> case body of
                              AMu x vs a bs | bs == map AVar tvs -> return (unrollMu (ACon n []) x vs a args)
                              _ -> unrollT env (inst tvs args body)
                       Just _  -> Left ("cannot unroll abstract type " ++ show n)
                       Nothing -> Left ("unknown type " ++ show n)
      _ -> Left ("unroll of " ++ ppr (A t))

-- the thunks and the strict alternatives of a lazy type, `unroll(τ) = L ~> S`
lazySides :: Env -> AType -> Q ([(Int,AType)],[(Int,AType)])
lazySides env t
  = do b <- unrollT env t
       case b of
         ALazy (ASum l) (ASum s) -> return (l,s)
         _ -> Left ("not a lazy type: " ++ ppr (A t))

-- the fields of an open constructor at an instance `T⟨B̄⟩` of its type
openFields :: Env -> Name -> AType -> Q [VType]
openFields env c t
  = case (M.lookup c (envSigs env), t) of
      (Just (SigCon tvs fs n), ACon m args) | n == m && length tvs == length args -> return (map (inst tvs args) fs)
      (Just (SigCon _ _ _), _) -> Left ("open constructor " ++ show c ++ " does not match " ++ ppr (A t))
      _ -> Left ("unknown open constructor " ++ show c)

-- the contents `V` of a box `Box V`
boxContents :: AType -> Q VType
boxContents t
  = case t of
      ABox v -> return v
      _ -> Left ("not a box: " ++ ppr t)

-- The size `|V|` of a box block. Heap contents cannot contain linear resources.
reuseSize :: VType -> Q Int
reuseSize v
  = do noHeapCredit v
       return (blockSize (layout v))

-- Credits and cells cannot be stored in a heap block (`Types.containsLinear`).
noHeapCredit :: VType -> Q ()
noHeapCredit t = when (containsLinear (V t)) (Left "cannot store reuse credits or cells in a heap block")
