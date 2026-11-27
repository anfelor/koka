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
-- typing context, the lazy metadata, and the monad for typed IR consumers.
module Lidar.Env( Env(..), Q, Lazies(..), envOf, funSig, dataBody, pointerShape, lazySides, openFields, boxContents, reuseSize, noHeapCredit
                        , M, runM, evalM, liftE
                        , module Control.Monad.Reader, module Control.Monad.State
                        ) where

import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( when )
import Lidar.Name
import Lidar.Syntax
import Lidar.Types
import Lidar.Pretty( ppr )
import Lidar.Layout( layout, blockSize )

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

data Env = Env{ envTypes :: TypeDefs, envSigs :: Sigs, envExterns :: Externs }

type Q a = Either String a

envOf :: Program -> Env
envOf prog = Env (progTypes prog) (progSigs prog) (progExterns prog)

-- The metadata of lazy types that elaboration (`Elab.Lazy`) passes to `Passes.Lazy`:
-- the `lazy-C` functions with the tag of their constructor, the size of its cell and its
-- fields (with the padding, see `Elab.TypeInfo.conFieldTypes`), the
-- `lazy-eval-locked` functions, and the tag of the indirection ι of each lazy type.
data Lazies = Lazies{ lzCons :: M.Map Name (Int,Int,[VType]), lzLocked :: S.Set Name
                    , lzIndirect :: M.Map Name Int }

funSig :: Env -> Name -> [AType] -> Q ([VType],VType)
funSig env f tys
  = case M.lookup f (envSigs env) of
      Just (SigFun tvs ps _ r) | length tvs == length tys
        -> return (map (inst tvs tys . snd) ps, inst tvs tys r)
      Just sig -> Left ("call of " ++ show f ++ " with " ++ show (length tys) ++ " type arguments: " ++ show sig)
      Nothing  -> Left ("unknown function: " ++ show f)

-- `A[B̄/ā]` for a datatype `T⟨B̄⟩` with `data T⟨ā⟩ := A ∈ Σ`
dataBody :: Env -> AType -> Q AType
dataBody env t
  = case t of
      ACon n args -> case M.lookup n (envTypes env) of
                       Just TypeDef{ tdefParams = tvs, tdefBody = BodyRef body } | length tvs == length args
                         -> return (inst tvs args body)
                       Just _  -> Left ("cannot unroll abstract type " ++ show n)
                       Nothing -> Left ("unknown type " ++ show n)
      _ -> Left ("unroll of " ++ ppr (A t))

-- The constructor shape of a pointer, unfolding named types but not their
-- payloads. Opaque representations supply no such evidence. Guard alias
-- unfolding as well: a recursive name alone has no known representation.
pointerShape :: Env -> Ty -> Maybe AType
pointerShape env t
  = case t of
      V (VPtr a) -> shape S.empty a
      A a -> shape S.empty a
      _ -> Nothing
  where
    shape _ a | isShape a = Just a
    shape seen a = case a of
      ACon n _ | not (S.member n seen)
               , Just TypeDef{} <- M.lookup n (envTypes env)
               , Right b <- dataBody env a -> shape (S.insert n seen) b
      _ -> Nothing

-- the thunks and the strict alternatives of a lazy datatype `T⟨B̄⟩`, `data T⟨ā⟩ := L ~> S`
lazySides :: Env -> AType -> Q ([(Int,AType)],[(Int,AType)])
lazySides env t
  = do b <- dataBody env t
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
