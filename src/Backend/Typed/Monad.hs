-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- the monad of all passes: an environment, a state and failure with a message
module Backend.Typed.Monad( M, runM, evalM, liftE
                          , module Control.Monad.Reader, module Control.Monad.State
                          ) where

import Control.Monad.Reader
import Control.Monad.State

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
