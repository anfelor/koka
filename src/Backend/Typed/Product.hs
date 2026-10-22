-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
-- Licensed under the Apache License, Version 2.0.
-----------------------------------------------------------------------------

-- The normal form of products at the representation boundary. Existentials
-- move outside a product; contexts remain atomic (their two fields are scanned).
module Backend.Typed.Product( normalizeVType, normalizeAType, productParts, productOrder
                            , variablesV ) where

import Control.Monad.State
import Backend.Typed.Syntax
import Backend.Typed.Types( Types(..), inst, prodV )
import Backend.Typed.Layout( layout, orderFields )

normalizeAType :: AType -> AType
normalizeAType a = case a of
  ABox t -> ABox (normalizeVType t)
  ASum ts -> ASum [(i,normalizeAType b) | (i,b) <- ts]
  AFun ps r -> AFun [(m,normalizeVType t) | (m,t) <- ps] (normalizeVType r)
  AForall vs b -> AForall vs (normalizeAType b)
  ALam vs b -> ALam vs (normalizeAType b)
  AApp v ts -> AApp v (map normalizeAType ts)
  ACon n ts -> ACon n (map normalizeAType ts)
  _ -> a

normalizeVType :: VType -> VType
normalizeVType t = case t of
  VProd{} -> productType t
  VExists{} -> productType t
  VPtr a -> VPtr (normalizeAType a)
  VSum ts -> VSum (map normalizeVType ts)
  VCtx f a b -> VCtx f (normalizeAType a) (normalizeAType b)
  _ -> t
  where
    productType s = let { (vs,fs) = productParts s
                       ; ns = map normalizeVType fs
                       ; body = prodV [ns !! i | i <- memoryOrder ns] }
                   in if null vs then body else VExists vs body

-- Alpha-rename before hoisting: two fields can instantiate the same
-- existential definition, and its binders must remain independent.
productParts :: VType -> ([TVar],[VType])
productParts t = evalState (collect t) (minimum (0 : variablesV t) - 1)
  where
    collect s = case s of
      VProd a b -> (<>) <$> collect a <*> collect b
      VExists vs b -> do ns <- mapM (const fresh) vs
                         (ws,fs) <- collect (inst vs (map AVar ns) b)
                         return (ns ++ ws,fs)
      VUnit -> return ([],[])
      _ -> return ([],[s])
    fresh = do n <- get; put (n-1); return n

-- The memory order of the fields of a product (`Layout.orderFields`), by the layouts of their
-- normal forms.
productOrder :: [VType] -> [Int]
productOrder = memoryOrder . map normalizeVType

memoryOrder :: [VType] -> [Int]
memoryOrder ns = map fst (orderFields [(i,layout t) | (i,t) <- zip [0..] ns])

variablesV :: VType -> [TVar]
variablesV t = case t of
  VProd a b -> variablesV a ++ variablesV b
  VExists vs b -> vs ++ variablesV b
  VSum ts -> concatMap variablesV ts
  VPtr a -> variablesA a
  VCtx _ a b -> variablesA a ++ variablesA b
  VReuse _ _ p -> maybe [] (\(Contents _ _ s) -> variablesV s) p
  _ -> []

variablesA :: AType -> [TVar]
variablesA a = case a of
  ABox t -> variablesV t
  ASum ts -> concatMap (variablesA . snd) ts
  AFun ps r -> concatMap (variablesV . snd) ps ++ variablesV r
  AForall vs b -> vs ++ variablesA b
  ALam vs b -> vs ++ variablesA b
  AVar v -> [v]
  AApp v ts -> v : concatMap variablesA ts
  ACon _ ts -> concatMap variablesA ts
  AScalar _ -> []
  AUnit -> []
