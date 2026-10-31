-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
-- Koka boxing representations and builders used by Core-to-typed-IR elaboration.
module Backend.Typed.Elab.Representation( rep, boxrep, boxA, shapeLeaves, leafCons
                                        , scalarField, varV, atAny, sumOf
                                        , tapp, injA, caseSum ) where

import Common.NamePrim( nameTpAny )
import Backend.Typed.Syntax
import Backend.Typed.Types( leaves, isEnum )
import Backend.Typed.Traversal( child )

-- a value at a type variable: `a*`
varV :: TVar -> VType
varV v = VPtr (AVar v)

-- The index of an alternative is its runtime tag (Koka's tags start at 1), not its position
-- in the list. Filtering alternatives therefore preserves their tags.
sumAlts :: [AType] -> [(Int,AType)]
sumAlts ts = zip [1..] ts

sumOf :: [AType] -> AType
sumOf [a] = a
sumOf ts = ASum (sumAlts ts)

atAny :: AType
atAny = ACon nameTpAny []

-- the boxed type that instantiates a type variable for a Koka type argument of type `V` (Koka's
-- `box`); a closure there takes and returns `boxrep`s of its types (Koka's `boxedFunType`).
-- `rep` is idempotent (`rep (VPtr (rep t)) == rep t`), so that
-- `list<() -> a>[a := rep float64]` is `list<rep (() -> float64)>` without a deep coercion.
rep :: VType -> AType
rep t
  = case t of
      VPtr a -> boxFunA a
      _      -> boxA t

-- the representation of a value of type `V` at a type variable
boxrep :: VType -> VType
boxrep t = VPtr (rep t)

boxFunA :: AType -> AType
boxFunA a
  = case a of
      AFun ps r     -> AFun [(m,boxrep p) | (m,p) <- ps] (boxrep r)
      AForall tvs b -> AForall tvs (boxFunA b)
      ABox _        -> a
      AScalar _     -> a
      AUnit         -> a
      ASum _        -> a
      AVar _        -> a
      AApp _ _      -> a
      ACon _ _      -> a
      ALam _ _      -> a
      ALazy _ _     -> a
      AMu _ _ _ _   -> a

-- Koka's `box`: a raw value is boxed by itself, any other value as a shape, and a product of a
-- single raw value or enumeration (`scalarField`) like that field
boxA :: VType -> AType
boxA t
  = case t of
      VSum [(_,s)] -> boxA s
      VRaw r   -> AScalar r
      _ | Just s <- scalarField t -> boxA s
        | otherwise -> shapeA t

-- the only field of a product of a raw value or an enumeration and units, which Koka boxes like
-- that field: as `Scalar raw`, or as the shape of the enumeration
scalarField :: VType -> Maybe VType
scalarField t
  = case (t, leaves t) of
      (VSum _, _)      -> Nothing
      (VRaw _, _)      -> Nothing
      (_, [s@(VRaw _)]) -> Just s
      (_, [s]) | isEnum s -> Just s
      _                -> Nothing

-- the shape of a boxed value: a flat sum of its leaves, which have tags
shapeA :: VType -> AType
shapeA t = sumOf (shapeLeaves t)

-- the constructors of the leaves of a value sum (`shapeLeaves`): those of a nested sum are its own
leafCons :: [(Con,VType)] -> [Con]
leafCons ts = concat [case s of { VSum us@(_:_) -> leafCons us; _ -> [c] } | (c,s) <- ts]

-- the alternatives of a value, where those of nested sums are spliced in, in order
shapeLeaves :: VType -> [AType]
shapeLeaves t
  = case t of
      VUnit   -> [AUnit]
      VSum [(_,s)] -> shapeLeaves s
      VSum ts | not (null ts) -> concatMap (shapeLeaves . snd) ts
      VSum _      -> [ABox t]
      VPtr _      -> [ABox t]
      VProd _     -> [ABox t]
      VRaw _      -> [ABox t]
      VExists _ _ -> [ABox t]
      VReuse _ _ _  -> [ABox t]
      VCtx _ _ _  -> [ABox t]
      VCell _ _   -> [ABox t]

tapp :: VVal -> [AType] -> VVal
tapp v []  = v
tapp v tys = TyApp v tys

injA :: [AType] -> Int -> AVal -> AVal
injA [_] 0 v = v
injA ss i v = InjA (fst (sumAlts ss !! i)) (sumOf ss) v

-- a case on each alternative of a boxed sum `a`; the branch gets the alternative, a variable at a
-- boxed type that it may only destructure. `cons` are the constructors of the alternatives.
caseSum :: MonadFail m => [Con] -> [AType] -> Path -> (Int -> Path -> m VExpr) -> m VExpr
caseSum cons shapes a branch
  = case shapes of
      [] -> fail "empty case"
      [_] -> branch 0 a
      _ -> do alts <- mapM (\i -> do let tag = fst (sumAlts shapes !! i)
                                         y = child a (SInjA tag (cons !! i))
                                     e <- branch i y
                                     return (tag,y,e)) [0 .. length shapes - 1]
              return (CaseA Owned a alts Nothing)
