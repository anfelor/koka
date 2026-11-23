-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
-- Boxing representations and builders shared by the elaborations into the IR. A raw value is
-- boxed by itself and any other value as a shape, and closures take and return boxed values.
module Lidar.Elab.Representation( rep, boxrep, boxA, shapeLeaves, leafCons
                                , scalarField, varV, atAny, sumOf
                                , tapp, injA, caseSum
                                , withField, leafField, leafStarts, boxLeaf, isMultiSum
                                , ptrA, funPair, knownFun, conValue ) where

import qualified Data.Map as M
import Lidar.Name( Name )
import Lidar.Types( Sub, atAny, underNull, withToken, unToken, isToken, inst, tokenParam )
import Lidar.Syntax
import Lidar.Layout( leaves, isEnum )
import Lidar.Traversal( child )

-- a value at a type variable: `a*`
varV :: TVar -> VType
varV v = VPtr (AVar v)

-- The index of an alternative is its position among the constructors. Filtering alternatives
-- preserves their indices.
sumAlts :: [AType] -> [(Int,AType)]
sumAlts ts = zip [0..] ts

sumOf :: [AType] -> AType
sumOf [a] = a
sumOf ts = ASum (sumAlts ts)

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

-- A result that may yield stays one (`boxrep(W)?`), and the token stays a token
-- (`(boxrep(V), KCtx) -> boxrep(W)? ⊗ KCtx`).
boxFunA :: AType -> AType
boxFunA a
  = case a of
      AFun ps r     -> AFun [(m,if isToken p then p else boxrep p) | (m,p) <- ps] (boxRes r)
      AForall tvs b -> AForall tvs (boxFunA b)
      ABox _        -> a
      AScalar _     -> a
      AUnit         -> a
      ASum _        -> a
      AVar _        -> a
      AApp _ _      -> a
      ACon _ _      -> a
      AAny          -> a
      APrim _       -> a
      ALam _ _      -> a
      ALazy _ _     -> a
  where
    boxRes r = maybe (underNull boxrep r) (withToken . underNull boxrep) (unToken r)

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

-- the shape of a boxed value: a flat sum of its leaves, by position
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
      VOrNull _   -> [ABox t]
      VToken      -> [ABox t]

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
              return (CaseA a alts Nothing)

-- the value of type `t` whose only field (`scalarField`) is `w`; the existentials of `t` do not
-- occur in its fields, which are units apart from `w`
withField :: VType -> VVal -> VVal
withField t w
  = case t of
      VProd fs -> Tuple [if j == leafField fs then withField s w else unitOf s | (j,(_,s)) <- zip [0..] fs]
      VExists tvs b -> Pack t (map (const atAny) tvs) (withField b w)
      _ -> w
  where
    unitOf s = case s of
                 VProd fs -> Tuple (map (unitOf . snd) fs)
                 VExists tvs b -> Pack s (map (const atAny) tvs) (unitOf b)
                 _ -> UnitV

-- the field of a product that holds its only leaf (`scalarField`)
leafField :: [(Field,VType)] -> Int
leafField = length . takeWhile (null . leaves . snd)

-- the position of the first leaf of each alternative
leafStarts :: [(Con,VType)] -> [Int]
leafStarts ts = scanl (+) 0 (map (length . shapeLeaves . snd) ts)

-- the shape of a type that is not a sum of several alternatives
boxLeaf :: VType -> VVal -> AVal
boxLeaf t v
  = case t of
      VUnit       -> UnitA
      VSum _      -> Box v
      VPtr _      -> Box v
      VProd _     -> Box v
      VRaw _      -> Box v
      VExists _ _ -> Box v
      VReuse _ _ _  -> Box v
      VCtx _ _ _  -> Box v
      VCell _ _   -> Box v
      VOrNull _   -> Box v
      VToken      -> Box v

isMultiSum :: VType -> Bool
isMultiSum (VSum ts) = length ts > 1
isMultiSum _         = False

ptrA :: VType -> AType
ptrA (VPtr a) = a
ptrA t        = boxA t

-- functions with the same number of parameters, apart from their tokens
funPair :: AType -> AType -> Maybe ([TVar],[TVar],[(Mode,VType)],VType,[(Mode,VType)],VType)
funPair a b
  = case (a,b) of
      (AFun ps r, AFun qs s) | arity ps == arity qs -> Just ([],[],ps,r,qs,s)
      (AFun ps r, AForall bs (AFun qs s)) | arity ps == arity qs -> Just (bs,[],ps,r,qs,s)
      (AForall as (AFun ps r), AForall bs b') | length as == length bs
        -> case inst bs (map AVar as) b' of
             AFun qs s | arity ps == arity qs -> Just (as,as,ps,r,qs,s)
             _ -> Nothing
      _ -> Nothing
  where
    arity = length . fst . tokenParam

-- a top-level function applied to all its type arguments; as a closure its parameters are owned
knownFun :: VVal -> [AType] -> Maybe (Name,[AType])
knownFun v tys
  = case v of
      TyApp w tys'                                           -> knownFun w (tys' ++ tys)
      Ptr (AForall tvs _) (Fun f) | length tvs == length tys -> Just (f,tys)
      Ptr (AFun _ _) (Fun f)      | null tys                 -> Just (f,tys)
      _                                                      -> Nothing

-- The value of the constructor with index i of the datatype `T⟨B̄⟩`, given its fields `v` (a
-- value of its field types, padded) and the types of their existentials: an injection into
-- a value sum, or a pointer to the rolled injection of its shape (`Box`, or `1` without
-- fields) into the unrolling of `T⟨B̄⟩`, also of a lazy one.
conValue :: MonadFail m => TypeDefs -> Name -> [AType] -> Int -> Sub -> VVal -> m VVal
conValue tdefs tname args i exSub v
  = case M.lookup tname tdefs of
      Just d@TypeDef{ tdefParams = tvs } | length tvs == length args
        -> case tdefBody d of
             BodyValue b -> case inst tvs args b of
                              t@(VSum ts) | length (tdefLabels d) > 1, (_,s):_ <- drop i ts
                                -> return (Inj i t (pack s))
                              t -> return (pack t)
             BodyRef b -> do let t = ACon tname args
                             w <- inj (inst tvs args b)
                             return (Ptr t (Roll t w))
             _ -> fail ("constructing a value of the datatype " ++ show tname ++ ", which has no constructors")
      _ -> fail ("unknown datatype " ++ show tname)
  where
    pack t@(VExists tvs _) = Pack t [M.findWithDefault atAny tv exSub | tv <- tvs] v
    pack _ = v
    shapeVal a = case a of
                   ABox t -> return (Box (pack t))
                   AUnit -> return UnitA
                   _ -> fail ("the alternative " ++ show i ++ " of " ++ show tname ++ " is not a shape")
    inj a = case a of
              ALazy l@(ASum ls) s@(ASum ss)
                | Just b <- lookup i ls -> InjLazy Delay a . InjA i l <$> shapeVal b
                | Just b <- lookup i ss -> InjLazy Whnf a . InjA i s <$> shapeVal b
              ASum ts | Just b <- lookup i ts -> InjA i a <$> shapeVal b
              ASum _ -> fail ("no alternative " ++ show i ++ " in " ++ show tname)
              ALazy _ _ -> fail ("no alternative " ++ show i ++ " in " ++ show tname)
              _ -> shapeVal a
