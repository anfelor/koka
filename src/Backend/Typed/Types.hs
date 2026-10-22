-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Types( Sub, Types(..), inst, mapReuseContents, traverseReuseContents, collapse
                          , rep, boxrep, boxA, shapeA, shapeLeaves, isPtr, varV, forallA, prodV, sumTypes, sumAlts, sumOf
                          , vtInt, vtString, vtChar, vtFloat, atAny
                          ) where

import Data.Functor.Identity( Identity(..) )
import qualified Data.Map as M
import Control.Monad( foldM )
import Common.NamePrim( nameTpInt, nameTpString, nameTpAny )
import Backend.Typed.Syntax
import Backend.Typed.Layout( isScalar )

type Sub = M.Map TVar AType

-- substitution, free variables, alpha-equivalence and first-order matching
class Types t where
  subst   :: Sub -> t -> t
  ftv     :: t -> [TVar]
  alphaEq :: t -> t -> Bool
  match   :: [TVar] -> t -> t -> Maybe Sub
  match tvs = matchWith tvs M.empty
  matchWith :: [TVar] -> Sub -> t -> t -> Maybe Sub

instance Types VType where
  subst     = substV
  ftv       = ftvV
  alphaEq   = eqV
  matchWith = matchVWith

instance Types AType where
  subst     = substA
  ftv       = ftvA
  alphaEq   = eqA
  matchWith = matchAWith

instance Types Ty where
  subst sub (A a) = A (substA sub a)
  subst sub (V t) = V (substV sub t)
  ftv (A a) = ftvA a
  ftv (V t) = ftvV t
  alphaEq (A a) (A b) = eqA a b
  alphaEq (V a) (V b) = eqV a b
  alphaEq _ _ = False
  matchWith tvs sub (A a) (A b) = matchAWith tvs sub a b
  matchWith tvs sub (V a) (V b) = matchVWith tvs sub a b
  matchWith _ _ _ _ = Nothing

-- instantiate type variables
inst :: Types t => [TVar] -> [AType] -> t -> t
inst tvs tys = subst (M.fromList (zip tvs tys))

-- Transform descriptions without changing the runtime type of a credit.
mapReuseContents :: (Maybe Contents -> Maybe Contents) -> VType -> VType
mapReuseContents f = runIdentity . traverseReuseContents (Identity . f)

traverseReuseContents :: Applicative f => (Maybe Contents -> f (Maybe Contents)) -> VType -> f VType
traverseReuseContents f = goV
  where
    goV t = case t of
      VPtr a -> VPtr <$> goA a
      VSum ts -> VSum <$> traverse goV ts
      VProd a b -> VProd <$> goV a <*> goV b
      VExists vs b -> VExists vs <$> goV b
      VReuse fl n p -> VReuse fl n <$> f p
      VCtx fl a b -> VCtx fl <$> goA a <*> goA b
      VUnit -> pure t
      VRaw _ -> pure t
    goA a = case a of
      ABox t -> ABox <$> goV t
      AScalar t -> AScalar <$> goV t
      ASum ts -> ASum <$> traverse (\(i,t) -> (,) i <$> goA t) ts
      AFun ps r -> AFun <$> traverse (\(m,t) -> (,) m <$> goV t) ps <*> goV r
      AForall vs b -> AForall vs <$> goA b
      AApp v ts -> AApp v <$> traverse goA ts
      ACon n ts -> ACon n <$> traverse goA ts
      ALam vs b -> ALam vs <$> goA b
      AUnit -> pure a
      AVar _ -> pure a

-- a value at a type variable: `a*`
varV :: TVar -> VType
varV v = VPtr (AVar v)

forallA :: [TVar] -> AType -> AType
forallA [] a  = a
forallA tvs a = AForall tvs a

-- the alternatives of a boxed sum (a singleton datatype has no sum wrapper)
sumTypes :: AType -> [AType]
sumTypes a
  = case a of
      ASum ts -> map snd ts
      _ -> [a]

-- The index of an alternative is its runtime tag (Koka's tags start at 1), not its position
-- in the list. Filtering alternatives therefore preserves their tags.
sumAlts :: [AType] -> [(Int,AType)]
sumAlts ts = zip [1..] ts

sumOf :: [AType] -> AType
sumOf [a] = a
sumOf ts = ASum (sumAlts ts)

prodV :: [VType] -> VType
prodV []     = VUnit
prodV [t]    = t
prodV (t:ts) = VProd t (prodV ts)

vtInt, vtString, vtChar, vtFloat :: VType
vtInt    = VPtr (ACon nameTpInt [])
vtString = VPtr (ACon nameTpString [])
vtChar   = VRaw RChar
vtFloat  = VRaw RFloat64

atAny :: AType
atAny = ACon nameTpAny []

substV :: Sub -> VType -> VType
substV sub t
  = case t of
      VPtr a    -> VPtr (substA sub a)
      VSum ts   -> VSum (map (substV sub) ts)
      VProd x y -> VProd (substV sub x) (substV sub y)
      VExists tvs b -> VExists tvs (substV (foldr M.delete sub tvs) b)
      VUnit     -> t
      VRaw _    -> t
      VReuse f n p -> VReuse f n (fmap (substContents sub) p)
      VCtx f a b -> VCtx f (substA sub a) (substA sub b)

substA :: Sub -> AType -> AType
substA sub a
  = case a of
      AVar v        -> M.findWithDefault a v sub
      AApp v ts     -> applyA (M.findWithDefault (AVar v) v sub) (map (substA sub) ts)
      ACon n ts     -> ACon n (map (substA sub) ts)
      ABox t        -> ABox (substV sub t)
      AScalar t     -> AScalar (substV sub t)
      ASum ts       -> ASum [(i,substA sub t) | (i,t) <- ts]
      AFun ps r     -> AFun [(m,substV sub p) | (m,p) <- ps] (substV sub r)
      AForall tvs b -> AForall tvs (substA (foldr M.delete sub tvs) b)
      ALam tvs b    -> ALam tvs (substA (foldr M.delete sub tvs) b)
      AUnit         -> AUnit

-- type application, with β-reduction of type lambdas
applyA :: AType -> [AType] -> AType
applyA f []  = f
applyA f ts
  = case f of
      AVar v    -> AApp v ts
      AApp v ss -> AApp v (ss ++ ts)
      ACon n ss -> ACon n (ss ++ ts)
      ALam vs b | length vs == length ts -> inst vs ts b
                | length vs > length ts  -> ALam (drop (length ts) vs) (inst (take (length ts) vs) ts b)
      _         -> AApp (-1) ts

ftvV :: VType -> [TVar]
ftvV t
  = case t of
      VPtr a        -> ftvA a
      VSum ts       -> concatMap ftvV ts
      VProd x y     -> ftvV x ++ ftvV y
      VExists vs b  -> filter (`notElem` vs) (ftvV b)
      VUnit         -> []
      VRaw _        -> []
      VReuse _ _ p  -> maybe [] ftvContents p
      VCtx _ a b    -> ftvA a ++ ftvA b

ftvA :: AType -> [TVar]
ftvA a
  = case a of
      AVar v        -> [v]
      AApp v ts     -> v : concatMap ftvA ts
      ACon _ ts     -> concatMap ftvA ts
      ABox t        -> ftvV t
      AScalar t     -> ftvV t
      ASum ts       -> concatMap (ftvA . snd) ts
      AFun ps r     -> concatMap (ftvV . snd) ps ++ ftvV r
      AForall vs b  -> filter (`notElem` vs) (ftvA b)
      ALam vs b     -> filter (`notElem` vs) (ftvA b)
      AUnit         -> []

isPtr :: VType -> Bool
isPtr t
  = case t of
      VPtr _      -> True
      VUnit       -> False
      VSum _      -> False
      VProd _ _   -> False
      VRaw _      -> False
      VExists _ _ -> False
      VReuse _ _ _  -> False
      VCtx _ _ _  -> False

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

-- Koka's `box`: a scalar is boxed by itself, any other value as a shape
boxA :: VType -> AType
boxA t
  = case t of
      VSum [s] -> boxA s
      _ | isScalar t -> AScalar t
        | otherwise  -> shapeA t

-- the shape of a boxed value: a flat sum of its leaves, which have tags
shapeA :: VType -> AType
shapeA t = sumOf (shapeLeaves t)

-- the alternatives of a value, where those of nested sums are spliced in, in order
shapeLeaves :: VType -> [AType]
shapeLeaves t
  = case t of
      VUnit   -> [AUnit]
      VSum [s]    -> shapeLeaves s
      VSum ts | not (null ts) -> concatMap shapeLeaves ts
      VSum _      -> [ABox t]
      VPtr _      -> [ABox t]
      VProd _ _   -> [ABox t]
      VRaw _      -> [ABox t]
      VExists _ _ -> [ABox t]
      VReuse _ _ _  -> [ABox t]
      VCtx _ _ _  -> [ABox t]

eqV :: VType -> VType -> Bool
eqV s t
  = case (s,t) of
      (VPtr a, VPtr b)       -> eqA a b
      (VSum ss, VSum ts)     -> eqVs ss ts
      (VProd a b, VProd c d) -> eqV a c && eqV b d
      (VExists as a, VExists bs b) | length as == length bs
        -> eqV a (inst bs (map AVar as) b)
      (VReuse f n p, VReuse g m q) -> f == g && n == m && eqContentsMaybe p q
      (VCtx f a b, VCtx g c d) -> f == g && eqA a c && eqA b d
      _                      -> s == t

-- Contents are descriptions, so only their structural forms need type substitution.
substContents :: Sub -> Contents -> Contents
substContents sub (Contents k p t) = Contents k (go p) (substV sub t)
  where
    go v = case v of
      Inj i s x -> Inj i (substV sub s) (go x)
      Pair x y -> Pair (go x) (go y)
      Pack s ts x -> Pack (substV sub s) (map (substA sub) ts) (go x)
      TyApp x ts -> TyApp (go x) (map (substA sub) ts)
      _ -> v

ftvContents :: Contents -> [TVar]
ftvContents (Contents _ p t) = go p ++ ftvV t
  where
    go v = case v of
      Inj _ s x -> ftvV s ++ go x
      Pair x y -> go x ++ go y
      Pack s ts x -> ftvV s ++ concatMap ftvA ts ++ go x
      TyApp x ts -> go x ++ concatMap ftvA ts
      _ -> []

eqContentsMaybe :: Maybe Contents -> Maybe Contents -> Bool
eqContentsMaybe Nothing Nothing = True
eqContentsMaybe (Just (Contents k p s)) (Just (Contents l q t)) = k == l && eqV s t && eqContents p q
eqContentsMaybe _ _ = False

-- descriptions are equal up to their normal form (`collapse`)
eqContents :: VVal -> VVal -> Bool
eqContents p0 q0 = go (collapse p0) (collapse q0)
  where
    go p q = case (p,q) of
      (Inj i t x, Inj j u y) -> i == j && eqV t u && go x y
      (Pair a b, Pair c d) -> go a c && go b d
      (Pack t ts x, Pack u us y) -> eqV t u && eqAs ts us && go x y
      (TyApp x ts, TyApp y us) -> go x y && eqAs ts us
      _ -> p == q

-- The normal form of a description: a value built from the parts of a variable is that
-- variable, as in `(z.fst, z.snd) = z` and `injᵢ z.injᵢ = z`.
collapse :: VVal -> VVal
collapse v
  = case v of
      Pair a b -> let a' = collapse a
                      b' = collapse b
                  in case (parentAt SFst a', parentAt SSnd b') of
                       (Just x, Just y) | x == y -> Var x
                       _ -> Pair a' b'
      Inj i t w -> let w' = collapse w in maybe (Inj i t w') Var (parentAt (SInjV i) w')
      Pack t ts w -> let w' = collapse w in maybe (Pack t ts w') Var (parentAt SPack w')
      TyApp w ts -> TyApp (collapse w) ts
      _ -> v
  where
    parentAt s (Var (Path x ss@(_:_))) | last ss == s = Just (Path x (init ss))
    parentAt _ _ = Nothing

eqVs :: [VType] -> [VType] -> Bool
eqVs ss ts = length ss == length ts && and (zipWith eqV ss ts)

eqAs :: [AType] -> [AType] -> Bool
eqAs ss ts = length ss == length ts && and (zipWith eqA ss ts)

eqA :: AType -> AType -> Bool
eqA s t
  = case (s,t) of
      (ACon n ss, ACon m ts)  -> n == m && eqAs ss ts
      (AApp v ss, AApp w ts)  -> v == w && eqAs ss ts
      (ABox a, ABox b)        -> eqV a b
      (AScalar a, AScalar b)  -> eqV a b
      (ASum ss, ASum ts)      -> map fst ss == map fst ts && eqAs (map snd ss) (map snd ts)
      (AFun ps r, AFun qs s') -> eqVs (map snd ps) (map snd qs) && eqV r s'
      (AForall as a, AForall bs b) | length as == length bs
        -> eqA a (inst bs (map AVar as) b)
      (ALam as a, ALam bs b) | length as == length bs
        -> eqA a (inst bs (map AVar as) b)
      _ -> s == t

matchVWith :: [TVar] -> Sub -> VType -> VType -> Maybe Sub
matchVWith tvs sub pat t
  = case (pat,t) of
      (VPtr p, VPtr s)       -> matchAWith tvs sub p s
      (VSum ps, VSum ts) | length ps == length ts
        -> foldM (\sb (p,s) -> matchVWith tvs sb p s) sub (zip ps ts)
      (VProd p q, VProd s u) -> matchVWith tvs sub p s >>= \sub' -> matchVWith tvs sub' q u
      (VCtx f p q, VCtx g s u) | f == g -> matchAWith tvs sub p s >>= \sub' -> matchAWith tvs sub' q u
      (VExists as p, VExists bs s) | length as == length bs
        -> matchVWith tvs sub p (inst bs (map AVar as) s)
      _ -> if pat == t then Just sub else Nothing

matchAWith :: [TVar] -> Sub -> AType -> AType -> Maybe Sub
matchAWith tvs sub pat t
  = case pat of
      AVar v | v `elem` tvs -> bind v t
      AApp v ps | v `elem` tvs, Just f <- M.lookup v sub ->
        if eqA (applyA f (map (substA sub) ps)) t then Just sub else Nothing
      AApp v ps | v `elem` tvs ->
        case t of
          ACon n ts | length ts >= length ps
            -> let (hs,rest) = splitAt (length ts - length ps) ts
               in bind v (ACon n hs) >>= \sub' -> matchAs sub' ps rest
          AApp w ts | length ts >= length ps
            -> let (hs,rest) = splitAt (length ts - length ps) ts
               in bind v (applyA (AVar w) hs) >>= \sub' -> matchAs sub' ps rest
          _ -> Nothing
      AApp v ps -> case t of
                     AApp w ts | v == w -> matchAs sub ps ts
                     _ -> Nothing
      ACon n ps -> case t of
                     ACon m ts | n == m -> matchAs sub ps ts
                     _ -> Nothing
      ABox p    -> case t of
                     ABox s -> matchVWith tvs sub p s
                     _ -> Nothing
      AScalar p -> case t of
                     AScalar s -> matchVWith tvs sub p s
                     _ -> Nothing
      ASum ps   -> case t of
                     ASum ts | map fst ps == map fst ts -> matchAs sub (map snd ps) (map snd ts)
                     _ -> Nothing
      AFun ps r -> case t of
                     AFun qs s | length ps == length qs
                       -> foldM (\sb (p,q) -> matchVWith tvs sb p q) sub (zip (map snd ps ++ [r]) (map snd qs ++ [s]))
                     _ -> Nothing
      AForall as p -> case t of
                        AForall bs s | length as == length bs
                          -> matchAWith tvs sub p (inst bs (map AVar as) s)
                        _ -> Nothing
      ALam as p -> case t of
                     ALam bs s | length as == length bs
                       -> matchAWith tvs sub p (inst bs (map AVar as) s)
                     _ -> Nothing
      AVar _    -> if pat == t then Just sub else Nothing
      AUnit     -> if pat == t then Just sub else Nothing
  where
    bind v s = case M.lookup v sub of
                 Nothing -> Just (M.insert v s sub)
                 Just s' -> if eqA s s' then Just sub else Nothing
    matchAs sb ps ts | length ps == length ts = foldM (\sb' (p,s) -> matchAWith tvs sb' p s) sb (zip ps ts)
                     | otherwise = Nothing
