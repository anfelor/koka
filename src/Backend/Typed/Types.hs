-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Types( Sub, Types(..), inst, mapReuseContents
                          , rep, boxrep, boxA, isPtr, varV, forallA, prodV, sumTypes, sumAlts, sumWidth
                          , vtInt, vtString, vtChar, vtFloat, atAny
                          ) where

import qualified Data.Map as M
import Control.Monad( foldM )
import Common.NamePrim( nameTpInt, nameTpString, nameTpChar, nameTpFloat, nameTpAny )
import Backend.Typed.Syntax

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
  subst sub (AAt p a) = AAt p (substA sub a)
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
mapReuseContents f = goV
  where
    goV t = case t of
      VPtr a -> VPtr (goA a)
      VSum ts -> VSum (map goV ts)
      VProd a b -> VProd (goV a) (goV b)
      VExists vs b -> VExists vs (goV b)
      VReuse n p -> VReuse n (f p)
      VCtx a b -> VCtx (goA a) (goA b)
      VUnit -> t
      VRaw _ -> t
    goA a = case a of
      ABox t -> ABox (goV t)
      ASum ts -> ASum [(i,goA t) | (i,t) <- ts]
      AFun ps r -> AFun [(m,goV t) | (m,t) <- ps] (goV r)
      AForall vs b -> AForall vs (goA b)
      AApp v ts -> AApp v (map goA ts)
      ACon n ts -> ACon n (map goA ts)
      ALam vs b -> ALam vs (goA b)
      AUnit -> a
      AVar _ -> a

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

-- The index is the start of an alternative's runtime tag interval, not its
-- position in the list. Filtering alternatives therefore preserves their tags.
sumAlts :: [AType] -> [(Int,AType)]
sumAlts ts = zip (scanl (+) 0 (map sumWidth ts)) ts

sumWidth :: AType -> Int
sumWidth (ASum ts) = maximum (0 : [i + sumWidth t | (i,t) <- ts])
sumWidth _ = 1

prodV :: [VType] -> VType
prodV []     = VUnit
prodV [t]    = t
prodV (t:ts) = VProd t (prodV ts)

vtInt, vtString, vtChar, vtFloat :: VType
vtInt    = VPtr (ACon nameTpInt [])
vtString = VPtr (ACon nameTpString [])
vtChar   = VRaw nameTpChar
vtFloat  = VRaw nameTpFloat

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
      VReuse n p -> VReuse n (fmap (substContents sub) p)
      VCtx a b  -> VCtx (substA sub a) (substA sub b)

substA :: Sub -> AType -> AType
substA sub a
  = case a of
      AVar v        -> M.findWithDefault a v sub
      AApp v ts     -> applyA (M.findWithDefault (AVar v) v sub) (map (substA sub) ts)
      ACon n ts     -> ACon n (map (substA sub) ts)
      ABox t        -> ABox (substV sub t)
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
      VReuse _ p    -> maybe [] ftvContents p
      VCtx a b      -> ftvA a ++ ftvA b

ftvA :: AType -> [TVar]
ftvA a
  = case a of
      AVar v        -> [v]
      AApp v ts     -> v : concatMap ftvA ts
      ACon _ ts     -> concatMap ftvA ts
      ABox t        -> ftvV t
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
      VReuse _ _    -> False
      VCtx _ _    -> False

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
      AUnit         -> a
      ASum _        -> a
      AVar _        -> a
      AApp _ _      -> a
      ACon _ _      -> a
      ALam _ _      -> a

boxA :: VType -> AType
boxA t
  = case t of
      VUnit   -> AUnit
      VSum [s]    -> boxA s
      VSum ts | not (null ts) -> ASum (sumAlts (map boxA ts))
      VSum _      -> ABox t
      VPtr _      -> ABox t
      VProd _ _   -> ABox t
      VRaw _      -> ABox t
      VExists _ _ -> ABox t
      VReuse _ _    -> ABox t
      VCtx _ _    -> ABox t

eqV :: VType -> VType -> Bool
eqV s t
  = case (s,t) of
      (VPtr a, VPtr b)       -> eqA a b
      (VSum ss, VSum ts)     -> eqVs ss ts
      (VProd a b, VProd c d) -> eqV a c && eqV b d
      (VExists as a, VExists bs b) | length as == length bs
        -> eqV a (inst bs (map AVar as) b)
      (VReuse n p, VReuse m q) -> n == m && eqContentsMaybe p q
      (VCtx a b, VCtx c d)   -> eqA a c && eqA b d
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

eqContents :: VVal -> VVal -> Bool
eqContents p q = case (p,q) of
  (Inj i t x, Inj j u y) -> i == j && eqV t u && eqContents x y
  (Pair a b, Pair c d) -> eqContents a c && eqContents b d
  (Pack t ts x, Pack u us y) -> eqV t u && eqAs ts us && eqContents x y
  (TyApp x ts, TyApp y us) -> eqContents x y && eqAs ts us
  _ -> p == q

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
      (VCtx p q, VCtx s u)   -> matchAWith tvs sub p s >>= \sub' -> matchAWith tvs sub' q u
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
