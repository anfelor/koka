-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Types( Sub, Types(..), inst
                          , rep, boxrep, boxA, isPtr, varV, forallA, prodV, splitSum
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

-- a value at a type variable: `a*`
varV :: TVar -> VType
varV v = VPtr (AVar v)

forallA :: [TVar] -> AType -> AType
forallA [] a  = a
forallA tvs a = AForall tvs a

-- the n alternatives of a right-nested boxed sum
splitSum :: Int -> AType -> [AType]
splitSum n a
  = case a of
      ASum l r | n > 1 -> l : splitSum (n-1) r
      _ -> [a]

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
      VReuse _  -> t

substA :: Sub -> AType -> AType
substA sub a
  = case a of
      AVar v        -> M.findWithDefault a v sub
      AApp v ts     -> applyA (M.findWithDefault (AVar v) v sub) (map (substA sub) ts)
      ACon n ts     -> ACon n (map (substA sub) ts)
      ABox t        -> ABox (substV sub t)
      ASum x y      -> ASum (substA sub x) (substA sub y)
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
      VReuse _      -> []

ftvA :: AType -> [TVar]
ftvA a
  = case a of
      AVar v        -> [v]
      AApp v ts     -> v : concatMap ftvA ts
      ACon _ ts     -> concatMap ftvA ts
      ABox t        -> ftvV t
      ASum x y      -> ftvA x ++ ftvA y
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
      VReuse _    -> False

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
      ASum _ _      -> a
      AVar _        -> a
      AApp _ _      -> a
      ACon _ _      -> a
      ALam _ _      -> a

boxA :: VType -> AType
boxA t
  = case t of
      VUnit   -> AUnit
      VSum ts | not (null ts) -> foldr1 ASum (map boxA ts)
      VSum _      -> ABox t
      VPtr _      -> ABox t
      VProd _ _   -> ABox t
      VRaw _      -> ABox t
      VExists _ _ -> ABox t
      VReuse _    -> ABox t

eqV :: VType -> VType -> Bool
eqV s t
  = case (s,t) of
      (VPtr a, VPtr b)       -> eqA a b
      (VSum ss, VSum ts)     -> eqVs ss ts
      (VProd a b, VProd c d) -> eqV a c && eqV b d
      (VExists as a, VExists bs b) | length as == length bs
        -> eqV a (inst bs (map AVar as) b)
      _                      -> s == t

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
      (ASum a b, ASum c d)    -> eqA a c && eqA b d
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
      ASum p q  -> case t of
                     ASum s u -> matchAWith tvs sub p s >>= \sub' -> matchAWith tvs sub' q u
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
