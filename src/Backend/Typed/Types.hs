-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Types( Sub, Types(..), inst
                          , boxrep, boxA, isPtr, forallA, prodV, splitSum
                          , vtInt, vtString, vtChar, vtFloat, vtAny
                          ) where

import qualified Data.Map as M
import Control.Monad( foldM )
import Common.NamePrim( nameTpInt, nameTpString, nameTpChar, nameTpFloat, nameTpAny )
import Backend.Typed.Syntax

type Sub = M.Map TVar VType

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
inst :: Types t => [TVar] -> [VType] -> t -> t
inst tvs tys = subst (M.fromList (zip tvs tys))

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

vtInt, vtString, vtChar, vtFloat, vtAny :: VType
vtInt    = VCon nameTpInt []
vtString = VCon nameTpString []
vtChar   = VRaw nameTpChar
vtFloat  = VRaw nameTpFloat
vtAny    = VCon nameTpAny []

substV :: Sub -> VType -> VType
substV sub t
  = case t of
      VVar v    -> M.findWithDefault t v sub
      VApp v ts -> applyV (M.findWithDefault (VVar v) v sub) (map (substV sub) ts)
      VCon n ts -> VCon n (map (substV sub) ts)
      VPtr a    -> VPtr (substA sub a)
      VSum ts   -> VSum (map (substV sub) ts)
      VProd x y -> VProd (substV sub x) (substV sub y)
      VExists tvs b -> VExists tvs (substV (foldr M.delete sub tvs) b)
      VTLam tvs b   -> VTLam tvs (substV (foldr M.delete sub tvs) b)
      VUnit     -> t
      VRaw _    -> t
      VReuse _  -> t

applyV :: VType -> [VType] -> VType
applyV f []  = f
applyV f ts
  = case f of
      VVar v    -> VApp v ts
      VApp v ss -> VApp v (ss ++ ts)
      VCon n ss -> VCon n (ss ++ ts)
      VTLam vs b | length vs == length ts -> boxrep (inst vs ts b)
      _         -> VApp (-1) ts

substA :: Sub -> AType -> AType
substA sub a
  = case a of
      ABox t        -> ABox (substV sub t)
      ASum x y      -> ASum (substA sub x) (substA sub y)
      AFun ps r     -> AFun [(m,substV sub p) | (m,p) <- ps] (substV sub r)
      AForall tvs b -> AForall tvs (substA (foldr M.delete sub tvs) b)
      AUnit         -> AUnit

ftvV :: VType -> [TVar]
ftvV t
  = case t of
      VVar v        -> [v]
      VApp v ts     -> v : concatMap ftvV ts
      VCon _ ts     -> concatMap ftvV ts
      VPtr a        -> ftvA a
      VSum ts       -> concatMap ftvV ts
      VProd x y     -> ftvV x ++ ftvV y
      VExists vs b  -> filter (`notElem` vs) (ftvV b)
      VTLam vs b    -> filter (`notElem` vs) (ftvV b)
      VUnit         -> []
      VRaw _        -> []
      VReuse _      -> []

ftvA :: AType -> [TVar]
ftvA a
  = case a of
      ABox t        -> ftvV t
      ASum x y      -> ftvA x ++ ftvA y
      AFun ps r     -> concatMap (ftvV . snd) ps ++ ftvV r
      AForall vs b  -> filter (`notElem` vs) (ftvA b)
      AUnit         -> []

isPtr :: VType -> Bool
isPtr t
  = case t of
      VVar _   -> True
      VApp _ _ -> True
      VCon _ _ -> True
      VPtr _   -> True
      VTLam _ _ -> True
      VUnit    -> False
      VSum _   -> False
      VProd _ _ -> False
      VRaw _   -> False
      VExists _ _ -> False
      VReuse _ -> False

-- the representation at a type variable (Koka's `box`); a closure there takes and returns
-- `boxrep`s of its types (Koka's `boxedFunType`). `boxrep` is idempotent, and since type
-- variables are only instantiated with `boxrep`s it commutes with their substitution:
-- `boxrep (subst sub t) == subst sub (boxrep t)`, e.g. `list<() -> a>[a := boxrep float64]`
-- is `list<boxrep (() -> float64)>` without a deep coercion.
boxrep :: VType -> VType
boxrep t
  = case t of
      VPtr a      -> VPtr (boxFunA a)
      _ | isPtr t -> t
      _           -> VPtr (boxA t)

boxFunA :: AType -> AType
boxFunA a
  = case a of
      AFun ps r     -> AFun [(m,boxrep p) | (m,p) <- ps] (boxrep r)
      AForall tvs b -> AForall tvs (boxFunA b)
      ABox _        -> a
      AUnit         -> a
      ASum _ _      -> a

boxA :: VType -> AType
boxA t
  = case t of
      VUnit   -> AUnit
      VSum ts | not (null ts) -> foldr1 ASum (map boxA ts)
      VSum _      -> ABox t
      VVar _      -> ABox t
      VApp _ _    -> ABox t
      VCon _ _    -> ABox t
      VPtr _      -> ABox t
      VProd _ _   -> ABox t
      VRaw _      -> ABox t
      VExists _ _ -> ABox t
      VTLam _ _   -> ABox t
      VReuse _    -> ABox t

eqV :: VType -> VType -> Bool
eqV s t
  = case (s,t) of
      (VCon n ss, VCon m ts) -> n == m && eqVs ss ts
      (VApp v ss, VApp w ts) -> v == w && eqVs ss ts
      (VPtr a, VPtr b)       -> eqA a b
      (VSum ss, VSum ts)     -> eqVs ss ts
      (VProd a b, VProd c d) -> eqV a c && eqV b d
      (VExists as a, VExists bs b) | length as == length bs
        -> eqV a (inst bs (map VVar as) b)
      (VTLam as a, VTLam bs b) | length as == length bs
        -> eqV a (inst bs (map VVar as) b)
      _                      -> s == t

eqVs :: [VType] -> [VType] -> Bool
eqVs ss ts = length ss == length ts && and (zipWith eqV ss ts)

eqA :: AType -> AType -> Bool
eqA s t
  = case (s,t) of
      (ABox a, ABox b)        -> eqV a b
      (ASum a b, ASum c d)    -> eqA a c && eqA b d
      (AFun ps r, AFun qs s') -> eqVs (map snd ps) (map snd qs) && eqV r s'
      (AForall as a, AForall bs b) | length as == length bs
        -> eqA a (inst bs (map VVar as) b)
      _ -> s == t

matchAWith :: [TVar] -> Sub -> AType -> AType -> Maybe Sub
matchAWith tvs sub pat t
  = case (pat,t) of
      (ABox p, ABox s)       -> matchVWith tvs sub p s
      (ASum p q, ASum s u)   -> matchAWith tvs sub p s >>= \sub' -> matchAWith tvs sub' q u
      (AFun ps r, AFun qs s) | length ps == length qs
        -> foldM (\sb (p,q) -> matchVWith tvs sb p q) sub (zip (map snd ps ++ [r]) (map snd qs ++ [s]))
      (AForall as p, AForall bs s) | length as == length bs
        -> matchAWith tvs sub p (inst bs (map VVar as) s)
      (AUnit, AUnit) -> Just sub
      _ -> Nothing

matchVWith :: [TVar] -> Sub -> VType -> VType -> Maybe Sub
matchVWith tvs sub pat t
  = case pat of
      VVar v | v `elem` tvs -> bind v t
      VApp v ps | v `elem` tvs, Just f <- M.lookup v sub ->
        if eqV (applyV f (map (substV sub) ps)) t then Just sub else Nothing
      VApp v ps | v `elem` tvs ->
        case t of
          VCon n ts | length ts >= length ps
            -> let (hs,rest) = splitAt (length ts - length ps) ts
               in bind v (VCon n hs) >>= \sub' -> matchVs sub' ps rest
          VApp w ts | length ts >= length ps
            -> let (hs,rest) = splitAt (length ts - length ps) ts
               in bind v (applyV (VVar w) hs) >>= \sub' -> matchVs sub' ps rest
          _ -> Nothing
      VApp v ps -> case t of
                     VApp w ts | v == w -> matchVs sub ps ts
                     _ -> Nothing
      VCon n ps -> case t of
                     VCon m ts | n == m -> matchVs sub ps ts
                     _ -> Nothing
      VPtr p    -> case t of
                     VPtr s -> matchAWith tvs sub p s
                     _ -> Nothing
      VSum ps   -> case t of
                     VSum ts -> matchVs sub ps ts
                     _ -> Nothing
      VProd p q -> case t of
                     VProd s u -> matchVs sub [p,q] [s,u]
                     _ -> Nothing
      VExists as p -> case t of
                        VExists bs s | length as == length bs
                          -> matchVWith tvs sub p (inst bs (map VVar as) s)
                        _ -> Nothing
      _ -> if pat == t then Just sub else Nothing
  where
    bind v s = case M.lookup v sub of
                 Nothing -> Just (M.insert v s sub)
                 Just s' -> if eqV s s' then Just sub else Nothing
    matchVs sb ps ts | length ps == length ts = foldM (\sb' (p,s) -> matchVWith tvs sb' p s) sb (zip ps ts)
                     | otherwise = Nothing
