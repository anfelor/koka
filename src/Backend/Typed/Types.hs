-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Types( Sub, Types(..), inst, mapReuseContents, traverseReuseContents, collapse
                          , unrollMu, isPtr, forallA, prodV, prodFields
                          , leaves, isEnum
                          , dupType, isTrivialWith, isShape, containsLinear
                          , applyA, vtInt, vtString, vtChar, vtFloat
                          ) where

import Data.Functor.Identity( Identity(..) )
import qualified Data.Map as M
import Control.Monad( foldM )
import Common.NamePrim( nameTpInt, nameTpString, nameTpReuse )
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

-- Transform descriptions without changing the runtime type of a credit.
mapReuseContents :: (Maybe Contents -> Maybe Contents) -> VType -> VType
mapReuseContents f = runIdentity . traverseReuseContents (Identity . f)

traverseReuseContents :: Applicative f => (Maybe Contents -> f (Maybe Contents)) -> VType -> f VType
traverseReuseContents f = goV
  where
    goV t = case t of
      VPtr a -> VPtr <$> goA a
      VSum ts -> VSum <$> traverse (\(c,s) -> (,) c <$> goV s) ts
      VProd fs -> VProd <$> traverse (\(f,s) -> (,) f <$> goV s) fs
      VExists vs b -> VExists vs <$> goV b
      VReuse fl n p -> VReuse fl n <$> f p
      VCtx fl a b -> VCtx fl <$> goA a <*> goA b
      VCell n a -> VCell n <$> goA a
      VUnit -> pure t
      VRaw _ -> pure t
    goA a = case a of
      ABox t -> ABox <$> goV t
      AScalar _ -> pure a
      ASum ts -> ASum <$> traverse (\(i,t) -> (,) i <$> goA t) ts
      AFun ps r -> AFun <$> traverse (\(m,t) -> (,) m <$> goV t) ps <*> goV r
      AForall vs b -> AForall vs <$> goA b
      AApp v ts -> AApp v <$> traverse goA ts
      ACon n ts -> ACon n <$> traverse goA ts
      ALam vs b -> ALam vs <$> goA b
      ALazy l b -> ALazy <$> goA l <*> goA b
      AMu x vs b ts -> AMu x vs <$> goA b <*> traverse goA ts
      AUnit -> pure a
      AVar _ -> pure a

-- `A[f/t][B̄/ā]`, the unrolling of `(μt⟨ā⟩. A)⟨B̄⟩` with its recursive occurrences folded to `f`;
-- `f` is the type function `μt⟨ā⟩. A` itself, or the name that abbreviates it
unrollMu :: AType -> TVar -> [TVar] -> AType -> [AType] -> AType
unrollMu f t vs a bs = inst (t:vs) (f:bs) a

forallA :: [TVar] -> AType -> AType
forallA [] a  = a
forallA tvs a = AForall tvs a

-- the product of fields named by their position (`prodFields`)
prodV :: [VType] -> VType
prodV = prodFields . zip (map posField [0..])

-- the product of fields; one field is not wrapped
prodFields :: [(Field,VType)] -> VType
prodFields []      = VUnit
prodFields [(_,t)] = t
prodFields fs      = VProd fs

vtInt, vtString, vtChar, vtFloat :: VType
vtInt    = VPtr (ACon nameTpInt [])
vtString = VPtr (ACon nameTpString [])
vtChar   = VRaw RChar
vtFloat  = VRaw RFloat64

substV :: Sub -> VType -> VType
substV sub t
  = case t of
      VPtr a    -> VPtr (substA sub a)
      VSum ts   -> VSum [(c,substV sub s) | (c,s) <- ts]
      VProd fs  -> VProd [(f,substV sub s) | (f,s) <- fs]
      VExists tvs b -> VExists tvs (substV (foldr M.delete sub tvs) b)
      VUnit     -> t
      VRaw _    -> t
      VReuse f n p -> VReuse f n (fmap (substContents sub) p)
      VCtx f a b -> VCtx f (substA sub a) (substA sub b)
      VCell n a -> VCell n (substA sub a)

substA :: Sub -> AType -> AType
substA sub a
  = case a of
      AVar v        -> M.findWithDefault a v sub
      AApp v ts     -> applyA (M.findWithDefault (AVar v) v sub) (map (substA sub) ts)
      ACon n ts     -> ACon n (map (substA sub) ts)
      ABox t        -> ABox (substV sub t)
      AScalar _     -> a
      ASum ts       -> ASum [(i,substA sub t) | (i,t) <- ts]
      AFun ps r     -> AFun [(m,substV sub p) | (m,p) <- ps] (substV sub r)
      AForall tvs b -> AForall tvs (substA (foldr M.delete sub tvs) b)
      ALam tvs b    -> ALam tvs (substA (foldr M.delete sub tvs) b)
      ALazy l b     -> ALazy (substA sub l) (substA sub b)
      AMu x tvs b ts -> AMu x tvs (substA (foldr M.delete sub (x:tvs)) b) (map (substA sub) ts)
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
      AMu x vs b ss -> AMu x vs b (ss ++ ts)
      _         -> AApp (-1) ts

ftvV :: VType -> [TVar]
ftvV t
  = case t of
      VPtr a        -> ftvA a
      VSum ts       -> concatMap (ftvV . snd) ts
      VProd fs      -> concatMap (ftvV . snd) fs
      VExists vs b  -> filter (`notElem` vs) (ftvV b)
      VUnit         -> []
      VRaw _        -> []
      VReuse _ _ p  -> maybe [] ftvContents p
      VCtx _ a b    -> ftvA a ++ ftvA b
      VCell _ a     -> ftvA a

ftvA :: AType -> [TVar]
ftvA a
  = case a of
      AVar v        -> [v]
      AApp v ts     -> v : concatMap ftvA ts
      ACon _ ts     -> concatMap ftvA ts
      ABox t        -> ftvV t
      AScalar _     -> []
      ASum ts       -> concatMap (ftvA . snd) ts
      AFun ps r     -> concatMap (ftvV . snd) ps ++ ftvV r
      AForall vs b  -> filter (`notElem` vs) (ftvA b)
      ALam vs b     -> filter (`notElem` vs) (ftvA b)
      ALazy l b     -> ftvA l ++ ftvA b
      AMu x vs b ts -> filter (`notElem` (x:vs)) (ftvA b) ++ concatMap ftvA ts
      AUnit         -> []

isPtr :: VType -> Bool
isPtr t
  = case t of
      VPtr _      -> True
      VUnit       -> False
      VSum _      -> False
      VProd _     -> False
      VRaw _      -> False
      VExists _ _ -> False
      VReuse _ _ _  -> False
      VCtx _ _ _  -> False
      VCell _ _   -> False

-- leaves of a product
leaves :: VType -> [VType]
leaves t
  = case t of
      VProd fs -> concatMap (leaves . snd) fs
      VExists _ b -> leaves b
      VUnit -> []
      VPtr _ -> [t]
      VSum _ -> [t]
      VRaw _ -> [t]
      VReuse _ _ _ -> [t]
      VCtx _ a b -> [VPtr a, VPtr b]
      VCell _ _ -> [t]

isEnum :: VType -> Bool
isEnum t
  = case t of
      VSum ts -> length ts > 1 && all (isUnitT . snd) ts
      _ -> False
  where
    isUnitT VUnit = True
    isUnitT (VProd fs) = all (isUnitT . snd) fs
    isUnitT (VExists _ b) = isUnitT b
    isUnitT _ = False

eqV :: VType -> VType -> Bool
eqV s t
  = case (s,t) of
      (VPtr a, VPtr b)       -> eqA a b
      (VSum ss, VSum ts)     -> eqVs (map snd ss) (map snd ts)
      (VProd fs, VProd gs)   -> eqVs (map snd fs) (map snd gs)
      (VExists as a, VExists bs b) | length as == length bs
        -> eqV a (inst bs (map AVar as) b)
      (VReuse f n p, VReuse g m q) -> f == g && n == m && eqContentsMaybe p q
      (VCtx f a b, VCtx g c d) -> f == g && eqA a c && eqA b d
      (VCell n a, VCell m b) -> n == m && eqA a b
      _                      -> s == t

-- Contents are descriptions, so only their structural forms need type substitution.
substContents :: Sub -> Contents -> Contents
substContents sub (Contents k p t) = Contents k (go p) (substV sub t)
  where
    go v = case v of
      Inj i s x -> Inj i (substV sub s) (go x)
      Tuple xs -> Tuple (map go xs)
      Pack s ts x -> Pack (substV sub s) (map (substA sub) ts) (go x)
      TyApp x ts -> TyApp (go x) (map (substA sub) ts)
      _ -> v

ftvContents :: Contents -> [TVar]
ftvContents (Contents _ p t) = go p ++ ftvV t
  where
    go v = case v of
      Inj _ s x -> ftvV s ++ go x
      Tuple xs -> concatMap go xs
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
      (Tuple as, Tuple bs) -> length as == length bs && and (zipWith go as bs)
      (Pack t ts x, Pack u us y) -> eqV t u && eqAs ts us && go x y
      (TyApp x ts, TyApp y us) -> go x y && eqAs ts us
      _ -> p == q

-- The normal form of a description: a value built from the parts of a variable is that
-- variable, as in `(z.f₀, ..., z.fₙ₋₁) = z` and `injᵢ z.injᵢ = z`.
collapse :: VVal -> VVal
collapse v
  = case v of
      Tuple ws -> let ws' = map collapse ws
                  in case sequence [parentAt (SField i (posField i)) w | (i,w) <- zip [0..] ws'] of
                       Just (x:xs) | all (== x) xs -> Var x
                       _ -> Tuple ws'
      Inj i t w -> let w' = collapse w in maybe (Inj i t w') Var (parentAt (SInjV i (tagCon i)) w')
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
      (AScalar a, AScalar b)  -> a == b
      (ASum ss, ASum ts)      -> map fst ss == map fst ts && eqAs (map snd ss) (map snd ts)
      (AFun ps r, AFun qs s') -> eqVs (map snd ps) (map snd qs) && eqV r s'
      (AForall as a, AForall bs b) | length as == length bs
        -> eqA a (inst bs (map AVar as) b)
      (ALam as a, ALam bs b) | length as == length bs
        -> eqA a (inst bs (map AVar as) b)
      (ALazy l a, ALazy k b)  -> eqA l k && eqA a b
      (AMu x as a ss, AMu y bs b ts) | length as == length bs
        -> eqA a (inst (y:bs) (map AVar (x:as)) b) && eqAs ss ts
      _ -> s == t

matchVWith :: [TVar] -> Sub -> VType -> VType -> Maybe Sub
matchVWith tvs sub pat t
  = case (pat,t) of
      (VPtr p, VPtr s)       -> matchAWith tvs sub p s
      (VSum ps, VSum ts) | length ps == length ts
        -> foldM (\sb (p,s) -> matchVWith tvs sb p s) sub (zip (map snd ps) (map snd ts))
      (VProd ps, VProd ts) | length ps == length ts
        -> foldM (\sb (p,s) -> matchVWith tvs sb p s) sub (zip (map snd ps) (map snd ts))
      (VCtx f p q, VCtx g s u) | f == g -> matchAWith tvs sub p s >>= \sub' -> matchAWith tvs sub' q u
      (VCell n p, VCell m s) | n == m -> matchAWith tvs sub p s
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
                     AScalar s | p == s -> Just sub
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
      ALazy l p -> case t of
                     ALazy k s -> matchAWith tvs sub l k >>= \sub' -> matchAWith tvs sub' p s
                     _ -> Nothing
      AMu x as p ps -> case t of
                         AMu y bs s ts | length as == length bs
                           -> matchAWith tvs sub p (inst (y:bs) (map AVar (x:as)) s) >>= \sub' -> matchAs sub' ps ts
                         _ -> Nothing
      AVar _    -> if pat == t then Just sub else Nothing
      AUnit     -> if pat == t then Just sub else Nothing
  where
    bind v s = case M.lookup v sub of
                 Nothing -> Just (M.insert v s sub)
                 Just s' -> if eqA s s' then Just sub else Nothing
    matchAs sb ps ts | length ps == length ts = foldM (\sb' (p,s) -> matchAWith tvs sb' p s) sb (zip ps ts)
                     | otherwise = Nothing

-- The duplication rule: the type of the copy of a variable of type `t`
dupType :: Ty -> Either String Ty
dupType t
  = case t of
      V (VReuse _ _ _) -> Left "dup of a reuse credit"
      V (VCell _ _) -> Left "dup of a cell"
      V _ -> Right t
      A _ -> Left "dup of a boxed value"

-- values of these types need no reference counting, where `unroll` gives the body of a
-- named type if it is known (a type with a single constructor without fields, for example)
isTrivialWith :: (AType -> Maybe AType) -> Ty -> Bool
isTrivialWith unroll t
  = case t of
      V v -> trivialV v
      A a -> trivialA a
  where
    trivialV v = case v of
                   VRaw _       -> True
                   VUnit        -> True
                   VProd fs     -> all (trivialV . snd) fs
                   VSum ts      -> all (trivialV . snd) ts
                   VExists _ b  -> trivialV b
                   VPtr a       -> trivialA a
                   VReuse _ _ _   -> False
                   VCtx _ _ _   -> False
                   VCell _ _    -> False
    trivialA a = case a of
                   AUnit     -> True
                   ASum ts   -> all (trivialA . snd) ts
                   ACon n _  -> n == nameTpReuse || maybe False trivialA (unroll a)
                   ALazy l b -> trivialA l && trivialA b
                   AMu _ _ _ _ -> maybe False trivialA (unroll a)
                   ABox _    -> False
                   AScalar _ -> False
                   AFun _ _  -> False
                   AForall _ _ -> False
                   AVar _    -> False
                   AApp _ _  -> False
                   ALam _ _  -> False

-- Boxed sum alternatives must have a tag determined by their construction: sums are flat and
-- their tags are increasing.
isShape :: AType -> Bool
isShape a = case a of
  ASum ts -> not (null ts) && all (\(i,t) -> i >= 1 && isAlt t) ts
             && and [i < j | ((i,_),(j,_)) <- zip ts (drop 1 ts)]
  _ -> isAlt a
  where
    isAlt t = case t of
                AUnit -> True
                ABox _ -> True
                _ -> False

-- Credits and cells have ownership but no reference count: duplication cannot create another
-- owner, so they are not stored in a heap block or captured by a closure.
containsLinear :: Ty -> Bool
containsLinear (V v) = case v of
  VPtr a -> containsLinear (A a)
  VProd fs -> any (containsLinear . V . snd) fs
  VSum ts -> any (containsLinear . V . snd) ts
  VExists _ b -> containsLinear (V b)
  VUnit -> False
  VRaw _ -> False
  VReuse _ _ _ -> True
  VCtx _ _ _ -> False
  VCell _ _ -> True
containsLinear (A a) = case a of
  ABox v -> containsLinear (V v)
  AScalar _ -> False
  ASum ts -> any (containsLinear . A . snd) ts
  AForall _ b -> containsLinear (A b)
  ALam _ b -> containsLinear (A b)
  ALazy l b -> containsLinear (A l) || containsLinear (A b)
  AMu _ _ b ts -> any (containsLinear . A) (b : ts)
  ACon _ ts -> any (containsLinear . A) ts
  AApp _ ts -> any (containsLinear . A) ts
  AVar _ -> False
  AFun _ _ -> False
  AUnit -> False
