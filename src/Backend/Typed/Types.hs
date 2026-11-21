-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Types( Sub, Types(..), inst, mapReuseContents, traverseReuseContents, collapse
                          , isPtr, forallA, prodV, prodFields
                          , checkDupType, isShape, containsLinear, wellNull, yields, eraseEv, orNull, unNull, underNull
                          , withToken, unToken, isToken, tokenParam
                          , applyA, atAny, vtInt, vtString, vtChar, vtFloat
                          ) where

import Data.Functor.Identity( Identity(..) )
import qualified Data.Map as M
import Common.NamePrim( nameTpAny, nameTpInt, nameTpString )
import Backend.Typed.Syntax

type Sub = M.Map TVar AType

-- substitution, free variables and alpha-equivalence
class Types t where
  subst   :: Sub -> t -> t
  ftv     :: t -> [TVar]
  alphaEq :: t -> t -> Bool

instance Types VType where
  subst     = substV
  ftv       = ftvV
  alphaEq   = eqV

instance Types AType where
  subst     = substA
  ftv       = ftvA
  alphaEq   = eqA

instance Types Ty where
  subst sub (A a) = A (substA sub a)
  subst sub (V t) = V (substV sub t)
  ftv (A a) = ftvA a
  ftv (V t) = ftvV t
  alphaEq (A a) (A b) = eqA a b
  alphaEq (V a) (V b) = eqV a b
  alphaEq _ _ = False

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
      VOrNull b -> VOrNull <$> goV b
      VToken -> pure t
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
      AUnit -> pure a
      AVar _ -> pure a

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

-- the top type `any` of `[up]` and `[down]`, which also instantiates unconstrained type variables
atAny :: AType
atAny = ACon nameTpAny []

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
      VOrNull b -> VOrNull (substV sub b)
      VToken    -> t

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
      VSum ts       -> concatMap (ftvV . snd) ts
      VProd fs      -> concatMap (ftvV . snd) fs
      VExists vs b  -> filter (`notElem` vs) (ftvV b)
      VUnit         -> []
      VRaw _        -> []
      VReuse _ _ p  -> maybe [] ftvContents p
      VCtx _ a b    -> ftvA a ++ ftvA b
      VCell _ a     -> ftvA a
      VOrNull b     -> ftvV b
      VToken        -> []

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
      VOrNull _   -> False
      VToken      -> False

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
      (VOrNull a, VOrNull b) -> eqV (unNull a) (unNull b)
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
      Up x -> Up (go x)
      Down b x -> Down (substA sub b) (go x)
      _ -> v

ftvContents :: Contents -> [TVar]
ftvContents (Contents _ p t) = go p ++ ftvV t
  where
    go v = case v of
      Inj _ s x -> ftvV s ++ go x
      Tuple xs -> concatMap go xs
      Pack s ts x -> ftvV s ++ concatMap ftvA ts ++ go x
      TyApp x ts -> go x ++ concatMap ftvA ts
      Up x -> go x
      Down b x -> ftvA b ++ go x
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
      (Up x, Up y) -> go x y
      (Down a x, Down b y) -> eqA a b && go x y
      _ -> p == q

-- The normal form of a description: a value built from the children of a variable is that
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
      Up w -> Up (collapse w)
      Down b w -> Down b (collapse w)
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
      _ -> s == t

-- The duplication rule: a variable of type `t` may be duplicated
checkDupType :: Ty -> Either String ()
checkDupType t
  = case t of
      V (VReuse _ _ _) -> Left "dup of a reuse credit"
      V (VCell _ _) -> Left "dup of a cell"
      V VToken -> Left "dup of a token"
      _ -> Right ()

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

-- Credits, cells and tokens have ownership but no reference count: duplication cannot create
-- another owner, so they are not stored in a heap block or captured by a closure.
containsLinear :: Ty -> Bool
containsLinear = go
  where
    go (V v) = case v of
       VPtr a -> go (A a)
       VProd fs -> any (go . V . snd) fs
       VSum ts -> any (go . V . snd) ts
       VExists _ b -> go (V b)
       VUnit -> False
       VRaw _ -> False
       VReuse _ _ _ -> True
       VCtx _ _ _ -> False
       VCell _ _ -> True
       VToken -> True
       VOrNull b -> go (V b)
    go (A a) = case a of
       ABox v -> go (V v)
       AScalar _ -> False
       ASum ts -> any (go . A . snd) ts
       AForall _ b -> go (A b)
       ALam _ b -> go (A b)
       ALazy l b -> go (A l) || go (A b)
       ACon _ ts -> any (go . A) ts
       AApp _ ts -> any (go . A) ts
       AVar _ -> False
       AFun _ _ -> False
       AUnit -> False

-- `V?` contains no credits or cells, and no heap block contains a `V?` (see "Nullable values"
-- in `Syntax`)
wellNull :: Ty -> Bool
wellNull ty
  = case ty of
      V t -> goV t
      A a -> goA a
  where
    goV t = case t of
      VOrNull b -> not (containsLinear (V b)) && goV b
      VPtr a -> goA a
      VSum ts -> all (goV . snd) ts
      VProd fs -> all (goV . snd) fs
      VExists _ b -> goV b
      VReuse _ _ p -> maybe True (\(Contents _ _ s) -> goV s) p
      VCtx _ a b -> goA a && goA b
      VCell _ a -> goA a
      VToken -> True
      VUnit -> True
      VRaw _ -> True
    goA a = case a of
      ABox v -> noNull v && goV v
      AFun ps r -> all (goV . snd) ps && goV r
      ASum ts -> all (goA . snd) ts
      AForall _ b -> goA b
      ALam _ b -> goA b
      ALazy l b -> goA l && goA b
      ACon _ ts -> all goA ts
      AApp _ ts -> all goA ts
      AScalar _ -> True
      AVar _ -> True
      AUnit -> True
    -- the unboxed parts of the contents of a block
    noNull v = case v of
      VOrNull _ -> False
      VSum ts -> all (noNull . snd) ts
      VProd fs -> all (noNull . snd) fs
      VExists _ b -> noNull b
      _ -> True

-- `V?`, where `V??` is `V?`
orNull :: VType -> VType
orNull t@(VOrNull _) = t
orNull t = VOrNull t

-- the type `V` of `V?`, or the type itself
unNull :: VType -> VType
unNull (VOrNull t) = unNull t
unNull t = t

-- a function applied to `V` in `V?`, or to the type itself
underNull :: (VType -> VType) -> VType -> VType
underNull f (VOrNull t) = orNull (f t)
underNull f t = f t

-- Whether a result may be the dummy of a yield: `V?`, or `V? ⊗ KCtx` (see "Effect yields" in
-- `Syntax`).
yields :: VType -> Bool
yields t
  = case maybe t id (unToken t) of
      VOrNull _ -> True
      _ -> False

-- `|V|`: the type without any `?` or token (a token is 𝟙, and a token field of a product
-- or a token parameter of a function is left out), also under boxes, type arguments and
-- function types (`[cast-ev]`)
eraseEv :: VType -> VType
eraseEv t
  = case t of
      VOrNull v -> eraseEv v
      VToken -> VUnit
      VPtr a -> VPtr (eraseA a)
      VSum ts -> VSum [(c,eraseEv s) | (c,s) <- ts]
      VProd fs -> prodFields [(f,eraseEv s) | (f,s) <- fs, not (isToken s)]
      VExists vs b -> VExists vs (eraseEv b)
      VReuse fl n p -> VReuse fl n (fmap (\(Contents k v s) -> Contents k v (eraseEv s)) p)
      VCtx fl a b -> VCtx fl (eraseA a) (eraseA b)
      VCell n a -> VCell n (eraseA a)
      VUnit -> t
      VRaw _ -> t
  where
    eraseA a = case a of
      ABox v -> ABox (eraseEv v)
      ASum ts -> ASum [(i,eraseA s) | (i,s) <- ts]
      AFun ps r -> AFun [(m,eraseEv p) | (m,p) <- ps, not (isToken p)] (eraseEv r)
      AForall vs b -> AForall vs (eraseA b)
      AApp v ts -> AApp v (map eraseA ts)
      ACon n ts -> ACon n (map eraseA ts)
      ALam vs b -> ALam vs (eraseA b)
      ALazy l b -> ALazy (eraseA l) (eraseA b)
      AScalar _ -> a
      AUnit -> a
      AVar _ -> a

-- the effect token
isToken :: VType -> Bool
isToken t
  = case t of
      VToken -> True
      _ -> False

-- the result `V` of a token-threaded function as `V ⊗ KCtx`
withToken :: VType -> VType
withToken v = prodV [v,VToken]

-- the result `V` of `V ⊗ KCtx`, if it is one
unToken :: VType -> Maybe VType
unToken t
  = case t of
      VProd [(_,v),(_,VToken)] -> Just v
      _ -> Nothing

-- the parameters of a function without its token, and whether it has one
tokenParam :: [(a,VType)] -> ([(a,VType)],Bool)
tokenParam ps
  = case reverse ps of
      (_,VToken) : rest -> (reverse rest,True)
      _ -> (ps,False)
