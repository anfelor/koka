-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
-- Licensed under the Apache License, Version 2.0.
-----------------------------------------------------------------------------

-- The normal form of products at the representation boundary. Existentials
-- move outside a product; contexts remain atomic (their two fields are scanned).
module Backend.Typed.Product( normalizeVType, normalizeAType, productParts, productOrder
                            , normalizeDescription, normalizeStructural, variablesV ) where

import Control.Monad.State
import Backend.Typed.Syntax
import Backend.Typed.Types( Types(..), inst, prodV )
import Backend.Typed.Common( child )
import Backend.Typed.Layout( layout, orderFields )

normalizeAType :: AType -> AType
normalizeAType a = case a of
  ABox t -> ABox (normalizeVType t)
  AScalar t -> AScalar (normalizeVType t)
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
  VReuse f n p -> VReuse f n (p >>= normalizeDescription)
  _ -> t
  where
    productType s = let { (vs,fs) = productParts s
                       ; body = prodV [normalizeVType (fs !! i) | i <- productOrder fs] }
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

productOrder :: [VType] -> [Int]
productOrder fs = map fst (orderFields [(i,layout t) | (i,t) <- zip [0..] fs])

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
  AScalar t -> variablesV t
  ASum ts -> concatMap (variablesA . snd) ts
  AFun ps r -> concatMap (variablesV . snd) ps ++ variablesV r
  AForall vs b -> vs ++ variablesA b
  ALam vs b -> vs ++ variablesA b
  AVar v -> [v]
  AApp v ts -> v : concatMap variablesA ts
  ACon _ ts -> concatMap variablesA ts
  AUnit -> []

normalizeDescription :: Contents -> Maybe Contents
normalizeDescription (Contents k v t)
  | not (known t v) = Nothing
  | otherwise = Just (Contents k (normalizeStructural t v) (normalizeVType t))
  where
    -- Hoisting an opaque existential would require opening its witnesses in a
    -- non-executable description. Forget this optional fact instead. Credits
    -- obtained by UnboxRu still describe their normalized contents directly.
    known _ Var{} = True
    known s w = case (s,w) of
      (VProd{},_) -> fields s w
      (VExists{},_) -> fields s w
      (VSum ts,Inj i _ x) -> known (ts !! i) x
      _ -> True
    fields s w = case (s,w) of
      (VProd a b,Pair x y) -> fields a x && fields b y
      (VProd a b,Var x) -> fields a (Var (child x SFst)) && fields b (Var (child x SSnd))
      (VExists vs b,Pack _ ts x) -> fields (inst vs ts b) x
      (VExists{},_) -> False
      _ -> known s w

-- Descriptions are structural and may name parts outside their scope. No
-- executable destructurings are needed here; OrderFields renames these paths.
normalizeStructural :: VType -> VVal -> VVal
normalizeStructural _ v@Var{} = v
normalizeStructural t v = case (t,v) of
  (VProd{},_) -> productValue t v
  (VExists{},_) -> productValue t v
  (VSum ts,Inj i _ w) -> Inj i (normalizeVType t) (normalizeStructural (ts !! i) w)
  (_,TyApp w ts) -> TyApp w (map normalizeAType ts)
  _ -> v
  where
    productValue s w = let { (ws,fs) = gather s w
                          ; value = pairValues [b | i <- productOrder (map fst fs), let (_,b) = fs !! i] }
                      in if null ws then value else Pack (normalizeVType s) (map normalizeAType ws) value
    gather s w = case (s,w) of
      (VProd a b,Pair x y) -> gather a x <> gather b y
      (VProd a b,Var x) -> gather a (Var (child x SFst)) <> gather b (Var (child x SSnd))
      (VExists vs b,Pack _ ts x) -> let (ws,fs) = gather (inst vs ts b) x in (ts ++ ws,fs)
      (VExists _ b,Var x) -> gather b (Var (child x SPack))
      (VUnit,_) -> ([],[])
      _ -> ([],[(s,normalizeStructural s w)])
    pairValues [] = UnitV
    pairValues [w] = w
    pairValues (w:ws) = Pair w (pairValues ws)

