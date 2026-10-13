-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Coerce( coerce, genVal, injA, caseChain, tapp ) where

import qualified Data.Map as M
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Types
import Backend.Typed.ElabMonad
import Backend.Typed.Pretty( ppr )

genVal :: VType -> Val -> E (K,Val)
genVal t@(VPtr (AForall tvs a)) w
  = do x <- fresh "l"
       return (Let x (V t) (Gen tvs (Ret (Fold (VPtr a) w))), Var x)
genVal t w = return (id, Fold t w)

tapp :: Val -> [VType] -> Val
tapp v []  = v
tapp v tys = TyApp v tys

sumOf :: [AType] -> AType
sumOf = foldr1 ASum

injA :: [AType] -> Int -> Val -> Val
injA [_] 0 v = v
injA ss 0 v  = Inl (sumOf ss) v
injA ss i v  = Inr (sumOf ss) (injA (tail ss) (i-1) v)

coerce :: VType -> VType -> Val -> E (K,Val)
coerce from to v
  | alphaEq from to = return (id,v)
  | not (isPtr from) && alphaEq to (boxrep from) = boxV from v
  | not (isPtr to) && alphaEq from (boxrep to) = unboxV to v
  | otherwise
  = case (from,to) of
      (VPtr a, VPtr b) | Just (tvs,itvs,ps,r,qs,s) <- funPair a b -> wrapFun tvs itvs ps r qs s v
      (VPtr (AForall tvs a), _) | Just sub <- match tvs a (ptrA to) -> instPoly tvs a sub v to
      _ -> failE ("cannot coerce " ++ ppr from ++ " to " ++ ppr to)

boxV :: VType -> Val -> E (K,Val)
boxV t v
  = do (k,a) <- boxAV t v
       return (k, Fold (VPtr (boxA t)) a)

boxAV :: VType -> Val -> E (K,Val)
boxAV t v
  = case t of
      VUnit -> return (id, Unit)
      VSum ts | length ts > 1 ->
        do r <- fresh "b"
           alts <- mapM (boxAlt ts) (zip [0..] ts)
           return (Let r (A (boxA t)) (CaseV Owned v alts), Var r)
      VSum _      -> box
      VVar _      -> box
      VApp _ _    -> box
      VCon _ _    -> box
      VPtr _      -> box
      VProd _ _   -> box
      VRaw _      -> box
      VExists _ _ -> box
      VTLam _ _   -> box
      VReuse _    -> box
  where
    box = return (id, Box v)   -- as `boxA`

boxAlt :: [VType] -> (Int,VType) -> E (Name,Expr)
boxAlt ts (i,ti)
  = do y <- fresh "y"
       (k,a) <- boxAV ti (Var y)
       return (y, k (Ret (injA (map boxA ts) i a)))

unboxV :: VType -> Val -> E (K,Val)
unboxV t v
  = do a <- fresh "u"
       (k,w) <- unboxAV t (Var a)
       return (Unfold Owned v a . k, w)

unboxAV :: VType -> Val -> E (K,Val)
unboxAV t a
  = case t of
      VUnit -> return (id, Unit)
      VSum ts | length ts > 1 ->
        do r <- fresh "s"
           body <- caseChain (map boxA ts) a (unboxAlt t ts)
           return (Let r (V t) body, Var r)
      VSum _      -> unbox
      VVar _      -> unbox
      VApp _ _    -> unbox
      VCon _ _    -> unbox
      VPtr _      -> unbox
      VProd _ _   -> unbox
      VRaw _      -> unbox
      VExists _ _ -> unbox
      VTLam _ _   -> unbox
      VReuse _    -> unbox
  where
    unbox = do x <- fresh "x"   -- as `boxA`
               return (Unbox Owned a x, Var x)

unboxAlt :: VType -> [VType] -> Int -> Name -> E Expr
unboxAlt t ts i y
  = do (k,w) <- unboxAV (ts !! i) (Var y)
       return (k (Ret (Inj i t w)))

caseChain :: [AType] -> Val -> (Int -> Name -> E Expr) -> E Expr
caseChain shapes a branch = go 0 shapes a
  where
    go i [_] v = do y <- fresh "y"
                    body <- branch i y
                    return (Let y (A (shapes !! i)) (Ret v) body)
    go _ [] _ = failE "empty case chain"
    go i (_:rest) v
      = do y <- fresh "y"
           z <- fresh "z"
           b1 <- branch i y
           b2 <- go (i+1) rest (Var z)
           return (CaseA Owned v (y,b1) (z,b2))

ptrA :: VType -> AType
ptrA (VPtr a) = a
ptrA t        = ABox t

instPoly :: [TVar] -> AType -> Sub -> Val -> VType -> E (K,Val)
instPoly tvs a sub v to
  = do g <- fresh "i"
       let ai = subst sub a
       (k,w) <- coerce (VPtr ai) to (Fold (VPtr ai) (TyApp (Var g) [M.findWithDefault vtAny tv sub | tv <- tvs]))
       return (Unfold Owned v g . k, w)

funPair :: AType -> AType -> Maybe ([TVar],[TVar],[(Mode,VType)],VType,[(Mode,VType)],VType)
funPair a b
  = case (a,b) of
      (AFun ps r, AFun qs s) | length ps == length qs -> Just ([],[],ps,r,qs,s)
      (AFun ps r, AForall bs (AFun qs s)) | length ps == length qs -> Just (bs,[],ps,r,qs,s)
      (AForall as (AFun ps r), AForall bs b') | length as == length bs
        -> case inst bs (map VVar as) b' of
             AFun qs s | length ps == length qs -> Just (as,as,ps,r,qs,s)
             _ -> Nothing
      _ -> Nothing

wrapFun :: [TVar] -> [TVar] -> [(Mode,VType)] -> VType -> [(Mode,VType)] -> VType -> Val -> E (K,Val)
wrapFun tvs itvs ps r qs s v
  = do ys <- mapM (const (fresh "w")) qs
       g  <- fresh "g"
       (ks,args) <- unzip <$> mapM (\((_,q),(_,p),y) -> coerce q p (Var y)) (zip3 qs ps ys)
       x  <- fresh "r"
       (kr,res) <- coerce r s (Var x)
       let body = Unfold Owned v g (compose ks (Let x (V r) (App (tapp (Var g) (map VVar itvs)) args) (kr (Ret res))))
           lam  = Lam [(y,m,q) | (y,(m,q)) <- zip ys qs] s body
       genVal (VPtr (forallA tvs (AFun qs s))) lam
