-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Elab.Coerce( coerce, genVal, genPtr, applyFun ) where

import qualified Data.Map as M
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Types
import Backend.Typed.Elab.Monad
import Backend.Typed.Pretty( ppr )

-- a pointer to a value `w : A`, generalized at `(∀ā. A)*`
genVal :: VType -> AVal -> E (K,VVal)
genVal t@(VPtr (AForall _ a)) w = genPtr t (Ptr a w)
genVal t@(VPtr a) w = genPtr t (Ptr a w)
genVal t _ = failE ("not a pointer type: " ++ ppr t)

-- a pointer `v : A*`, generalized at `(∀ā. A)*`
genPtr :: VType -> VVal -> E (K,VVal)
genPtr t@(VPtr (AForall tvs _)) v
  = do x <- fresh "l"
       return (Let x t (Gen tvs (Ret v)), Var x)
genPtr _ v = return (id, v)

coerce :: VType -> VType -> VVal -> E (K,VVal)
coerce from to v
  | alphaEq from to = return (id,v)
  | not (isPtr from) && alphaEq to (boxrep from) = boxV from v
  | not (isPtr to) && alphaEq from (boxrep to) = unboxV to v
  | otherwise
  = case (from,to) of
      (VPtr a, VPtr b) | Just (tvs,itvs,ps,r,qs,s) <- funPair a b -> wrapFun tvs itvs ps r qs s v
      (VPtr (AForall tvs a), _) | Just sub <- match tvs a (ptrA to) -> instPoly tvs a sub v to
      _ -> failE ("cannot coerce " ++ ppr from ++ " to " ++ ppr to)

-- a sum is boxed by a case on it (and on its nested sums), and each alternative builds the whole
-- boxed value at once, so that no variable is bound at a boxed type
boxV :: VType -> VVal -> E (K,VVal)
boxV t v
  | isMultiSum t = do r <- fresh "b"
                      body <- boxAV t v (return . Ret . Ptr (boxA t))
                      return (Let r (VPtr (boxA t)) body, Var r)
  | otherwise    = return (id, Ptr (boxA t) (boxLeaf t v))

-- the boxed form `a : boxA(t)` of `v : t`, given to the continuation in every alternative
boxAV :: VType -> VVal -> (AVal -> E VExpr) -> E VExpr
boxAV t v k
  | VSum ts <- t, isMultiSum t = CaseV Owned v <$> mapM (boxAlt ts k) (zip [0..] ts)
  | otherwise                  = k (boxLeaf t v)

-- as `boxA` on a type that is not a sum of several alternatives
boxLeaf :: VType -> VVal -> AVal
boxLeaf t v
  = case t of
      VUnit       -> UnitA
      VSum _      -> Box v
      VPtr _      -> Box v
      VProd _ _   -> Box v
      VRaw _      -> Box v
      VExists _ _ -> Box v
      VReuse _ _    -> Box v
      VCtx _ _    -> Box v

boxAlt :: [VType] -> (AVal -> E VExpr) -> (Int,VType) -> E (Path,VExpr)
boxAlt ts k (i,ti)
  = do y <- fresh "y"
       body <- boxAV ti (Var y) (k . injA (map boxA ts) i)
       return (y, body)

isMultiSum :: VType -> Bool
isMultiSum (VSum ts) = length ts > 1
isMultiSum _         = False

unboxV :: VType -> VVal -> E (K,VVal)
unboxV t v
  = do a <- fresh "u"
       (k,w) <- unboxAV t a
       return (Deref Owned v a . k, w)

unboxAV :: VType -> Path -> E (K,VVal)
unboxAV t a
  = case t of
      VUnit -> return (id, UnitV)
      VSum ts | length ts > 1 ->
        do r <- fresh "s"
           body <- caseSum fresh (map boxA ts) a (unboxAlt t ts)
           return (Let r t body, Var r)
      VSum _      -> unbox
      VPtr _      -> unbox
      VProd _ _   -> unbox
      VRaw _      -> unbox
      VExists _ _ -> unbox
      VReuse _ _    -> unbox
      VCtx _ _    -> unbox
  where
    unbox = do x <- fresh "x"   -- as `boxA`
               return (Unbox Owned a x, Var x)

unboxAlt :: VType -> [VType] -> Int -> Path -> E VExpr
unboxAlt t ts i y
  = do (k,w) <- unboxAV (ts !! i) y
       return (k (Ret (Inj i t w)))

ptrA :: VType -> AType
ptrA (VPtr a) = a
ptrA t        = ABox t

instPoly :: [TVar] -> AType -> Sub -> VVal -> VType -> E (K,VVal)
instPoly tvs a sub v to
  = coerce (VPtr (subst sub a)) to (TyApp v [M.findWithDefault atAny tv sub | tv <- tvs])

funPair :: AType -> AType -> Maybe ([TVar],[TVar],[(Mode,VType)],VType,[(Mode,VType)],VType)
funPair a b
  = case (a,b) of
      (AFun ps r, AFun qs s) | length ps == length qs -> Just ([],[],ps,r,qs,s)
      (AFun ps r, AForall bs (AFun qs s)) | length ps == length qs -> Just (bs,[],ps,r,qs,s)
      (AForall as (AFun ps r), AForall bs b') | length as == length bs
        -> case inst bs (map AVar as) b' of
             AFun qs s | length ps == length qs -> Just (as,as,ps,r,qs,s)
             _ -> Nothing
      _ -> Nothing

wrapFun :: [TVar] -> [TVar] -> [(Mode,VType)] -> VType -> [(Mode,VType)] -> VType -> VVal -> E (K,VVal)
wrapFun tvs itvs ps r qs s v
  = do ys <- mapM (const (fresh "w")) qs
       (ks,args) <- unzip <$> mapM (\((_,q),(_,p),y) -> coerce q p (Var y)) (zip3 qs ps ys)
       x  <- fresh "r"
       (kr,res) <- coerce r s (Var x)
       call <- applyFun (tapp v (map AVar itvs)) args
       let body = compose ks (Let x r call (kr (Ret res)))
           lam  = Lam [(y,m,q) | (y,(m,q)) <- zip ys qs] s body
       genVal (VPtr (forallA tvs (AFun qs s))) lam

-- Immediately applied coercion adapters need no closure. Bind arguments outside
-- the lambda's scope first, so its parameters cannot capture names in later arguments.
-- A top-level function is called directly rather than through its static closure.
applyFun :: VVal -> [VVal] -> E VExpr
applyFun (Ptr _ (Lam ps _ body)) args
  = do xs <- mapM (const (fresh "arg")) args
       let bind (x,t,v) = Let x t (Ret v)
           actuals = [(x,t,v) | (x,(_,_,t),v) <- zip3 xs ps args]
           formals = [(p,t,Var x) | ((p,_,t),x) <- zip ps xs]
       return (compose (map bind actuals ++ map bind formals) body)
applyFun fv args
  | Just (f,tys) <- knownFun fv []
  = return (Call f tys args)
  | otherwise
  = do g <- fresh "f"
       return (Deref Owned fv g (App g args))

-- a top-level function applied to all its type arguments; as a closure its parameters are owned
knownFun :: VVal -> [AType] -> Maybe (Name,[AType])
knownFun v tys
  = case v of
      TyApp w tys'                                           -> knownFun w (tys' ++ tys)
      Ptr (AForall tvs _) (Fun f) | length tvs == length tys -> Just (f,tys)
      Ptr (AFun _ _) (Fun f)      | null tys                 -> Just (f,tys)
      _                                                      -> Nothing
