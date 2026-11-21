-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Elab.Coerce( coerce, coerceInst, coerceExpr, genVal, genPtr, applyFun ) where

import qualified Data.Map as M
import Data.Maybe( isJust )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Build( K, compose, yieldedWith )
import Backend.Typed.Traversal( child, hasRegion )
import Backend.Typed.Types
import Backend.Typed.Layout( leaves )
import Backend.Typed.Elab.TypeMatch( match )
import Backend.Typed.Elab.Representation
import Backend.Typed.Elab.Monad
import Control.Monad.Reader( asks )
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

-- A value is injected into `W?` by `[some]`. A value `V?` (a result that Koka does not test)
-- is used as a `V` after a test for null (`extractNull`), and as a `W?` by a test that maps
-- its V. A function used where its results may yield (`addsNull`) is cast (`[cast-ev]`), not
-- eta-expanded: it does not yield, so the tests of its callers take the non-yielding branch.
coerce :: VType -> VType -> VVal -> E (K,VVal)
coerce from to v
  | alphaEq from to = return (id,v)
  | VOrNull w <- to, not (isNull from)
  = do (k,v') <- coerce from w v
       return (k, Some v')
  | VOrNull f <- from, not (isNull to)
  = do (k1,w) <- extractNull f v
       (k2,u) <- coerce f to w
       return (k1 . k2, u)
  | VOrNull f <- from, VOrNull t <- to, not (addsNull from to)
  = mapNull f t v
  | addsNull from to = castV from to v
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
                      body <- leafAV t v (\i a -> return (Ret (Ptr (boxA t) (injA (shapeLeaves t) i a))))
                      return (Let r (VPtr (boxA t)) body, Var r)
  | VRaw r <- t  = return (id, Ptr (AScalar r) (Scalar v))
  | Just s <- scalarField t = do (k1,w) <- fieldOf t v
                                 (k2,b) <- boxV s w
                                 return (k1 . k2, b)
  | otherwise    = return (id, Ptr (boxA t) (boxLeaf t v))

-- the only field `w` of `v : t` (`scalarField`)
fieldOf :: VType -> VVal -> E (K,VVal)
fieldOf t v
  = case t of
      VProd fs -> do x <- fresh "f"
                     let i = leafField fs
                     (k,w) <- fieldOf (snd (fs !! i)) (Var x)
                     return (Proj v i x . k, w)
      VExists tvs b -> do x <- fresh "f"
                          (k,w) <- fieldOf b (Var x)
                          return (Unpack v tvs x . k, w)
      _ -> return (id, v)

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

-- the boxed leaf of `v : t` and its position in `shapeLeaves(t)`, given to the continuation in
-- every alternative
leafAV :: VType -> VVal -> (Int -> AVal -> E VExpr) -> E VExpr
leafAV t v k
  | VSum ts <- t, isMultiSum t = CaseV v <$> mapM alt (zip3 [0..] (leafStarts ts) ts)
  | otherwise                  = k 0 (boxLeaf t v)
  where
    alt (i,start,(c,ti)) = do y <- case v of
                                     Var z -> return (child z (SInjV i c))
                                     _     -> fresh "y"
                              body <- leafAV ti (Var y) (k . (+ start))
                              return (i, y, body)

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

unboxV :: VType -> VVal -> E (K,VVal)
unboxV t v
  = do a <- fresh "u"
       (k,w) <- unboxAV t a
       return (Deref v a . k, w)

unboxAV :: VType -> Path -> E (K,VVal)
unboxAV t a
  | Just s <- scalarField t
  = do (k,w) <- unboxAV s a
       return (k, withField t w)
  | otherwise
  = case t of
      VUnit -> return (id, UnitV)
      VSum ts | isMultiSum t ->
        do r <- fresh "s"
           body <- caseSum (leafCons ts) (shapeLeaves t) a (\j y -> (\(k,w) -> k (Ret w)) <$> unboxLeaf t j y)
           return (Let r t body, Var r)
      VSum _      -> unbox Unbox
      VPtr _      -> unbox Unbox
      VProd _     -> unbox Unbox
      VRaw _      -> unbox (Unscalar Owned)
      VExists _ _ -> unbox Unbox
      VReuse _ _ _  -> unbox Unbox
      VCtx _ _ _  -> unbox Unbox
      VCell _ _   -> unbox Unbox
      VOrNull _   -> unbox Unbox
      VToken      -> unbox Unbox
  where
    unbox form = do x <- fresh "x"
                    return (form a x, Var x)

-- the value of type `t` whose leaf at position `j` is `y`
unboxLeaf :: VType -> Int -> Path -> E (K,VVal)
unboxLeaf t j y
  | VSum ts <- t, isMultiSum t
  = do let (i,start) = last [(i,s) | (i,s) <- zip [0..] (leafStarts ts), s <= j]
       (k,w) <- unboxLeaf (snd (ts !! i)) (j - start) y
       return (k, Inj i t w)
  | otherwise = unboxAV t y

-- whether two types differ only in their `?`s and tokens, but not in a token at the top, so
-- that `[cast-ev]` relates them
castable :: VType -> VType -> Bool
castable from to = alphaEq (eraseEv from) (eraseEv to) && holdsToken from == holdsToken to

-- `to` is `from` with `?`s and tokens added to the results of functions (`V` to `V? ⊗ KCtx`),
-- where function parameters are contravariant and all other types are compared as they are
addsNull :: VType -> VType -> Bool
addsNull from to
  | alphaEq from to = True
  | Just t <- unToken to, Nothing <- unToken from = addsNull from t
  | Just f <- unToken from, Just t <- unToken to = addsNull f t
  | VOrNull t <- to, not (isNull from) = addsNull from t
  | VOrNull f <- from, VOrNull t <- to = addsNull f t
  | VPtr a <- from, VPtr b <- to = addsA a b
  | otherwise = False
  where
    addsA (AFun ps r) (AFun qs s)
      = let (ps0,pk) = tokenParam ps
            (qs0,qk) = tokenParam qs
        in (qk || not pk) && length ps0 == length qs0 && and [m == n && addsNull q p | ((m,p),(n,q)) <- zip ps0 qs0] && addsNull r s
    addsA (AForall as a) (AForall bs b)
      = length as == length bs && addsA a (inst bs (map AVar as) b)
    addsA _ _ = False

-- The V of `v : V?`, which is not null as Koka does not test it: `let x : V = is-null v of
-- { null -> unreachable; y -> ret y }`. In the definitions that pass on a dummy where Koka
-- expects a value (`envTrusted`), it is cast instead.
extractNull :: VType -> VVal -> E (K,VVal)
extractNull f v
  = do trusted <- asks envTrusted
       if trusted then castV (orNull f) f v
         else do x <- fresh "x"
                 y <- fresh "y"
                 return (Let x f (IsNull v (Unreachable f) (y, Ret (Var y))), Var x)

-- `v : V?` at `W?`: the null is the null of W, and the V is coerced to W
mapNull :: VType -> VType -> VVal -> E (K,VVal)
mapNull f t v
  = do x <- fresh "x"
       y <- fresh "y"
       (k,w) <- coerce f t (Var y)
       return (Let x (orNull t) (IsNull v (Ret (Null t)) (y, k (Ret (Some w)))), Var x)

-- `v` at the type `to` (`[cast-ev]`)
castV :: VType -> VType -> VVal -> E (K,VVal)
castV from to v
  = do x <- fresh "c"
       return (Let x to (CastEv from to (Ret v)), Var x)

-- The value `v` of a generic type instantiated at `from`, at its Koka instance `to`. The IR
-- has no effects, so the `?`s and tokens of `from` follow the effect variables of the generic type, while
-- `to` follows their instances. Where these differ only in `?`s and tokens (an effect variable
-- instantiated at a total effect), a function value is wrapped (`wrapped`), whose results are
-- tested for null, and a value that holds functions under a type constructor, as in
-- `list<(int, KCtx) -> int? ⊗ KCtx>` at `list<(int) -> int>`, is cast (`[cast-ev]`): this
-- trusts Koka's typing. A `V?` at a `V` is tested for null (`extractNull`).
coerceInst :: VType -> VType -> VVal -> E (K,VVal)
coerceInst from to v
  | VOrNull f <- from, not (isNull to)
  = do (k1,w) <- extractNull f v
       (k2,u) <- coerceInst f to w
       return (k1 . k2, u)
  | not (alphaEq from to) && castable from to && not (wrapped from to) = castV from to v
  | otherwise = coerce from to v

-- A function value whose type differs only in `?`s and tokens, but not as `addsNull`, is
-- wrapped (`wrapFun`), so that its results are tested for null rather than cast
wrapped :: VType -> VType -> Bool
wrapped from to
  = case (from,to) of
      (VPtr a, VPtr b) -> isJust (funPair a b) && not (addsNull from to)
      _ -> False

isNull :: VType -> Bool
isNull t = case t of
             VOrNull _ -> True
             _ -> False

-- The expression `e : from` at the type `to`. Where both may be the dummy of a yield, a
-- result `U? ⊗ KCtx` is tested for a yield (`[if-yielding]` on its token), its U is
-- extracted (`[is-null]`), and the yielding branch is the dummy (`Build.yieldedWith`).
-- Otherwise, Koka does not test the result: it knows that it cannot yield (such as the
-- result of an effect-polymorphic function at a total effect, of a `deref`, or of a call
-- through `unsafe-total-cast`, which makes it look total), or the code tests the flag itself
-- (`std/core/hnd`, and its `local-var` and `finally` where they are inlined: there the result
-- may be a dummy, which elaboration passes on at `V?` to `prompt-local-var` or
-- `finally-prompt`). A result that differs from `to` only in `?`s and tokens is then cast
-- (`[cast-ev]`), except that its `?` at the top is removed by a test for null (`checked`),
-- added by `[some]`, and a function value is wrapped (`wrapped`). A coercion (such as an unboxing) would inspect a dummy, so it is tested,
-- and the yielding branch passes on a dummy of the type `to` (cast from `to?`), as Koka does.
--
-- The token of a token-threaded `to` is that of `from`, or the current token (`takeToken`)
-- if `from` has none. A `from` with a token is coerced only to a `to` with one: code without
-- a token calls a function that takes one in a `[total]` region (`region`), whose result
-- has a token.
coerceExpr :: VType -> VType -> VExpr -> E VExpr
coerceExpr from to e
  | alphaEq from to = return e
  | Just to0 <- unToken to, Nothing <- unToken from
  = do (kt,k) <- takeToken
       kt <$> coerceTo from to0 e (\v -> Ret (Tuple [v,k]))
  | castable from to && yields from && not (yields to)
  = checked from to e
  | castable from to && (yields from || not (yields to)) && not (wrapped from to)
  = return (CastEv from to e)
  | Just from0 <- unToken from, Just to0 <- unToken to
  = tested from0 to0 to e
  | otherwise
  = coerceTo from to e Ret

-- `e : U?` or `U? ⊗ KCtx`, which Koka does not test, at `to`: its U is extracted by a test for
-- null, which fails only if Koka's typing is wrong (cast instead where `envTrusted`)
checked :: VType -> VType -> VExpr -> E VExpr
checked from to e
  = do trusted <- asks envTrusted
       if trusted then return (CastEv from to e) else checkedNull from to e

checkedNull :: VType -> VType -> VExpr -> E VExpr
checkedNull from to e
  = do r <- fresh "r"
       y <- fresh "y"
       let from' = maybe (unNull from) (withToken . unNull) (unToken from)
       body <- case unToken from of
                 Just _ -> do r0 <- fresh "r"
                              k <- fresh "k"
                              return (Proj (Var r) 0 r0 (Proj (Var r) 1 k (IsNull (Var r0) (Unreachable from') (y, Ret (Tuple [Var y, Var k])))))
                 Nothing -> return (IsNull (Var r) (Unreachable from') (y, Ret (Var y)))
       coerceExpr from' to (Let r from e body)

-- `e : from`, which is not the dummy, at `to`, given the tail `ret` of a value
coerceTo :: VType -> VType -> VExpr -> (VVal -> VExpr) -> E VExpr
coerceTo from to e ret
  = do r <- fresh "r"
       (k,v) <- coerce from to (Var r)
       return (Let r from e (k (ret v)))

-- `e : from₀ ⊗ KCtx` at `to₀ ⊗ KCtx` (`to`), tested for a yield if `from₀` may be the dummy
tested :: VType -> VType -> VType -> VExpr -> E VExpr
tested from0 to0 to e
  = do r <- fresh "r"
       r0 <- fresh "r"
       k <- fresh "k"
       (k1,w) <- extract from0 r0 to
       (k2,v) <- coerce (unNull from0) to0 w
       let value t = k1 (k2 (Ret (Tuple [v,Var t])))
       test <- if yields from0
                 then do k3 <- fresh "k"
                         k2' <- fresh "k"
                         return (IfYielding (Var k) (k3, yieldedWith to (Var k3)) (k2', value k2'))
                 else return (value k)
       return (Let r (withToken from0) e (Proj (Var r) 0 r0 (Proj (Var r) 1 k test)))

-- the value of `r : u` after a test for a yield, extracted if `u` is `V?` (in an expression of
-- type `full`)
extract :: VType -> Path -> VType -> E (K,VVal)
extract u r full
  = case u of
      VOrNull _ -> do y <- fresh "y"
                      return (\body -> IsNull (Var r) (Unreachable full) (y,body), Var y)
      _ -> return (id, Var r)

ptrA :: VType -> AType
ptrA (VPtr a) = a
ptrA t        = boxA t

instPoly :: [TVar] -> AType -> Sub -> VVal -> VType -> E (K,VVal)
instPoly tvs a sub v to
  = coerce (VPtr (subst sub a)) to (TyApp v [M.findWithDefault atAny tv sub | tv <- tvs])

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

-- A function `v` with the parameters `ps` as one with the parameters `qs`. The token of the
-- wrapper is that of `v`; without one, the result of `v` gets the token of the wrapper, or
-- the call of `v` is a `[total]` region (`region`).
wrapFun :: [TVar] -> [TVar] -> [(Mode,VType)] -> VType -> [(Mode,VType)] -> VType -> VVal -> E (K,VVal)
wrapFun tvs itvs ps r qs s v
  = do ys <- mapM (const (fresh "w")) qs
       let (qs0,qk) = tokenParam qs
           (ps0,pk) = tokenParam ps
           token = if qk then Just (last ys) else Nothing
       (ks,args) <- unzip <$> mapM (\((_,q),(_,p),y) -> coerceInst q p (Var y)) (zip3 qs0 ps0 ys)
       body <- tokenIn token $ withResult s $ (if pk then region else id) $
               do (kt,targs) <- takeTokenIf pk
                  call <- applyFun (AFun ps r) (tapp v (map AVar itvs)) (args ++ targs)
                  expect <- result
                  compose ks . kt <$> coerceExpr r expect call
       let lam  = Lam [(y,m,q) | (y,(m,q)) <- zip ys qs] s body
       genVal (VPtr (forallA tvs (AFun qs s))) lam

-- Immediately applied coercion adapters need no closure, unless the adapter is a `[total]`
-- region in token-threaded code. Bind arguments outside
-- the lambda's scope first, so its parameters cannot capture names in later arguments.
-- A top-level function is called directly rather than through its static closure. Any
-- other function value of type `a` is bound first, so that the closure that `[app]`
-- consumes is a child of a variable, which can be duplicated (`[dup]` is on pointers).
applyFun :: AType -> VVal -> [VVal] -> E VExpr
applyFun a f@(Ptr _ (Lam ps _ body)) args
  = do token <- currentToken
       if isJust token && hasRegion body then applyClosure a f args else inlineFun ps body args
applyFun a fv args
  | Just (f,tys) <- knownFun fv []
  = return (Call f tys args)
  | otherwise
  = applyClosure a fv args

inlineFun :: [(Path,Mode,VType)] -> VExpr -> [VVal] -> E VExpr
inlineFun ps body args
  = do xs <- mapM (const (fresh "arg")) args
       let bind (x,t,v) = Let x t (Ret v)
           actuals = [(x,t,v) | (x,(_,_,t),v) <- zip3 xs ps args]
           formals = [(p,t,Var x) | ((p,_,t),x) <- zip ps xs]
       return (compose (map bind actuals ++ map bind formals) body)

applyClosure :: AType -> VVal -> [VVal] -> E VExpr
applyClosure a fv args
  = do s <- fresh "f"
       let g = child s SDeref
       return (Let s (VPtr a) (Ret fv) (Deref (Var s) g (App g args)))

-- a top-level function applied to all its type arguments; as a closure its parameters are owned
knownFun :: VVal -> [AType] -> Maybe (Name,[AType])
knownFun v tys
  = case v of
      TyApp w tys'                                           -> knownFun w (tys' ++ tys)
      Ptr (AForall tvs _) (Fun f) | length tvs == length tys -> Just (f,tys)
      Ptr (AFun _ _) (Fun f)      | null tys                 -> Just (f,tys)
      _                                                      -> Nothing
