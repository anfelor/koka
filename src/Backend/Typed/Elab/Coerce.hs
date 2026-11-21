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
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Build( K, compose, yielded, yieldedWith, dropToken )
import Backend.Typed.Traversal( child )
import Backend.Typed.Types
import Backend.Typed.Layout( leaves )
import Backend.Typed.Elab.TypeMatch( match )
import Backend.Typed.Elab.Representation
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

-- A value is injected into `W?` by `[some]`. A value that may be null is not coerced:
-- `coerceExpr` tests the result of a call, or casts it where Koka does not test it. A function
-- used where its results may yield (`addsNull`) is cast (`[cast-ev]`), not eta-expanded: it
-- does not yield, so the tests of its callers take the non-yielding branch.
coerce :: VType -> VType -> VVal -> E (K,VVal)
coerce from to v
  | alphaEq from to = return (id,v)
  | VOrNull w <- to, not (isNull from)
  = do (k,v') <- coerce from w v
       return (k, Some v')
  | VOrNull _ <- from
  = failE ("cannot coerce " ++ ppr from ++ " to " ++ ppr to ++ " without a test for null")
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

-- whether two types differ only in their `?`s and tokens, so that `[cast-ev]` relates them
castable :: VType -> VType -> Bool
castable from to = alphaEq (eraseEv from) (eraseEv to)

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

-- `v` at the type `to` (`[cast-ev]`)
castV :: VType -> VType -> VVal -> E (K,VVal)
castV from to v
  = do x <- fresh "c"
       return (Let x to (CastEv from to (Ret v)), Var x)

-- The value `v` of a generic type instantiated at `from`, at its Koka instance `to`. The IR
-- has no effects, so the `?`s and tokens of `from` follow the effect variables of the generic type, while
-- `to` follows their instances. Where these differ only in `?`s and tokens (an effect variable
-- instantiated at a total effect, also under a type constructor, as in
-- `list<(int, KCtx) -> int? ⊗ KCtx>` at `list<(int) -> int>`), the value is cast (`[cast-ev]`):
-- Koka does not test its results.
coerceInst :: VType -> VType -> VVal -> E (K,VVal)
coerceInst from to v
  | not (alphaEq from to) && castable from to = castV from to v
  | otherwise = coerce from to v

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
-- may be a dummy, which `prompt-local-var` or `finally-prompt` receives). A result that
-- differs from `to` only in `?`s and tokens is then cast (`[cast-ev]`, unless that would add
-- a `?` at the top, which is `[some]`). A coercion (such as an unboxing) would inspect a
-- dummy, so it is tested, and the yielding branch passes on a dummy of the type `to` (cast
-- from `to?`), as Koka does.
--
-- The token of a token-threaded `to` is that of `from`, or the current token (`takeToken`)
-- if `from` has none. A token of `from` that `to` does not have is dropped by a cast (site 1
-- of "The effect token" in `Syntax`), or after its test.
coerceExpr :: VType -> VType -> VExpr -> E VExpr
coerceExpr from to e
  | alphaEq from to = return e
  | Just to0 <- unToken to, Nothing <- unToken from
  = do (kt,k) <- takeToken
       kt <$> coerceTo from to0 e (\v -> Ret (Tuple [v,k]))
  | castable from to && (yields from || not (yields to))
  = return (CastEv from to e)
  | Just from0 <- unToken from, Just to0 <- unToken to
  = tested True from0 to0 to e
  | Just from0 <- unToken from, yields from0
  = tested False from0 to to e
  | Just from0 <- unToken from
  = coerceExpr from0 to (CastEv from from0 e)
  | otherwise
  = coerceTo from to e Ret

-- `e : from`, which is not the dummy, at `to`, given the tail `ret` of a value
coerceTo :: VType -> VType -> VExpr -> (VVal -> VExpr) -> E VExpr
coerceTo from to e ret
  = do r <- fresh "r"
       (k,v) <- coerce from to (Var r)
       return (Let r from e (k (ret v)))

-- `e : from₀ ⊗ KCtx` at `to₀`, the type `to` without its token, tested for a yield if `from₀`
-- may be the dummy: the result passes on the token if `keep`, and otherwise drops it in both
-- branches
tested :: Bool -> VType -> VType -> VType -> VExpr -> E VExpr
tested keep from0 to0 to e
  = do r <- fresh "r"
       r0 <- fresh "r"
       k <- fresh "k"
       (k1,w) <- extract from0 r0 to
       (k2,v) <- coerce (unNull from0) to0 w
       let value t = k1 (k2 (Ret (if keep then Tuple [v,Var t] else v)))
           dummy t = if keep then yieldedWith to (Var t) else yielded to
           branch body t = if keep then return (t, body t)
                           else do u <- fresh "u"
                                   return (t, dropToken u (Var t) (body t))
       test <- if yields from0
                 then IfYielding (Var k) <$> (branch dummy =<< fresh "k") <*> (branch value =<< fresh "k")
                 else snd <$> branch value k
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
-- `v` gets a fresh token, which its result drops (`coerceExpr`).
wrapFun :: [TVar] -> [TVar] -> [(Mode,VType)] -> VType -> [(Mode,VType)] -> VType -> VVal -> E (K,VVal)
wrapFun tvs itvs ps r qs s v
  = do ys <- mapM (const (fresh "w")) qs
       let (qs0,qk) = tokenParam qs
           (ps0,pk) = tokenParam ps
           token = if qk then Just (last ys) else Nothing
       (ks,args) <- unzip <$> mapM (\((_,q),(_,p),y) -> coerce q p (Var y)) (zip3 qs0 ps0 ys)
       body <- tokenIn token $
               do (kt,targs) <- takeTokenIf pk
                  call <- applyFun (AFun ps r) (tapp v (map AVar itvs)) (args ++ targs)
                  compose ks . kt <$> coerceExpr r s call
       let lam  = Lam [(y,m,q) | (y,(m,q)) <- zip ys qs] s body
       genVal (VPtr (forallA tvs (AFun qs s))) lam

-- Immediately applied coercion adapters need no closure. Bind arguments outside
-- the lambda's scope first, so its parameters cannot capture names in later arguments.
-- A top-level function is called directly rather than through its static closure. Any
-- other function value of type `a` is bound first, so that the closure that `[app]`
-- consumes is a child of a variable, which can be duplicated (`[dup]` is on pointers).
applyFun :: AType -> VVal -> [VVal] -> E VExpr
applyFun _ (Ptr _ (Lam ps _ body)) args
  = do xs <- mapM (const (fresh "arg")) args
       let bind (x,t,v) = Let x t (Ret v)
           actuals = [(x,t,v) | (x,(_,_,t),v) <- zip3 xs ps args]
           formals = [(p,t,Var x) | ((p,_,t),x) <- zip ps xs]
       return (compose (map bind actuals ++ map bind formals) body)
applyFun a fv args
  | Just (f,tys) <- knownFun fv []
  = return (Call f tys args)
  | otherwise
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
