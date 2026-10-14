-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
-- Type inference and environment queries shared by typed IR consumers.
-- Keep inference in sync with the typing rules in Syntax.
module Backend.Typed.Query( Env(..), Gamma, envOf, bindAll, checkE, inferE, inferA, inferV
                          , inferVar, inferAVar, altTypes, boxContents, reuseSize, unrollT, openFields
                          , funSig, paramModes ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( zipWithM_, unless, when )
import Common.Name
import Lib.PPrint( Pretty )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Types
import Backend.Typed.Pretty( ppr )
import Backend.Typed.Layout( layout, blockSize, isBlock )

type Gamma = M.Map Name Ty

-- the join points that can be jumped to: their parameter types and result type
type Joins = M.Map Name ([VType],VType)

data Env = Env{ envTypes :: TypeDefs, envSigs :: Sigs }

type Q a = Either String a

envOf :: Program -> Env
envOf prog = Env (progTypes prog) (progSigs prog)

bindAll :: [(Name,Ty)] -> Gamma -> Gamma
bindAll bs g = foldr (uncurry M.insert) g bs

expect :: (Types t, Pretty t) => t -> t -> Q ()
expect t1 t2 = unless (alphaEq t1 t2) (Left ("type mismatch:\n  expected: " ++ ppr t1 ++ "\n  actual  : " ++ ppr t2))

-- jumps are only allowed in tail position: the joins are not visible in a let-bound
-- expression, a lambda or a generalization
checkE :: Env -> Gamma -> Joins -> VExpr -> VType -> Q ()
checkE env g js e t = inferE env g js e >>= expect t

inferE :: Env -> Gamma -> Joins -> VExpr -> Q VType
inferE env g js expr
  | Just ds <- destructAOf expr
  = do t <- inferAVar g (dsScrut ds)
       inferDestruct env g js expr (A t) (dsAlts ds)
  | Just ds <- destructVOf expr
  = do t <- inferV env g (dsScrut ds)
       inferDestruct env g js expr (V t) (dsAlts ds)
inferE env g js expr
  = case expr of
      Ret v -> inferV env g v
      Let x t e1 e2 -> do checkE env g M.empty e1 t
                          inferE env (M.insert x (V t) g) js e2
      Call f tys vs -> do (ps,r) <- funSig env f tys
                          checkArgs env g ps vs
                          return r
      App f vs -> do ft <- inferAVar g f
                     case ft of
                       AFun ps r -> do checkArgs env g (map snd ps) vs
                                       return r
                       _ -> Left ("applying a non-function: " ++ ppr ft)
      CaseLit v alts def -> do vt <- inferV env g v
                               mapM_ (\(l,_) -> expect vt (litType l)) alts
                               branches (inferE env g js def : [inferE env g js e | (_,e) <- alts])
      Drop x e -> inferAVar g x >> inferE env g js e
      Free r e -> do t <- inferV env g (Var r)
                     case t of
                       VReuse _ -> inferE env g js e
                       _ -> Left ("free of a non-credit: " ++ ppr t)
      Dup x y e -> do a <- inferAVar g x
                      when (containsReuse (A a)) (Left "cannot duplicate a reuse credit")
                      inferE env (M.insert y (A a) g) js e
      IsUnique x e1 e2 -> do _ <- inferAVar g x >>= boxContents >>= reuseSize
                             branches [inferE env g js e1, inferE env g js e2]
      UnboxRu v x r e -> do s <- inferAVar g v >>= boxContents
                            n <- reuseSize s
                            inferE env (bindAll [(x,V s),(r,V (VReuse n))] g) js e
      Join j ps e1 e2 -> do t <- inferE env (M.fromList [(x,V p) | (x,_,p) <- ps]) js e1
                            checkE env g (M.insert j ([p | (_,_,p) <- ps],t) js) e2 t
                            return t
      Jump j vs -> case M.lookup j js of
                     Just (ps,t) -> checkArgs env g ps vs >> return t
                     Nothing -> Left ("jump to " ++ show j ++ " outside of its scope or not in tail position")
      Gen tvs e -> do unbound tvs (ftvCtx g e)
                      t <- inferE env g M.empty e
                      case t of
                        VPtr a -> return (VPtr (AForall tvs a))
                        _ -> Left ("generalization of a non-pointer: " ++ ppr t)
      _ -> Left "unexpected destructuring form"

-- The two scrutinee categories share branch checking and existential escape checks.
inferDestruct :: Env -> Gamma -> Joins -> VExpr -> Ty -> [([Name],VExpr)] -> Q VType
inferDestruct env g js expr t alts
  = do tss <- altTypes env t expr
       unless (length alts == length tss) (Left "wrong number of alternatives")
       r <- branches [inferE env (bindAll (zip xs ts) g) js e | ((xs,e),ts) <- zip alts tss]
       case expr of
         Unpack _ _ tvs x e -> unbound tvs (ftv r ++ ftvCtx (M.delete x g) e)
         _ -> return ()
       return r

-- type variables bound by `gen` and `unpack` must not occur free in the context (or the result)
unbound :: [TVar] -> [TVar] -> Q ()
unbound tvs free
  = case filter (`elem` free) tvs of
      []    -> return ()
      (v:_) -> Left ("bound type variable escapes: " ++ ppr (AVar v))

-- the free type variables of the types of the free variables of an expression
ftvCtx :: Gamma -> VExpr -> [TVar]
ftvCtx g e = concat [ftv t | x <- S.toList (fvE e), Just t <- [M.lookup x g]]

-- the types of the binders of each alternative of a destructuring form, given the type of its scrutinee
altTypes :: Env -> Ty -> VExpr -> Q [[Ty]]
altTypes env t expr
  = case (expr,t) of
      (Unpair{}, V (VProd a b)) -> return [[V a, V b]]
      (CaseV _ _ alts, V (VSum ts)) | length ts == length alts -> return [[V s] | s <- ts]
      (CaseA{}, A (ASum a b)) -> return [[A a],[A b]]
      (Deref{}, V (VPtr a)) -> return [[A a]]
      (Unroll{}, A a) -> do b <- unrollT env a
                            return [[A b]]
      (Unbox{}, A (ABox s)) -> return [[V s]]
      (UnboxLazy{}, A (ABox s)) -> return [[V s]]
      (Unpack _ _ tvs _ _, V (VExists bs s)) | length bs == length tvs -> return [[V (inst bs (map AVar tvs) s)]]
      (CaseOpen _ _ alts _, A a) -> do fs <- mapM (\(c,_,_) -> openFields env c a) alts
                                       return ([[V f] | f <- fs] ++ [[]])
      _ -> Left ("cannot destructure a value of type " ++ ppr t)

branches :: [Q VType] -> Q VType
branches cs = do ts <- sequence cs
                 case ts of
                   []     -> Left "case without branches"
                   (t:rest) -> mapM_ (expect t) rest >> return t

funSig :: Env -> Name -> [AType] -> Q ([VType],VType)
funSig env f tys
  = case M.lookup f (envSigs env) of
      Just (SigFun tvs ps r) | length tvs == length tys
        -> return (map (inst tvs tys . snd) ps, inst tvs tys r)
      Just sig -> Left ("call of " ++ show f ++ " with " ++ show (length tys) ++ " type arguments: " ++ show sig)
      Nothing  -> Left ("unknown function: " ++ show f)

-- the modes of the parameters of a call with n arguments
paramModes :: Env -> Name -> Int -> [Mode]
paramModes env f n
  = case M.lookup f (envSigs env) of
      Just (SigFun _ ps _) -> map fst ps ++ replicate (n - length ps) Owned
      _ -> replicate n Owned

checkArgs :: Env -> Gamma -> [VType] -> [VVal] -> Q ()
checkArgs env g ps vs
  | length ps == length vs = zipWithM_ (\p v -> checkV env g v p) ps vs
  | otherwise = Left ("expecting " ++ show (length ps) ++ " arguments but got " ++ show (length vs))

-- `unroll(T⟨B̄⟩)`
unrollT :: Env -> AType -> Q AType
unrollT env t
  = case t of
      ACon n args -> case M.lookup n (envTypes env) of
                       Just (TypeDef _ tvs (Just body) _) | length tvs == length args -> return (inst tvs args body)
                       Just _  -> Left ("cannot unroll abstract type " ++ show n)
                       Nothing -> Left ("unknown type " ++ show n)
      _ -> Left ("unroll of " ++ ppr (A t))

-- the fields of an open constructor at an instance `T⟨B̄⟩` of its type
openFields :: Env -> Name -> AType -> Q VType
openFields env c t
  = case (M.lookup c (envSigs env), t) of
      (Just (SigCon tvs f n), ACon m args) | n == m && length tvs == length args -> return (inst tvs args f)
      (Just (SigCon _ _ _), _) -> Left ("open constructor " ++ show c ++ " does not match " ++ ppr (A t))
      _ -> Left ("unknown open constructor " ++ show c)

-- the contents `V` of a box `Box V`
boxContents :: AType -> Q VType
boxContents t
  = case t of
      ABox v -> return v
      _ -> Left ("not a box: " ++ ppr t)

-- the size `|V|` of the block of a box `Box V` that is always allocated on the heap
reuseSize :: VType -> Q Int
reuseSize v
  | isBlock (layout v) = return (blockSize (layout v))
  | otherwise          = Left ("no reusable block: " ++ ppr (A (ABox v)))

litType :: Lit -> VType
litType lit
  = case lit of
      LitInt _    -> vtInt
      LitString _ -> vtString
      LitChar _   -> vtChar
      LitFloat _  -> vtFloat

checkA :: Env -> Gamma -> AVal -> AType -> Q ()
checkA env g val t = inferA env g val >>= expect t

checkV :: Env -> Gamma -> VVal -> VType -> Q ()
checkV env g val t = inferV env g val >>= expect t

-- Look up a named operand; boxed eliminations and `drop` require A.
inferVar :: Gamma -> Name -> Q Ty
inferVar g x = maybe (Left ("unbound variable " ++ show x)) return (M.lookup x g)

inferAVar :: Gamma -> Name -> Q AType
inferAVar g x
  = do t <- inferVar g x
       case t of
         A a -> return a
         V _ -> Left ("boxed operand " ++ show x ++ " at the unboxed type " ++ ppr t)

checkShape :: AType -> Q ()
checkShape a = unless (isShape a) (Left ("sum alternatives must be shapes: " ++ ppr a))

noHeapCredit :: VType -> Q ()
noHeapCredit t = when (containsReuse (V t)) (Left "cannot store reuse credits in a heap block")

inferA :: Env -> Gamma -> AVal -> Q AType
inferA env g val
  = case val of
      Fun f -> case M.lookup f (envSigs env) of
                 Just (SigFun tvs ps r) -> return (forallA tvs (AFun ps r))
                 _ -> Left ("unknown function " ++ show f)
      UnitA -> return AUnit
      Inl a v -> case a of
                   ASum l _ -> checkShape a >> checkA env g v l >> return a
                   _ -> Left ("inl into " ++ ppr a)
      Inr a v -> case a of
                   ASum _ r -> checkShape a >> checkA env g v r >> return a
                   _ -> Left ("inr into " ++ ppr a)
      Roll a v -> do b <- unrollT env a
                     checkA env g v b
                     return a
      Box v -> do t <- inferV env g v
                  noHeapCredit t
                  return (ABox t)
      OpenCon c tys v
        -> case M.lookup c (envSigs env) of
             Just (SigCon tvs f n) | length tvs == length tys
               -> do noHeapCredit (inst tvs tys f)
                     checkV env g v (inst tvs tys f)
                     return (ACon n tys)
             _ -> Left ("unknown open constructor " ++ show c)
      Lam ps r e -> do when (any containsReuse [t | x <- S.toList (fvA val), Just t <- [M.lookup x g]])
                         (Left "cannot capture reuse credits in a closure")
                       checkE env (bindAll [(x,V t) | (x,_,t) <- ps] g) M.empty e r
                       return (AFun [(m,t) | (_,m,t) <- ps] r)
      BoxIn x v -> do tx <- inferV env g (Var x)
                      tv <- inferV env g v
                      noHeapCredit tv
                      case tx of
                        VPtr (ACon n args)
                          | Just (TypeDef _ tvs (Just body) (Just linfo)) <- M.lookup n (envTypes env)
                          , any (alphaEq (ABox tv)) (splitSum (length (lazyCons linfo)) (inst tvs args body))
                          -> return (ABox tv)
                        _ -> Left ("writing " ++ ppr tv ++ " into " ++ ppr tx)
      BoxAt r v -> do tr <- inferV env g (Var r)
                      tv <- inferV env g v
                      noHeapCredit tv
                      case tr of
                        VReuse n
                          -> do m <- reuseSize tv
                                unless (n == m) (Left ("reuse of a block of " ++ show n ++ " bytes for " ++ show m ++ " bytes"))
                                return (ABox tv)
                        _ -> Left ("allocation at " ++ ppr tr ++ " of " ++ ppr tv)

inferV :: Env -> Gamma -> VVal -> Q VType
inferV env g val
  = case val of
      Var x -> do t <- inferVar g x
                  case t of
                    V v -> return v
                    A _ -> Left ("variable " ++ show x ++ " at the boxed type " ++ ppr t)
      Glob x tys -> case M.lookup x (envSigs env) of
                      Just (SigVal tvs t) | length tvs == length tys -> return (inst tvs tys t)
                      _ -> Left ("unknown global value " ++ show x)
      UnitV -> return VUnit
      Lit l -> return (litType l)
      NoReuse n -> return (VReuse n)
      Inj i t v -> case t of
                     VSum ts | 0 <= i, i < length ts -> checkV env g v (ts !! i) >> return t
                     _ -> Left ("injection into " ++ ppr t)
      Pair v w -> VProd <$> inferV env g v <*> inferV env g w
      Ptr a v -> checkA env g v a >> return (VPtr a)
      Pack t tys v -> case t of
                        VExists bs b | length bs == length tys
                          -> checkV env g v (inst bs tys b) >> return t
                        _ -> Left ("pack into " ++ ppr t)
      DupV v -> do t <- inferV env g v
                   when (containsReuse (V t)) (Left "cannot duplicate a reuse credit")
                   return t
      TyApp v tys -> do tv <- inferV env g v
                        case tv of
                          VPtr (AForall tvs a) | length tvs == length tys -> return (VPtr (inst tvs tys a))
                          _ -> Left ("type application of " ++ ppr tv)
