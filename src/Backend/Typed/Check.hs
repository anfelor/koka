-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{- Type checker: the types of the typing rules in `Syntax` (the modes are checked by `Linear`).
  Keep it in sync with the rules: a change here must be reflected there, and vice versa.
-}
module Backend.Typed.Check( checkProgram, Env(..), Gamma, envOf, bindAll, inferV, altTypes, boxContents, reuseSize, unfoldT, openFields
                          , funSig, paramModes, isTrivial ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( zipWithM_, unless )
import Common.Name
import Common.NamePrim( nameTpFieldAddr, nameTpReuse )
import Backend.Typed.Syntax
import Backend.Typed.Types
import Backend.Typed.Pretty( ppr )
import Backend.Typed.Layout( layout, blockSize, isBlock )

type Gamma = M.Map Name Ty

-- the join points that can be jumped to: their parameter types and result type
type Joins = M.Map Name ([VType],Ty)

data Env = Env{ envTypes :: TypeDefs, envSigs :: Sigs }

type C a = Either String a

envOf :: Program -> Env
envOf prog = Env (progTypes prog) (progSigs prog)

bindAll :: [(Name,Ty)] -> Gamma -> Gamma
bindAll bs g = foldr (uncurry M.insert) g bs

checkProgram :: Program -> [String]
checkProgram prog
  = [show (defName d) ++ ": " ++ err | d <- progDefs prog, Left err <- [checkDef (envOf prog) d]]

checkDef :: Env -> Def -> C ()
checkDef env def
  = case def of
      DefFun _ _ args res body -> checkE env (M.fromList [(x,V t) | (x,_,t) <- args]) M.empty body (V res)
      DefVal _ _ t body        -> checkE env M.empty M.empty body (V t)

expect :: Ty -> Ty -> C ()
expect t1 t2 = unless (alphaEq t1 t2) (Left ("type mismatch:\n  expected: " ++ ppr t1 ++ "\n  actual  : " ++ ppr t2))

-- jumps are only allowed in tail position: the joins are not visible in a let-bound
-- expression, a lambda or a generalization
checkE :: Env -> Gamma -> Joins -> Expr -> Ty -> C ()
checkE env g js e t = inferE env g js e >>= expect t

inferE :: Env -> Gamma -> Joins -> Expr -> C Ty
inferE env g js expr
  | Just ds <- destructOf expr
  = do t   <- inferV env g (dsScrut ds)
       tss <- altTypes env t expr
       r   <- branches [inferE env (bindAll (zip xs ts) g) js e | ((xs,e),ts) <- zip (dsAlts ds) tss]
       case expr of
         Unpack _ _ tvs x e -> unbound tvs (ftv r ++ ftvCtx (M.delete x g) e)
         _ -> return ()
       return r
inferE env g js expr
  = case expr of
      Ret v -> inferV env g v
      Let x t e1 e2 -> do checkE env g M.empty e1 t
                          inferE env (M.insert x t g) js e2
      Call f tys vs -> do ptrArgs tys
                          (ps,r) <- funSig env f tys
                          checkArgs env g ps vs
                          return (V r)
      App f vs -> do ft <- inferV env g f
                     case ft of
                       A (AFun ps r) -> do checkArgs env g (map snd ps) vs
                                           return (V r)
                       _ -> Left ("applying a non-function: " ++ ppr ft)
      CaseLit v alts def -> do vt <- inferV env g v
                               mapM_ (\(l,_) -> expect vt (V (litType l))) alts
                               branches (inferE env g js def : [inferE env g js e | (_,e) <- alts])
      Drop x e -> inferV env g (Var x) >> inferE env g js e
      DropRu x r e -> do n <- inferV env g (Var x) >>= boxContents >>= reuseSize
                         inferE env (M.insert r (V (VReuse n)) g) js e
      IsUnique x e1 e2 -> do _ <- inferV env g (Var x) >>= boxContents >>= reuseSize
                             branches [inferE env g js e1, inferE env g js e2]
      UnboxRu v x r e -> do s <- inferV env g v >>= boxContents
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
                        V (VPtr a) -> return (V (VPtr (AForall tvs a)))
                        _ -> Left ("generalization of a non-pointer computation: " ++ ppr t)
      _ -> Left "unexpected destructuring form"

-- type arguments are pointer-sized
ptrArgs :: [VType] -> C ()
ptrArgs tys
  = case filter (not . isPtr) tys of
      []    -> return ()
      (t:_) -> Left ("type argument is not pointer-sized: " ++ ppr t)

-- type variables bound by `gen` and `unpack` must not occur free in the context (or the result)
unbound :: [TVar] -> [TVar] -> C ()
unbound tvs free
  = case filter (`elem` free) tvs of
      []    -> return ()
      (v:_) -> Left ("bound type variable escapes: " ++ ppr (VVar v))

-- the free type variables of the types of the free variables of an expression
ftvCtx :: Gamma -> Expr -> [TVar]
ftvCtx g e = concat [ftv t | x <- S.toList (fvE e), Just t <- [M.lookup x g]]

-- the types of the binders of each alternative of a destructuring form, given the type of its scrutinee
altTypes :: Env -> Ty -> Expr -> C [[Ty]]
altTypes env t expr
  = case (expr,t) of
      (Unpair{}, V (VProd a b)) -> return [[V a, V b]]
      (CaseV _ _ alts, V (VSum ts)) | length ts == length alts -> return [[V s] | s <- ts]
      (CaseA{}, A (ASum a b)) -> return [[A a],[A b]]
      (Unfold{}, V v) -> do a <- unfoldT env v
                            return [[A a]]
      (Unbox{}, A (ABox s)) -> return [[V s]]
      (UnboxLazy{}, A (ABox s)) -> return [[V s]]
      (Unpack _ _ tvs _ _, V (VExists bs s)) | length bs == length tvs -> return [[V (inst bs (map VVar tvs) s)]]
      (CaseOpen _ _ alts _, V v) -> do fs <- mapM (\(c,_,_) -> openFields env c v) alts
                                       return ([[V f] | f <- fs] ++ [[]])
      _ -> Left ("cannot destructure a value of type " ++ ppr t)

branches :: [C Ty] -> C Ty
branches cs = do ts <- sequence cs
                 case ts of
                   []     -> Left "case without branches"
                   (t:rest) -> mapM_ (expect t) rest >> return t

funSig :: Env -> Name -> [VType] -> C ([VType],VType)
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

checkArgs :: Env -> Gamma -> [VType] -> [Val] -> C ()
checkArgs env g ps vs
  | length ps == length vs = zipWithM_ (\p v -> checkV env g v (V p)) ps vs
  | otherwise = Left ("expecting " ++ show (length ps) ++ " arguments but got " ++ show (length vs))

unfoldT :: Env -> VType -> C AType
unfoldT env t
  = case t of
      VPtr a -> return a
      VCon n args -> case M.lookup n (envTypes env) of
                           Just (TypeDef _ tvs (Just body) _) -> return (inst tvs args body)
                           Just _  -> Left ("cannot unfold abstract type " ++ show n)
                           Nothing -> Left ("unknown type " ++ show n)
      _ -> Left ("unfold of " ++ ppr t)

openFields :: Env -> Name -> VType -> C VType
openFields env c t
  = case M.lookup c (envSigs env) of
      Just (SigCon tvs f r) -> case match tvs r t of
                                         Just sub -> return (subst sub f)
                                         Nothing  -> Left ("open constructor " ++ show c ++ " does not match " ++ ppr t)
      _ -> Left ("unknown open constructor " ++ show c)

-- the contents `V` of a box `Box V`
boxContents :: Ty -> C VType
boxContents t
  = case t of
      A (ABox v) -> return v
      _ -> Left ("not a box: " ++ ppr t)

-- the size `|V|` of the block of a box `Box V` that is always allocated on the heap
reuseSize :: VType -> C Int
reuseSize v
  | isBlock (layout v) = return (blockSize (layout v))
  | otherwise          = Left ("no reusable block: " ++ ppr (A (ABox v)))

-- values of these types need no reference counting
isTrivial :: Ty -> Bool
isTrivial t
  = case t of
      V v -> trivialV v
      A a -> trivialA a
  where
    trivialV v = case v of
                   VRaw _       -> True
                   VUnit        -> True
                   VProd x y    -> trivialV x && trivialV y
                   VSum ts      -> all trivialV ts
                   VExists _ b  -> trivialV b
                   VCon n _     -> n `elem` [nameTpFieldAddr, nameTpReuse]
                   VVar _       -> False
                   VApp _ _     -> False
                   VPtr _       -> False
                   VTLam _ _    -> False
                   VReuse _     -> False
    trivialA a = case a of
                   AUnit     -> True
                   ASum x y  -> trivialA x && trivialA y
                   ABox _    -> False
                   AFun _ _  -> False
                   AForall _ _ -> False

litType :: Lit -> VType
litType lit
  = case lit of
      LitInt _    -> vtInt
      LitString _ -> vtString
      LitChar _   -> vtChar
      LitFloat _  -> vtFloat

checkV :: Env -> Gamma -> Val -> Ty -> C ()
checkV env g val t
  = case (val,t) of
      (Unit, A AUnit) -> return ()
      (Unit, V VUnit) -> return ()
      _ -> inferV env g val >>= expect t

inferV :: Env -> Gamma -> Val -> C Ty
inferV env g val
  = case val of
      Var x -> maybe (Left ("unbound variable " ++ show x)) return (M.lookup x g)
      Fun f -> case M.lookup f (envSigs env) of
                 Just (SigFun tvs ps r) -> return (A (forallA tvs (AFun ps r)))
                 _ -> Left ("unknown function " ++ show f)
      Glob x tys -> case M.lookup x (envSigs env) of
                      Just (SigVal tvs t) | length tvs == length tys -> ptrArgs tys >> return (V (inst tvs tys t))
                      _ -> Left ("unknown global value " ++ show x)
      Unit -> return (V VUnit)
      Lit l -> return (V (litType l))
      NoReuse n -> return (V (VReuse n))
      Inj i t v -> case t of
                     VSum ts | i < length ts -> checkV env g v (V (ts !! i)) >> return (V t)
                     _ -> Left ("injection into " ++ ppr t)
      Inl a v -> case a of
                   ASum l _ -> checkV env g v (A l) >> return (A a)
                   _ -> Left ("inl into " ++ ppr a)
      Inr a v -> case a of
                   ASum _ r -> checkV env g v (A r) >> return (A a)
                   _ -> Left ("inr into " ++ ppr a)
      Pair v w -> do tv <- inferV env g v
                     tw <- inferV env g w
                     case (tv,tw) of
                       (V a, V b) -> return (V (VProd a b))
                       _ -> Left ("pair of boxed values: " ++ ppr tv ++ ", " ++ ppr tw)
      Fold t v -> do a <- unfoldT env t
                     checkV env g v (A a)
                     return (V t)
      Box v -> do tv <- inferV env g v
                  case tv of
                    V t -> return (A (ABox t))
                    _   -> Left ("boxing a boxed value: " ++ ppr tv)
      Pack t tys v -> case t of
                        VExists bs b | length bs == length tys
                          -> ptrArgs tys >> checkV env g v (V (inst bs tys b)) >> return (V t)
                        _ -> Left ("pack into " ++ ppr t)
      OpenCon c tys v -> case M.lookup c (envSigs env) of
                           Just (SigCon tvs f r) | length tvs == length tys
                             -> ptrArgs tys >> checkV env g v (V (inst tvs tys f)) >> return (V (inst tvs tys r))
                           _ -> Left ("unknown open constructor " ++ show c)
      Lam ps r e -> do checkE env (bindAll [(x,V t) | (x,_,t) <- ps] g) M.empty e (V r)
                       return (A (AFun [(m,t) | (_,m,t) <- ps] r))
      Dup v -> inferV env g v
      BoxIn x v -> do tx <- inferV env g (Var x)
                      tv <- inferV env g v
                      case (tx,tv) of
                        (V (VCon n args), V s)
                          | Just (TypeDef _ tvs (Just body) (Just linfo)) <- M.lookup n (envTypes env)
                          , any (alphaEq (ABox s)) (splitSum (length (lazyCons linfo)) (inst tvs args body))
                          -> return (A (ABox s))
                        _ -> Left ("writing " ++ ppr tv ++ " into " ++ ppr tx)
      BoxAt r v -> do tr <- inferV env g (Var r)
                      tv <- inferV env g v
                      case (tr,tv) of
                        (V (VReuse n), V t) -> do m <- reuseSize t
                                                  unless (n == m) (Left ("reuse of a block of " ++ show n ++ " bytes for " ++ show m ++ " bytes"))
                                                  return (A (ABox t))
                        _ -> Left ("allocation at " ++ ppr tr ++ " of " ++ ppr tv)
      TyApp v tys -> do tv <- inferV env g v
                        case tv of
                          A (AForall tvs a) | length tvs == length tys -> ptrArgs tys >> return (A (inst tvs tys a))
                          _ -> Left ("type application of " ++ ppr tv)
