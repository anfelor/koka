-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
-- Type inference and typing-context queries shared by typed IR consumers.
-- Keep inference in sync with the typing rules in Syntax.
module Backend.Typed.Query( Gamma, noJoins, yieldJoins, bindAll, checkE, inferE, inferA, inferV
                          , inferVar, inferAVar, altTypes, unboxRuGamma, copyRuGamma, lockGamma, uniqueGamma
                          , lamGamma
                          ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( zipWithM_, unless, when, forM_ )
import Common.Name
import Lib.PPrint( Pretty )
import Backend.Typed.Syntax
import Backend.Typed.Traversal( bindersE, boxTag, child, destructAOf, destructVOf, dsAlts, dsScrut, fvA, fvE, fvV, holes, isGlob, jumpArgs, within )
import Backend.Typed.Types
import Backend.Typed.Pretty( ppr )
import Backend.Typed.Env( Env(..), Q, funSig, unrollT, lazySides, openFields, boxContents, reuseSize, noHeapCredit )

type Gamma = M.Map Path Ty

-- J: the join points that can be jumped to (the variables they capture, including those of
-- the join points they jump to, their parameter types and their result type), and whether
-- the result may be the dummy value of an effect yield (`⊢ʸ`)
data Joins = Joins{ jsPoints :: M.Map Name (S.Set Path,[TVar],[VType],VType), jsYield :: Bool }

-- ∅, and ∅ where the result may be a dummy (`⊢ʸ`)
noJoins, yieldJoins :: Joins
noJoins = Joins M.empty False
yieldJoins = Joins M.empty True

bindAll :: [(Path,Ty)] -> Gamma -> Gamma
bindAll bs g = foldr (uncurry M.insert) g bs

expect :: (Types t, Pretty t) => t -> t -> Q ()
expect t1 t2 = unless (alphaEq t1 t2) (Left ("type mismatch:\n  expected: " ++ ppr t1 ++ "\n  actual  : " ++ ppr t2))

-- jumps are only allowed in tail position: the joins are not visible in a let-bound
-- expression, a lambda or a generalization
checkE :: Env -> Gamma -> Joins -> VExpr -> VType -> Q ()
checkE env g js e t = do mapM_ checkReuseTy (M.elems g)
                         checkReuseTy (V t)
                         case e of
                           Ret v -> checkV env g v t
                           _ -> inferE env g js e >>= expectV env t

inferE :: Env -> Gamma -> Joins -> VExpr -> Q VType
inferE env g js e = do mapM_ checkReuseTy (M.elems g)
                       inferExpr env g js e

-- Forgetting a description, its tag, or that a credit is full or a context nonempty is allowed;
-- inventing any is not. A cell can be used as a smaller one.
expectV :: Env -> VType -> VType -> Q ()
expectV _ expected actual
  = expect expected (forget expected actual)
  where
    forget (VReuse f _ p) (VReuse g n q) = VReuse (if f == MaybeEmpty then f else g) n (forgetDesc p q)
    forget (VCtx f _ _) (VCtx g a b) = VCtx (if f == MaybeEmpty then f else g) a b
    forget (VCell m _) (VCell n a) | m <= n = VCell m a
    forget (VProd fs) (VProd gs) | length fs == length gs = VProd (zipWith (\(f,t) (_,u) -> (f,forget t u)) fs gs)
    forget (VSum ts) (VSum us) | length ts == length us = VSum (zipWith (\(c,t) (_,u) -> (c,forget t u)) ts us)
    forget (VExists as a) (VExists bs b) | length as == length bs
      = VExists as (forget a (inst bs (map AVar as) b))
    forget _ t = t
    forgetDesc p q = case (p,q) of
                       (Just (Contents Nothing _ _), Just (Contents _ v s)) -> Just (Contents Nothing v s)
                       (Just _, _) -> q
                       (Nothing, _) -> Nothing

-- Forget only credits and contexts carried by a value, not contracts behind a pointer.
mapCredits :: (Fill -> Fill) -> (Maybe Contents -> Maybe Contents) -> VType -> VType
mapCredits f g t = case t of
  VReuse fl n p -> VReuse (f fl) n (g p)
  VCtx fl a b -> VCtx (f fl) a b
  VProd fs -> VProd [(l,mapCredits f g s) | (l,s) <- fs]
  VSum ts -> VSum [(c,mapCredits f g t) | (c,t) <- ts]
  VExists vs b -> VExists vs (mapCredits f g b)
  _ -> t

-- the descriptions of the credits carried by a value
descriptions :: VType -> [Contents]
descriptions t = case t of
  VReuse _ _ p -> maybe [] pure p
  VProd fs -> concatMap (descriptions . snd) fs
  VSum ts -> concatMap (descriptions . snd) ts
  VExists _ b -> descriptions b
  _ -> []

inferExpr :: Env -> Gamma -> Joins -> VExpr -> Q VType
inferExpr env g js expr
  | Just ds <- destructAOf expr
  = do t <- inferVar g (dsScrut ds)
       inferDestruct env g js expr t (dsAlts ds)
  | Just ds <- destructVOf expr
  = do t <- inferV env g (dsScrut ds)
       inferDestruct env g js expr (V t) (dsAlts ds)
inferExpr env g js expr
  = case expr of
      Ret v -> inferV env g v
      Let x t e1 e2 -> do checkE env g noJoins e1 t
                          inferE env (M.insert x (V t) g) js e2
      LetYield x t e1 e2 e3 -> do checkE env g yieldJoins e1 t
                                  branches env [inferE env (M.insert x (V t) g) js e2, inferE env g js e3]
      Yielded t | jsYield js -> return t
                | otherwise -> Left "the dummy value of a yield where the result is inspected"
      Unreachable t -> return t
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
                               branches env (inferE env g js def : [inferE env g js e | (_,e) <- alts])
      Drop x e -> do t <- inferVar g x
                     case t of
                       V (VCtx _ _ _) -> return ()
                       V _ -> Left ("drop of an unboxed value: " ++ ppr t)
                       A _ -> return ()
                     inferE env g js e
      Free r e -> do t <- inferV env g (Var r)
                     case t of
                       VReuse _ _ _ -> inferE env g js e
                       _ -> Left ("free of a non-credit: " ++ ppr t)
      Dup x e -> do inferVar g x >>= checkDupType
                    inferE env g js e
      IsUnique x e1 e2 -> do t <- inferVar g x
                             case t of
                               V (VCell _ _) -> return ()
                               _ -> () <$ (inferAVar g x >>= boxContents >>= reuseSize)
                             branches env [inferE env (uniqueGamma g x) js e1, inferE env g js e2]
      -- the credit is full in the first branch and empty in the second
      IfFull r e1 e2 -> do t <- inferV env g (Var r)
                           case t of
                             VReuse _ n p -> branches env [inferE env (M.insert r (V (VReuse Full n p)) g) js e1, inferE env (M.delete r g) js e2]
                             _ -> Left ("test of a non-credit: " ++ ppr t)
      UnboxRu v e -> do g' <- unboxRuGamma g v
                        inferE env g' js e
      CopyRu z r e -> do g' <- copyRuGamma g z r
                         inferE env g' js e
      Lock z e -> do g' <- lockGamma g z
                     inferE env g' js e
      Join NonRec j tvs ps e1 e2
                          -> do let xs = [x | (x,_,_) <- ps]
                                unless (S.disjoint (fvE e1 `S.difference` S.fromList xs) (S.fromList (bindersE e2)))
                                  (Left ("join point " ++ show j ++ " captures a variable that is bound again in its scope"))
                                joinDescriptions j ps
                                t <- inferE env (bindAll [(x,V p) | (x,_,p) <- ps] g) js e1
                                unbound tvs (ftv t ++ ftvCtx g e1)
                                let caps = S.unions (S.difference (fvE e1) (S.fromList xs) : [cs | (k,(cs,_,_,_)) <- M.toList (jsPoints js), not (null (jumpArgs k e1))])
                                t <$ checkE env g js{ jsPoints = M.insert j (caps,tvs,[p | (_,_,p) <- ps],t) (jsPoints js) } e2 t
      -- only itself is in scope in its body (its captures are borrowed, see `CheckLinear`)
      Join (Rec t) j tvs ps e1 e2
                          -> do let xs = [x | (x,_,_) <- ps]
                                    caps = S.filter (\y -> not (any (y `within`) xs)) (fvE e1)
                                unless (S.disjoint caps (S.fromList (bindersE e2)))
                                  (Left ("recursive join point " ++ show j ++ " captures a variable that is bound again in its scope"))
                                joinDescriptions j ps
                                unbound tvs (ftv t ++ ftvCtx g e1)
                                let self = M.insert j (caps,tvs,[p | (_,_,p) <- ps],t)
                                checkE env (bindAll [(x,V p) | (x,_,p) <- ps] g) js{ jsPoints = self M.empty } e1 t
                                t <$ checkE env g js{ jsPoints = self (jsPoints js) } e2 t
      -- the captured variables must still be in scope (`[unbox-ru]` and `[lock]` split a box into its parts)
      Jump j ts vs -> case M.lookup j (jsPoints js) of
                     Just (caps,tvs,ps,t) -> do forM_ (S.toList caps) $ \x ->
                                                  unless (M.member x g) (Left ("jump to " ++ show j ++ ", which captures " ++ show x ++ ", out of its scope"))
                                                unless (length ts == length tvs) (Left ("jump to " ++ show j ++ " with " ++ show (length ts) ++ " type arguments"))
                                                checkArgs env g (map (inst tvs ts) ps) vs
                                                return t
                     Nothing -> Left ("jump to " ++ show j ++ " outside of its scope or not in tail position")
      Gen tvs e -> do unbound tvs (ftvCtx g e)
                      t <- inferE env g noJoins e
                      case t of
                        VPtr a -> return (VPtr (AForall tvs a))
                        _ -> Left ("generalization of a non-pointer: " ++ ppr t)
      _ -> Left "unexpected destructuring form"

-- the descriptions in the parameters of a join point do not name its parameters
joinDescriptions :: Name -> [(Path,Mode,VType)] -> Q ()
joinDescriptions j ps
  = unless (S.disjoint (S.fromList [x | (x,_,_) <- ps]) (S.fromList [root n | (_,_,p) <- ps, Contents _ v _ <- descriptions p, Path n _ <- S.toList (fvV v)]))
      (Left ("a description in the parameters of join point " ++ show j ++ " names a parameter"))

-- The two scrutinee categories share branch checking and existential escape checks.
inferDestruct :: Env -> Gamma -> Joins -> VExpr -> Ty -> [([Path],VExpr)] -> Q VType
inferDestruct env g js expr t alts
  = do tss <- altTypes env t expr
       unless (length alts == length tss) (Left "wrong number of alternatives")
       r <- branches env [inferE env (bindAll (zip xs ts) g) js e | ((xs,e),ts) <- zip alts tss]
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
      (Proj _ _ i _ _, V (VProd fs)) | 0 <= i, i < length fs -> return [[V (snd (fs !! i))]]
      (CaseV _ _ alts, V (VSum ts)) -> do
        let indices = [i | (i,_,_) <- alts]
        unless (S.fromList indices == S.fromList [0 .. length ts - 1] && length indices == length ts)
          (Left "invalid value case indices")
        return [[V (snd (ts !! i))] | i <- indices]
      (SplitA _ _ k _ _, A a@(ASum ts)) -> do
        checkShape a
        let (ls,rs) = span ((< k) . fst) ts
        unless (not (null ls) && not (null rs)) (Left "invalid boxed sum partition")
        return [[A (ASum ls)], [A (ASum rs)]]
      (IfWhnf{}, A (ALazy l a)) -> return [[A a], [A l]]
      (CaseA _ _ alts def, A a@(ASum ts)) -> do
        checkShape a
        let indices = [i | (i,_,_) <- alts]
            rest = [(i,t) | (i,t) <- ts, i `notElem` indices]
        unless (all (`elem` map fst ts) indices && S.size (S.fromList indices) == length indices)
          (Left "invalid boxed case indices")
        unless (maybe (null rest) (const (not (null rest))) def)
          (Left "incomplete boxed case")
        return ([[A t] | i <- indices, Just t <- [lookup i ts]] ++ maybe [] (const [[A (ASum rest)]]) def)
      (Deref{}, V (VPtr a)) -> return [[A a]]
      (Unroll{}, A a) -> do b <- unrollT env a
                            return [[A b]]
      (Unbox{}, A (ABox s)) -> return [[V s]]
      (Unscalar{}, A (AScalar r)) -> return [[V (VRaw r)]]
      (Unpack _ _ tvs _ _, V (VExists bs s)) | length bs == length tvs -> return [[V (inst bs (map AVar tvs) s)]]
      (CaseOpen _ _ alts _, A a) -> do fss <- mapM (\(c,_,_) -> openFields env c a) alts
                                       return (map (map V) fss ++ [[]])
      _ -> Left ("cannot destructure a value of type " ++ ppr t)

-- the one-hole values `K` of `[ctx]`: the hole occurs once, in a field of a block that `K`
-- allocates, or `K` is the hole itself (the empty context)
isCtxValue :: VVal -> Bool
isCtxValue k
  = holes k == 1 && (k == Hole || path k)
  where
    path v = case v of
               Ptr _ a -> block a
               _ -> False
    block a = case a of
                Roll _ b -> block b
                InjA _ _ b -> block b
                InjLazy _ _ b -> block b
                Box v -> field v
                BoxAt _ v -> field v
                _ -> False
    field v = case v of
                Hole -> True
                Tuple ws -> any field [w | w <- ws, holes w == 1]
                _ -> path v

-- the context of the body of a lambda with parameters `ps`
lamGamma :: [(Path,Mode,VType)] -> Gamma -> Gamma
lamGamma ps g = bindAll [(x,V t) | (x,_,t) <- ps] (M.delete nameHole g)

-- The context of the body of `[unbox-ru]`: the contents `z.contents` of the box must have
-- been read, and the box `z` splits into them and the credit `z.credit` of its block, whose
-- tag follows from the path of the box.
unboxRuGamma :: Gamma -> Path -> Q Gamma
unboxRuGamma g z
  = do s <- inferAVar g z >>= boxContents
       n <- reuseSize s
       let x = child z SContents
       case M.lookup x g of
         Just (V s') | alphaEq s s' -> return ()
         _ -> Left ("taking the block of " ++ show z ++ " whose contents are not read")
       return (M.insert (child z SCredit) (V (VReuse Full n (Just (Contents (Just (boxTag z)) (Var x) s)))) (M.delete z g))

-- The context of the body of `[copy-ru]`: the binder is a credit with the description of the
-- block of `z`, a new root.
copyRuGamma :: Gamma -> Path -> Path -> Q Gamma
copyRuGamma g z r
  = do s <- inferAVar g z >>= boxContents
       n <- reuseSize s
       return (M.insert r (V (VReuse Full n (Just (Contents (Just (boxTag z)) (Var (child z SContents)) s)))) g)

-- The context of the body of `[lock]`: as for `[unbox-ru]`, the contents `z.contents` of the
-- box must have been read, and the box splits into them and the cell `z.credit` of its
-- block. The box is a thunk of a value `y` of a lazy type, also after `[split-a]`.
lockGamma :: Gamma -> Path -> Q Gamma
lockGamma g z
  = do s <- inferAVar g z >>= boxContents
       t <- case z of
              Path r ss | (SInjA _ _ : splits) <- reverse ss, (SDelay : SRoll : rest) <- dropWhile (`elem` [SLo,SHi]) splits
                -> inferAVar g (Path r (reverse rest))
              _ -> Left ("locking " ++ show z ++ ", which is not a thunk of a lazy value")
       n <- reuseSize s
       case M.lookup (child z SContents) g of
         Just (V s') | alphaEq s s' -> return ()
         _ -> Left ("locking " ++ show z ++ " whose contents are not read")
       return (M.insert (child z SCredit) (V (VCell n t)) (M.delete z g))

-- The context of the first branch of `[if-unique]`: a unique cell is a full credit.
uniqueGamma :: Gamma -> Path -> Gamma
uniqueGamma g x
  = case M.lookup x g of
      Just (V (VCell n _)) -> M.insert x (V (VReuse Full n Nothing)) g
      _ -> g

branches :: Env -> [Q VType] -> Q VType
branches env cs = do ts <- sequence cs
                     case ts of
                       []     -> Left "case without branches"
                       (t:rest)
                         | all (alphaEq t) rest -> return t
                         | all (alphaEq (weaken t) . weaken) rest -> return (weaken t)
                         | otherwise -> do mapM_ (expect (erase t) . erase) rest
                                           return (erase t)
  where
    -- disagreeing branches forget credits and contexts
    weaken = mapCredits (const MaybeEmpty) id
    erase = mapCredits (const MaybeEmpty) (const Nothing)

checkArgs :: Env -> Gamma -> [VType] -> [VVal] -> Q ()
checkArgs env g ps vs
  | length ps == length vs = zipWithM_ (\p v -> checkV env g v p) ps vs
  | otherwise = Left ("expecting " ++ show (length ps) ++ " arguments but got " ++ show (length vs))

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
checkV env g val t = do checkReuseTy (V t)
                        case (val,t) of
                          -- an empty credit satisfies every description
                          (NoReuse n _, VReuse MaybeEmpty m _) | n == m -> () <$ inferV env g val
                          _ -> inferV env g val >>= expectV env t

-- Descriptions are checked for layout, but never used as owned values. Their names need not be in
-- scope: the type of a description is part of it.
checkReuseTy :: Ty -> Q ()
checkReuseTy ty = case ty of
  V t -> case t of
    VReuse _ n p -> do when (n < 0) (Left "negative reuse size")
                       case p of
                         Nothing -> return ()
                         Just (Contents k v s) -> do when (maybe False (< 1) k) (Left "reuse contents with an invalid tag")
                                                     structural v
                                                     noHeapCredit s
                                                     m <- reuseSize s
                                                     unless (n == m) (Left "reuse contents do not match the block size")
    VPtr a -> checkReuseTy (A a)
    VProd fs -> do when (null fs) (Left "a product without fields")
                   mapM_ (inner . snd) fs
    VSum ts -> mapM_ (inner . snd) ts
    VExists _ b -> inner b
    VCtx _ a b -> checkReuseTy (A a) >> checkReuseTy (A b)
    VCell n a -> do when (n < 0) (Left "negative cell size")
                    checkReuseTy (A a)
    VUnit -> return ()
    VRaw _ -> return ()
  A a -> case a of
    ABox t -> inner t
    AScalar _ -> return ()
    ASum ts -> mapM_ (checkReuseTy . A . snd) ts
    AFun ps r -> mapM_ (checkReuseTy . V) (map snd ps ++ [r])
    AForall _ b -> checkReuseTy (A b)
    ALam _ b -> checkReuseTy (A b)
    ALazy l b -> do checkLazy a
                    checkReuseTy (A l) >> checkReuseTy (A b)
    AMu _ _ b ts -> mapM_ (checkReuseTy . A) (b : ts)
    ACon _ ts -> mapM_ (checkReuseTy . A) ts
    AApp _ ts -> mapM_ (checkReuseTy . A) ts
    AVar _ -> return ()
    AUnit -> return ()
  where
    -- a cell only occurs on its own
    inner t = case t of
      VCell _ _ -> Left ("a cell inside another type: " ++ ppr ty)
      _ -> checkReuseTy (V t)
    structural v = case v of
      Var _ -> return ()
      UnitV -> return ()
      Tuple vs -> mapM_ structural vs
      Inj _ _ x -> structural x
      Pack _ _ x -> structural x
      TyApp x _ -> structural x
      _ -> Left "reuse contents must be a structural value"

-- Look up a named operand; boxed eliminations and `drop` require A.
inferVar :: Gamma -> Path -> Q Ty
inferVar g x = maybe (Left ("unbound variable " ++ show x)) return (M.lookup x g)

inferAVar :: Gamma -> Path -> Q AType
inferAVar g x
  = do t <- inferVar g x
       case t of
         A a -> return a
         V _ -> Left ("boxed operand " ++ show x ++ " at the unboxed type " ++ ppr t)

checkShape :: AType -> Q ()
checkShape a = unless (isShape a) (Left ("sum alternatives must be shapes: " ++ ppr a))

-- A lazy sum `L ~> S` consists of two sums, of thunks and of strict alternatives, whose tags
-- are separated by the smallest tag of L.
checkLazy :: AType -> Q ()
checkLazy a
  = case a of
      ALazy l@(ASum ls) s@(ASum ss)
        -> do checkShape l
              checkShape s
              unless (all (isBox . snd) ls) (Left ("the thunks of a lazy sum must be boxes: " ++ ppr a))
              unless (maximum (map fst ss) < minimum (map fst ls)) (Left ("the strict tags of a lazy sum must come before its thunks: " ++ ppr a))
      _ -> Left ("ill-formed lazy sum: " ++ ppr a)
  where
    isBox t = case t of
                ABox _ -> True
                _ -> False

inferA :: Env -> Gamma -> AVal -> Q AType
inferA env g val
  = case val of
      Fun f -> case M.lookup f (envSigs env) of
                 Just (SigFun tvs ps r) -> return (forallA tvs (AFun ps r))
                 _ -> Left ("unknown function " ++ show f)
      UnitA -> return AUnit
      InjA i a v -> case a of
                      ASum ts | Just t <- lookup i ts -> checkShape a >> checkA env g v t >> return a
                      _ -> Left ("invalid boxed injection into " ++ ppr a)
      Roll a v -> do b <- unrollT env a
                     checkA env g v b
                     return a
      InjLazy d a v -> case a of
                         ALazy l s -> do checkLazy a
                                         checkA env g v (case d of Whnf -> s; Delay -> l)
                                         return a
                         _ -> Left ("invalid injection into the lazy sum " ++ ppr a)
      Box v -> do t <- inferV env g v
                  noHeapCredit t
                  return (ABox t)
      Scalar v -> do t <- inferV env g v
                     case t of
                       VRaw r -> return (AScalar r)
                       _ -> Left ("not a raw value: " ++ ppr t)
      OpenCon c tys vs
        -> case M.lookup c (envSigs env) of
             Just (SigCon tvs fs n) | length tvs == length tys && length fs == length vs
               -> do forM_ (zip vs fs) $ \(v,f) ->
                       do noHeapCredit (inst tvs tys f)
                          checkV env g v (inst tvs tys f)
                     return (ACon n tys)
             _ -> Left ("unknown open constructor " ++ show c)
      Lam ps r e -> do when (any containsLinear [t | x <- S.toList (fvA val), Just t <- [M.lookup x g]])
                         (Left "cannot capture reuse credits or cells in a closure")
                       checkE env (lamGamma ps g) yieldJoins e r
                       return (AFun [(m,t) | (_,m,t) <- ps] r)
      BoxAt r v -> do tr <- inferV env g (Var r)
                      checkReuseTy (V tr)
                      tv <- inferV env g v
                      noHeapCredit tv
                      case tr of
                        VReuse _ n _
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
      NoReuse n p -> do let t = VReuse MaybeEmpty n p
                        checkReuseTy (V t)
                        return t
      Inj i t v -> case t of
                     VSum ts | 0 <= i, i < length ts -> checkV env g v (snd (ts !! i)) >> return t
                     _ -> Left ("injection into " ++ ppr t)
      Tuple [] -> Left "a tuple without fields"
      Tuple vs -> VProd . zip (map posField [0..]) <$> mapM (inferV env g) vs
      Ptr a v -> checkA env g v a >> return (VPtr a)
      Pack t tys v -> case t of
                        VExists bs b | length bs == length tys
                          -> checkV env g v (inst bs tys b) >> return t
                        _ -> Left ("pack into " ++ ppr t)
      Hole -> case M.lookup nameHole g of
                Just (V t) -> return t
                _ -> Left "hole outside of a context"
      Context b k -> do unless (isCtxValue k) (Left ("ill-formed context: " ++ ppr val))
                        t <- inferV env (M.insert nameHole (V (VPtr b)) g) k
                        case t of
                          VPtr a -> return (VCtx (if k == Hole then MaybeEmpty else Full) a b)
                          _ -> Left ("context of a non-pointer: " ++ ppr t)
      Plug c v -> do t <- inferV env g c
                     case t of
                       VCtx _ a b -> checkV env g v (VPtr b) >> return (VPtr a)
                       _ -> Left ("plugging a non-context: " ++ ppr t)
      Append c d -> do tc <- inferV env g c
                       td <- inferV env g d
                       case (tc,td) of
                         (VCtx f a b, VCtx f' b' c') | alphaEq b b' -> return (VCtx (if f == Full then f else f') a c')
                         _ -> Left ("appending " ++ ppr td ++ " to " ++ ppr tc)
      CtxCopy c -> do t <- inferV env g c
                      case t of
                        VCtx _ _ _ -> return t
                        _ -> Left ("unsharing a non-context: " ++ ppr t)
      Memoize c d k v -> do tc <- inferV env g c
                            case tc of
                              VCell n a -> do (l,ss) <- lazySides env a
                                              s <- case lookup k (case d of Whnf -> ss; Delay -> l) of
                                                     Just (ABox s) -> return s
                                                     _ -> Left ("memoizing alternative " ++ show k ++ " of " ++ ppr (A a) ++ ", which is not a box on its side")
                                              checkV env g v s
                                              noHeapCredit s
                                              m <- reuseSize s
                                              unless (m <= n) (Left ("memoizing " ++ show m ++ " bytes in a cell of " ++ show n ++ " bytes"))
                                              return (VPtr a)
                              _ -> Left ("memoizing into a non-cell: " ++ ppr tc)
      DupV v -> do unless (isGlob v) (Left ("dup of a value that is not a global: " ++ ppr val))
                   inferV env g v
      TyApp v tys -> do tv <- inferV env g v
                        case tv of
                          VPtr (AForall tvs a) | length tvs == length tys -> return (VPtr (inst tvs tys a))
                          _ -> Left ("type application of " ++ ppr tv)
