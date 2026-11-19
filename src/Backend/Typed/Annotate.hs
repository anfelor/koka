-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Annotating values and expressions with their types, by bidirectional typing.

  The printer omits the type annotations of injections, rolls, pointers, packs, contexts,
  `yielded` and `unreachable`, as they follow from where they occur. This pass fills them in
  from the signatures and datatypes of the program: an expression is checked against its type,
  a value against the type that its position expects, and the type of a value is synthesized
  where nothing is expected (the scrutinee of a destructuring, the operand of `cast-ev`).

  The pass does not check the program (`CheckTypes` does). An annotation that does not follow
  is left as it is, with a message: for example, without the definition of an imported datatype
  its body is unknown, and so are the types of the binders of an `[unroll]` of its values.
-}
module Backend.Typed.Annotate( annotateProgram ) where

import qualified Data.Map as M
import Control.Monad( zipWithM )
import Control.Monad.Writer( Writer, runWriter, tell )
import Data.Functor.Const( Const(..) )
import Data.Monoid( Any(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Types( inst, forallA, atAny, vtInt, vtString, vtChar, vtFloat, traverseReuseContents )
import Backend.Typed.Traversal( Destruct(..), descendV, destructAOf, destructVOf )
import Backend.Typed.Env( Env(..), envOf, funSig, dataBody, lazySides )
import Backend.Typed.Query( Gamma, bindAll, altTypes, lamGamma, unboxRuGamma, copyRuGamma, lockGamma, uniqueGamma )
import Backend.Typed.Pretty( ppr )

-- the environment, the types of the variables, and the type parameters and parameter types of
-- the join points
data Ctx = Ctx{ ctxEnv :: Env, ctxGamma :: Gamma, ctxJoins :: M.Map Name ([TVar],[VType]) }

-- an annotation, with a message for each annotation that does not follow
type An = Writer [String]

-- the annotated program, and the messages of each definition
annotateProgram :: Program -> (Program,[(Name,[String])])
annotateProgram prog
  = (prog{ progDefs = map fst results }, [(defName d, msgs) | (d,msgs) <- results, not (null msgs)])
  where
    results = map (runWriter . annDef (envOf prog)) (progDefs prog)

annDef :: Env -> Def -> An Def
annDef env def
  = case def of
      DefFun f tvs ps q r e -> do ps' <- annParams c0 ps
                                  DefFun f tvs ps' q r <$> annE (bindVars [(x,V t) | (x,_,t) <- ps'] c0) e r
      DefVal x tvs t e -> DefVal x tvs t <$> annE c0 e t
  where
    c0 = Ctx env M.empty M.empty

bindVars :: [(Path,Ty)] -> Ctx -> Ctx
bindVars bs c = c{ ctxGamma = bindAll bs (ctxGamma c) }

unknown :: String -> a -> An a
unknown msg x = tell [msg] >> return x

annParams :: Ctx -> [(Path,Mode,VType)] -> An [(Path,Mode,VType)]
annParams c = mapM (\(x,m,t) -> (,,) x m <$> annTy c t)

-- the values in the descriptions of the credits in a type
annTy :: Ctx -> VType -> An VType
annTy c = traverseReuseContents (traverse (annContents c))

annContents :: Ctx -> Contents -> An Contents
annContents c (Contents k v t) = do v' <- checkV c v t
                                    return (Contents k v' t)

--------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------

-- an expression checked against its type
annE :: Ctx -> VExpr -> VType -> An VExpr
annE c expr w
  | Just ds <- destructAOf expr
  = dsBuild ds (dsScrut ds) <$> annAlts c expr (M.lookup (dsScrut ds) gamma) (dsAlts ds) w
  | Just ds <- destructVOf expr
  = case synthV c (dsScrut ds) of
      Just (t,mv) -> dsBuild ds <$> mv <*> annAlts c expr (Just (V t)) (dsAlts ds) w
      Nothing -> dsBuild ds (dsScrut ds) <$> annAlts c expr Nothing (dsAlts ds) w
  | otherwise
  = case expr of
      Ret v -> Ret <$> checkV c v w
      Let x t e1 e2 -> do t' <- annTy c t
                          e1' <- annE c e1 t'
                          Let x t' e1' <$> annE (bindVars [(x,V t')] c) e2 w
      LetYield x t e1 e2 e3 -> do t' <- annTy c t
                                  e1' <- annE c e1 (VYield t')
                                  e2' <- annE (bindVars [(x,V t')] c) e2 w
                                  LetYield x t' e1' e2' <$> annE c e3 w
      Yielded _ -> case w of
                     VYield t -> return (Yielded t)
                     _ -> unknown ("yielded at " ++ ppr w) expr
      Unreachable _ -> return (Unreachable w)
      CastEv t v -> do t' <- annTy c t
                       CastEv t' <$> maybe (checkV c v t') snd (synthV c v)
      Call f ts vs -> case funSig env f ts of
                        Right (ps,_) | length ps == length vs -> Call f ts <$> zipWithM (checkV c) vs ps
                        _ -> unknown ("unknown function " ++ show f) () >> (Call f ts <$> mapM (synthOrKeep c) vs)
      App f vs -> case M.lookup f gamma of
                    Just (A (AFun ps _)) | length ps == length vs -> App f <$> zipWithM (checkV c) vs (map snd ps)
                    _ -> unknown ("application of " ++ show f ++ " of an unknown type") () >> (App f <$> mapM (synthOrKeep c) vs)
      Jump j ts vs -> case M.lookup j (ctxJoins c) of
                        Just (tvs,ps) | length tvs == length ts && length ps == length vs
                          -> Jump j ts <$> zipWithM (checkV c) vs (map (inst tvs ts) ps)
                        _ -> unknown ("jump to an unknown join point " ++ show j) () >> (Jump j ts <$> mapM (synthOrKeep c) vs)
      CaseLit v alts def -> CaseLit <$> synthOrKeep c v <*> mapM (\(l,e) -> (,) l <$> annE c e w) alts <*> annE c def w
      Gen tvs e -> case w of
                     VPtr (AForall bs a) | length bs == length tvs -> Gen tvs <$> annE c e (VPtr (inst bs (map AVar tvs) a))
                     _ -> unknown ("generalization at " ++ ppr w) expr
      Drop x e -> Drop x <$> annE c e w
      Free r e -> Free r <$> annE c e w
      Dup x e -> Dup x <$> annE c e w
      IsUnique x e1 e2 -> IsUnique x <$> annE c{ ctxGamma = uniqueGamma gamma x } e1 w <*> annE c e2 w
      IfFull r e1 e2 -> let full = case M.lookup r gamma of
                                     Just (V (VReuse _ n p)) -> bindVars [(r,V (VReuse Full n p))] c
                                     _ -> c
                        in IfFull r <$> annE full e1 w <*> annE c e2 w
      UnboxRu z e -> UnboxRu z <$> within (unboxRuGamma gamma z) e
      CopyRu z r e -> CopyRu z r <$> within (copyRuGamma gamma z r) e
      Lock z e -> Lock z <$> within (lockGamma gamma z) e
      Join rec j tvs ps e1 e2 -> do ps' <- annParams c ps
                                    rec' <- case rec of
                                              NonRec -> return NonRec
                                              Rec t -> Rec <$> annTy c t
                                    let c' = c{ ctxJoins = M.insert j (tvs,[t | (_,_,t) <- ps']) (ctxJoins c) }
                                        body = bindVars [(x,V t) | (x,_,t) <- ps']
                                    e1' <- case rec' of
                                             NonRec -> annE (body c) e1 w
                                             Rec t -> annE (body c') e1 t
                                    Join rec' j tvs ps' e1' <$> annE c' e2 w
      Plug k v -> case synthV c k of
                    Just (VCtx _ _ b, mk) -> Plug <$> mk <*> checkV c v (VPtr b)
                    _ -> unknown ("plugging " ++ ppr k ++ " of an unknown type") () >> (Plug k <$> synthOrKeep c v)
      Append k d -> case (synthV c k, synthV c d, w) of
                      (Just (VCtx _ _ b, mk), _, VCtx f _ t) -> Append <$> mk <*> checkV c d (VCtx f b t)
                      (_, Just (VCtx f b _, md), VCtx _ a _) -> Append <$> checkV c k (VCtx f a b) <*> md
                      _ -> unknown ("appending contexts of unknown types at " ++ ppr w) expr
      CtxCopy k -> CtxCopy <$> maybe (checkV c k w) snd (synthV c k)
      Memoize k d i v -> case synthV c k of
                           Just (VCell _ a, mk) | Right (l,s) <- lazySides env a, Just (ABox t) <- lookup i (case d of { Whnf -> s; Delay -> l })
                             -> Memoize <$> mk <*> pure d <*> pure i <*> checkV c v t
                           _ -> unknown ("memoizing into " ++ ppr k ++ " of an unknown type") expr
      -- destructurings, handled above
      _ -> return expr
  where
    env = ctxEnv c
    gamma = ctxGamma c
    within q e = case q of
                   Right g -> annE c{ ctxGamma = g } e w
                   Left err -> unknown err () >> annE c e w

-- the alternatives of a destructuring form, given the type of its scrutinee
annAlts :: Ctx -> VExpr -> Maybe Ty -> [([Path],VExpr)] -> VType -> An [VExpr]
annAlts c expr mt alts w
  = do tss <- case mt of
                Just t | Right tss <- altTypes (ctxEnv c) t expr, length tss == length alts -> return (map Just tss)
                       | Left err <- altTypes (ctxEnv c) t expr -> unknown err (map (const Nothing) alts)
                _ -> unknown ("a destructuring of a value of an unknown type: " ++ ppr expr) (map (const Nothing) alts)
       sequence [annE (maybe c (\ts -> bindVars (zip xs ts) c) mts) e w | ((xs,e),mts) <- zip alts tss]

--------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------

-- a value checked against the type that its position expects
checkV :: Ctx -> VVal -> VType -> An VVal
checkV c val t
  = case (val,t) of
      (Inj i _ v, VSum ts) | 0 <= i, i < length ts -> Inj i t <$> checkV c v (snd (ts !! i))
      (Tuple vs, VProd fs) | length vs == length fs -> Tuple <$> zipWithM (checkV c) vs (map snd fs)
      (Ptr _ a, VPtr b) -> Ptr b <$> checkA c a b
      (Pack _ ts v, VExists bs b) | length ts == length bs -> Pack t ts <$> checkV c v (inst bs ts b)
      (Context _ k, VCtx _ a b) -> Context b <$> checkV (bindVars [(nameHole,V (VPtr b))] c) k (VPtr a)
      (Pure v, VYield s) -> Pure <$> checkV c v s
      (DupV v, _) -> DupV <$> checkV c v t
      (Down b v, _) -> Down b <$> checkV c v (VPtr atAny)
      (NoReuse n p, _) -> NoReuse n <$> traverse (annContents c) p
      _ | not (annotated val) -> return val
        | Just (_,mv) <- synthV c val -> mv
        | otherwise -> unknown ("cannot annotate " ++ ppr val ++ " at " ++ ppr t) val

-- the type of a value where nothing is expected, if it follows from the value, and the value
-- annotated
synthV :: Ctx -> VVal -> Maybe (VType, An VVal)
synthV c val
  = case val of
      Var x -> case M.lookup x (ctxGamma c) of
                 Just (V t) -> done t
                 _ -> Nothing
      Glob x ts -> case M.lookup x (envSigs (ctxEnv c)) of
                     Just (SigVal tvs t) | length tvs == length ts -> done (inst tvs ts t)
                     _ -> Nothing
      UnitV -> done VUnit
      Lit l -> done (litType l)
      Hole -> case M.lookup nameHole (ctxGamma c) of
                Just (V t) -> done t
                _ -> Nothing
      NoReuse n p -> Just (VReuse MaybeEmpty n p, NoReuse n <$> traverse (annContents c) p)
      Tuple vs -> do rs <- mapM (synthV c) vs
                     Just (VProd (zip (map posField [0..]) (map fst rs)), Tuple <$> mapM snd rs)
      Ptr _ a -> do (t,ma) <- synthA c a
                    Just (VPtr t, Ptr t <$> ma)
      TyApp v ts -> do (t,mv) <- synthV c v
                       case t of
                         VPtr (AForall bs a) | length bs == length ts -> Just (VPtr (inst bs ts a), (`TyApp` ts) <$> mv)
                         _ -> Nothing
      DupV v -> do (t,mv) <- synthV c v
                   Just (t, DupV <$> mv)
      Pure v -> do (t,mv) <- synthV c v
                   Just (VYield t, Pure <$> mv)
      Up v -> Just (VPtr atAny, Up <$> synthOrKeep c v)
      Down b v -> Just (VPtr b, Down b <$> checkV c v (VPtr atAny))
      Inj{} -> Nothing
      Pack{} -> Nothing
      Context{} -> Nothing
  where
    done t = Just (t, return val)

-- a value whose type is not known: annotated if its type follows from it
synthOrKeep :: Ctx -> VVal -> An VVal
synthOrKeep c v
  = case synthV c v of
      Just (_,mv) -> mv
      Nothing | annotated v -> unknown ("cannot annotate " ++ ppr v) v
              | otherwise -> return v

-- whether a value has type annotations
annotated :: VVal -> Bool
annotated val
  = case val of
      Inj{} -> True
      Ptr{} -> True
      Pack{} -> True
      Context{} -> True
      _ -> getAny (getConst (descendV (const (Const (Any True))) (Const . Any . annotated) val))

litType :: Lit -> VType
litType lit
  = case lit of
      LitInt _    -> vtInt
      LitString _ -> vtString
      LitChar _   -> vtChar
      LitFloat _  -> vtFloat

checkA :: Ctx -> AVal -> AType -> An AVal
checkA c val t
  = case (val,t) of
      (InjA i _ v, ASum ts) | Just s <- lookup i ts -> InjA i t <$> checkA c v s
      (Roll _ v, _) -> case dataBody (ctxEnv c) t of
                         Right b -> Roll t <$> checkA c v b
                         Left err -> unknown err (Roll t v)
      (InjLazy d _ v, ALazy l s) -> InjLazy d t <$> checkA c v (case d of { Whnf -> s; Delay -> l })
      (Box v, ABox s) -> Box <$> checkV c v s
      (BoxAt r v, ABox s) -> BoxAt r <$> checkV c v s
      (Scalar v, AScalar r) -> Scalar <$> checkV c v (VRaw r)
      (Fun _, _) -> return val
      (UnitA, _) -> return val
      _ | Just (_,ma) <- synthA c val -> ma
      (OpenCon k ts vs, _) -> unknown ("unknown open constructor " ++ show k) () >> (OpenCon k ts <$> mapM (synthOrKeep c) vs)
      _ -> unknown ("cannot annotate " ++ ppr val ++ " at " ++ ppr t) val

synthA :: Ctx -> AVal -> Maybe (AType, An AVal)
synthA c val
  = case val of
      Fun f -> case M.lookup f (envSigs (ctxEnv c)) of
                 Just (SigFun tvs ps _ r) -> done (forallA tvs (AFun ps r))
                 _ -> Nothing
      UnitA -> done AUnit
      Box v -> do (t,mv) <- synthV c v
                  Just (ABox t, Box <$> mv)
      BoxAt r v -> do (t,mv) <- synthV c v
                      Just (ABox t, BoxAt r <$> mv)
      Scalar v -> do (t,mv) <- synthV c v
                     case t of
                       VRaw r -> Just (AScalar r, Scalar <$> mv)
                       _ -> Nothing
      OpenCon k ts vs -> case M.lookup k (envSigs (ctxEnv c)) of
                           Just (SigCon tvs fs n) | length tvs == length ts && length fs == length vs
                             -> Just (ACon n ts, OpenCon k ts <$> zipWithM (checkV c) vs (map (inst tvs ts) fs))
                           _ -> Nothing
      Lam ps r e -> Just (AFun [(m,t) | (_,m,t) <- ps] r, lam)
        where
          lam = do ps' <- annParams c ps
                   Lam ps' r <$> annE c{ ctxGamma = lamGamma ps' (ctxGamma c), ctxJoins = M.empty } e r
      InjA{} -> Nothing
      Roll{} -> Nothing
      InjLazy{} -> Nothing
  where
    done t = Just (t, return val)
