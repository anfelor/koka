-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

module Backend.Typed.Elab.FromCore( elabProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List( find )
import Control.Monad( foldM, unless )
import Common.Name
import Common.NamePrim( nameFieldAddrOf, nameCCtxHoleCreate, nameCCtxCreate, nameCCtxExtend, nameCCtxApply, nameCCtxEmpty, nameCCtxCompose, nameCCtxComposeExtend )
import Common.Syntax( isDefFun, ParamInfo(..), Platform )
import qualified Common.Syntax as Syntax
import Kind.Newtypes
import Type.Type
import qualified Core.Core as C
import Core.Core( TName(..), typeOf )
import qualified Core.CoreVar as CV
import Core.Pretty()
import qualified Type.TypeVar as TV
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Elab.Types( typeDefs )
import Backend.Typed.TypeInfo
import Backend.Typed.Types
import Backend.Typed.Elab.Monad
import Backend.Typed.Elab.Coerce
import Backend.Typed.Names( nameUnreachable, isJoinName )
import Backend.Typed.Elab.Common( isValue, linearContexts, isLinearContextPrim )
import Backend.Typed.Pretty( ppr )

-- programs

elabProgram :: Platform -> Newtypes -> [C.Core] -> C.Core -> (Program,[String],[String])
elabProgram platform nt imports core
  = let defs    = map closeDef (filter (not . isContextAccessor) (C.flattenDefGroups (C.coreProgDefs core)))
        isigs   = M.fromList [(n,withModes modes sig) | (n,(tp,isFun,modes)) <- M.toList (importSigs (core:imports)), Right sig <- [typeSig nt tp isFun]]
        env0    = Env nt S.empty S.empty isigs M.empty S.empty M.empty
        tdefs   = typeDefs platform nt
        run (sigs,ds,errs,notes) def
          = let label msg = show (C.defName def) ++ ": " ++ msg
            in case runE (elabDef def) env0 (St 0 sigs []) of
                 Right ((d,sig),st) -> (M.insert (C.defName def) sig (stSigs st), ds ++ [d], errs, notes ++ map label (stNotes st))
                 Left err -> (sigs, ds, errs ++ [label err], notes)
        (sigs,ds,errs,notes) = foldl run (M.empty,[],[],[]) defs
    in (Program (C.coreProgName core) tdefs sigs ds, errs, notes)

-- Koka leaves the type variables that nothing constrains free: they become `any`
closeDef :: C.Def -> C.Def
closeDef def = TV.subNew [(tv,typeAny) | tv <- TV.tvsList (TV.ftv def), tvarStar tv] TV.|-> def

-- Koka's accessors of the fields of its abstract `cctx` would expose the hole. A context is
-- abstract in the IR, so they are left out.
isContextAccessor :: C.Def -> Bool
isContextAccessor def = C.defName def `elem` [newLocallyQualified "std/core/types" "cctx" f | f <- ["res","holeptr"]]

elabDef :: C.Def -> E (Def,Sig)
elabDef def
  = case splitLam (C.defExpr def) of
      Just (_,pars,body) | isDefFun (C.defSort def) -> elabFunDef def pars body
      Nothing | isDefFun (C.defSort def) -> failE "function definition is not a lambda"
      _ -> elabValDef def

elabFunDef :: C.Def -> [TName] -> C.Expr -> E (Def,Sig)
elabFunDef def pars body
  = do (tvs,args,res) <- funSig (typeOf (C.defExpr def))
       body' <- withTVars tvs (withLocals (map getName pars) (elabExprAt res body))
       let params = withParamModes (defModes def) args
           args' = [(root (getName p),m,t) | (p,(m,t)) <- zip pars params]
       return (DefFun (C.defName def) tvs args' res body', SigFun tvs params res)

elabValDef :: C.Def -> E (Def,Sig)
elabValDef def
  = do e <- env
       (tvs,t) <- tr (elabScheme (envNT e) (typeOf (C.defExpr def)))
       body <- withTVars tvs (elabExprAt t (stripTypeLam (C.defExpr def)))
       return (DefVal (C.defName def) tvs t body, SigVal tvs t)

importSigs :: [C.Core] -> M.Map Name (Type,Bool,[Mode])
importSigs cores
  = M.fromList ([(C.defName d, (C.defType d, isDefFun (C.defSort d), defModes d)) | c <- cores, d <- C.flattenDefGroups (C.coreProgDefs c)]
                ++ [(C.externalName x, (C.externalType x, True, [paramMode p False | p <- C.externalParams x])) | c <- cores, x@(C.External{}) <- C.coreProgExternals c])

-- The parameter modes of a function: borrowed as Koka infers, and unique for a context that
-- the body plugs or extends in place.
defModes :: C.Def -> [Mode]
defModes def
  = case C.defSort def of
      Syntax.DefFun pinfos _
        -> case splitLam (C.defExpr def) of
             Just (_,pars,body) -> let linear = linearContexts body
                                   in [paramMode p (S.member (getName x) linear) | (x,p) <- zip pars (pinfos ++ repeat Own)]
             Nothing -> [paramMode p False | p <- pinfos]
      _ -> []

paramMode :: ParamInfo -> Bool -> Mode
paramMode Borrow _     = Borrowed
paramMode _ True       = Unique
paramMode _ False      = Owned

-- Preserve the same calling convention for definitions and imported call sites.
withModes :: [Mode] -> Sig -> Sig
withModes modes sig
  = case sig of
      SigFun tvs ps r -> SigFun tvs (withParamModes modes ps) r
      _ -> sig

withParamModes :: [Mode] -> [(Mode,VType)] -> [(Mode,VType)]
withParamModes modes ps = [(m,t) | ((_,t),m) <- zip ps (modes ++ repeat Owned)]

typeSig :: Newtypes -> Type -> Bool -> Tr Sig
typeSig nt tp isFun
  | isFun     = (\(tvs,args,res) -> SigFun tvs args res) <$> funSigOf nt tp
  | otherwise = uncurry SigVal <$> elabScheme nt tp

funSigOf :: Newtypes -> Type -> Tr ([TVar],[(Mode,VType)],VType)
funSigOf nt tp
  = do a <- elabFunType nt tp
       case a of
         AForall tvs (AFun args res) -> Right (tvs,args,res)
         AFun args res               -> Right ([],args,res)
         _                           -> Left "expecting a function signature"

splitLam :: C.Expr -> Maybe ([TypeVar],[TName],C.Expr)
splitLam expr
  = case expr of
      C.TypeLam tvs (C.Lam pars _ body) -> Just (tvs,pars,body)
      C.Lam pars _ body                 -> Just ([],pars,body)
      _                                 -> Nothing

stripTypeLam :: C.Expr -> C.Expr
stripTypeLam (C.TypeLam _ e) = e
stripTypeLam e               = e

funSig :: Type -> E ([TVar],[(Mode,VType)],VType)
funSig tp
  = do e <- env
       tr (funSigOf (envNT e) tp)

-- expressions

elabExpr :: C.Expr -> E VExpr
elabExpr expr
  = case expr of
      C.Let [] body -> elabExpr body
      C.Let (C.DefNonRec (C.Def{ C.defName = j, C.defExpr = lam }) : dgs) body | isJoinName j, Just (tvs,pars,e1) <- splitLam lam
        -> do let linear = linearContexts e1
                  tvs'   = [typevarId tv | tv <- tvs, tvarStar tv]
              (ps,e1') <- withTVars tvs' $
                          do ps <- mapM (\p -> (\t -> (root (getName p),paramMode Own (S.member (getName p) linear),t)) <$> vt (tnameType p)) pars
                             (,) ps <$> withLocals (map getName pars) (elabExpr e1)
              Join j tvs' ps e1' <$> elabExpr (C.Let dgs body)
      C.App f args | (Just (TName j tp,_),tys) <- splitTypeApp f, isJoinName j, Just (pars,_,_) <- splitFunType (typeOf f)
        -> do tys' <- instArgs tp tys
              (ks,vs) <- unzip <$> mapM (\((_,ptp),arg) -> do t <- vt ptp
                                                              elabValAt t arg) (zip pars args)
              return (compose ks (Jump j tys' vs))
      C.Let (C.DefNonRec def : dgs) body
        -> elabLet def (C.Let dgs body)
      C.Let (C.DefRec defs : _) _
        -> failE ("local recursive definition: " ++ show (map C.defName defs))
      C.TypeLam tvs e | not (any tvarStar tvs) -> elabExpr e
      C.TypeLam tvs e | not (isValue expr) -> elabGen [typevarId tv | tv <- tvs, tvarStar tv] e (typeOf expr)
      C.Case [scrut] brs -> elabCase scrut brs
      C.Case _ _ -> failE "case with multiple scrutinees after matching"
      C.App f args | not (isConApp f) -> elabApp f args (typeOf expr)
      _ -> do (k,v) <- elabVal expr
              return (k (Ret v))

-- The parts of a context under construction are not bound: their uses become parts of the
-- `ctx` value (see `elabCtx`).
elabLet :: C.Def -> C.Expr -> E VExpr
elabLet def body
  = do en <- env
       let x = C.defName def
       if isFieldAddr en (C.defExpr def) then withHole x Nothing (elabExpr body)
       else if hasHole en (C.defExpr def)
         then do (k,v) <- elabVal (C.defExpr def)
                 k <$> withHole x (Just v) (elabExpr body)
       -- Match introduces aliases for pattern fields. Preserve their getters:
       -- binding a projected value inside a let would acquire a reference and
       -- hide the alias from copy propagation before Perceus.
       else if fieldAlias en (C.defExpr def)
         then do t <- vt (C.defType def)
                 getter <- elabValAt t (C.defExpr def)
                 withFields [(x,getter)] (elabExpr body)
         else do t  <- vt (C.defType def)
                 e1 <- elabExprAt t (C.defExpr def)
                 e2 <- withLocals [x] (elabExpr body)
                 return (Let (root x) t e1 e2)
  where
    fieldAlias en (C.Var (TName y _) _) = M.member y (envFields en)
    fieldAlias _ _ = False

elabGen :: [TVar] -> C.Expr -> Type -> E VExpr
elabGen tvs e tp
  = do target <- vt tp
       case target of
         VPtr (AForall tvs' a)
           -> do let a' = inst tvs (map AVar tvs') a
                 body <- withTVars tvs' (elabExprAt (VPtr a') e)
                 return (Gen tvs' body)
         _ -> failE ("type abstraction at the monomorphic type " ++ ppr target)

elabExprAt :: VType -> C.Expr -> E VExpr
elabExprAt t e
  = do e' <- elabExpr e
       t0 <- vt (typeOf e)
       if alphaEq t0 t then return e'
         else do r <- fresh "g"
                 (k,v) <- coerce t0 t (Var r)
                 return (Let r t0 e' (k (Ret v)))

isConApp :: C.Expr -> Bool
isConApp (C.Con _ _)     = True
isConApp (C.TypeApp e _) = isConApp e
isConApp _               = False

-- applications

elabApp :: C.Expr -> [C.Expr] -> Type -> E VExpr
elabApp f args resTp
  | isPrim nameCCtxEmpty f
  = do t <- vt resTp
       b <- holeType t
       return (Ret (Context b Hole))
  | isPrim nameCCtxCreate f, [res,addr] <- args
  = elabCtx Nothing res addr resTp
  | isPrim nameCCtxExtend f, [acc,res,addr] <- args
  = elabCtx (Just (isLinearContextPrim f, acc)) res addr resTp
  | isPrim nameCCtxApply f, [acc,_] <- args
  = do t <- vt (typeOf acc)
       (a,b) <- case t of
                  VCtx _ a b -> return (a,b)
                  _ -> failE ("plugging a non-context: " ++ ppr t)
       let shared = not (isLinearContextPrim f)
       callWith (\[c,v] -> return (Ret (Plug (ctxCopy shared c) v))) [t, VPtr b] (VPtr a) args resTp
  | isPrim nameCCtxCompose f
  = do t <- vt resTp
       ts <- mapM (vt . typeOf) args
       callWith (\[c,d] -> return (Ret (Append (CtxCopy c) (CtxCopy d)))) ts t args resTp
  | any (`isPrim` f) [nameCCtxHoleCreate, nameFieldAddrOf]
  = failE "a hole outside of a context"
  -- extends with the hole of a context that may be shared, without copying its path
  | isPrim nameCCtxComposeExtend f
  = failE "unsupported context primitive: @cctx-compose-extend"
elabApp f args resTp
  = do mbsig <- globalOf f
       case mbsig of
         Just (g,sig@(SigFun _ ps _),gtp,tys)
           -> do (tysD,params,res) <- instFun g sig gtp tys
                 e <- env
                 let copies = [m == Unique && captured e arg | ((m,_),arg) <- zip ps args] ++ repeat False
                 callWith (return . Call g tysD . zipWith ctxCopy copies) params res args resTp
         _ -> do (k1,fv) <- elabVal f
                 (params,res) <- funType f
                 body <- callWith (applyFun (AFun params res) fv) (map snd params) res args resTp
                 return (k1 body)

globalOf :: C.Expr -> E (Maybe (Name,Sig,Type,[Type]))
globalOf f
  = case splitTypeApp f of
      (Just (TName g gtp,info),tys) ->
        do e <- env
           if S.member g (envLocals e)
             then return Nothing
             else do sig <- globalSig g gtp info
                     return (Just (g,sig,gtp,tys))
      _ -> return Nothing

globalSig :: Name -> Type -> C.VarInfo -> E Sig
globalSig g gtp info
  = do e <- env
       sig <- case M.lookup g (envSigs e) of
                Just sig -> return sig
                Nothing  -> do note ("signature from use site: " ++ show g)
                               tr (typeSig (envNT e) gtp (isFunInfo info))
       recordSig g sig
       return sig

isFunInfo :: C.VarInfo -> Bool
isFunInfo (C.InfoArity _ _)  = True
isFunInfo (C.InfoExternal _) = True
isFunInfo _                  = False

instFun :: Name -> Sig -> Type -> [Type] -> E ([AType],[VType],VType)
instFun g (SigFun tvs params res) gtp tys
  = do e <- env
       tys' <- instArgs gtp tys
       useA <- tr (elabFunType (envNT e) gtp)
       let pat = AFun params res
           (utvs,ubody) = splitForallA useA
           used = inst utvs tys' ubody
       case (fmap (M.map (inst utvs tys')) (match tvs pat ubody), match tvs pat used) of
         (Just sub,_) -> return (map (instOf sub) tvs, map (subst sub . snd) params, subst sub res)
         (_,Just sub) -> return (map (instOf sub) tvs, map (subst sub . snd) params, subst sub res)
         _ -> failE ("use of " ++ show g ++ " does not match its signature:\n  declared: " ++ show pat ++ "\n  used    : " ++ show ubody)
instFun g _ _ _ = failE ("not a function: " ++ show g)

splitForallA :: AType -> ([TVar],AType)
splitForallA (AForall tvs a) = (tvs,a)
splitForallA a = ([],a)

instOf :: Sub -> TVar -> AType
instOf sub tv = M.findWithDefault atAny tv sub

instVal :: Name -> Sig -> Type -> [Type] -> E ([AType],VType)
instVal g (SigVal tvs t) gtp tys
  = do e <- env
       tys' <- instArgs gtp tys
       (utvs,ut) <- tr (elabScheme (envNT e) gtp)
       case match tvs t ut of
         Just sub0 -> let sub = M.map (inst utvs tys') sub0
                      in return (map (instOf sub) tvs, subst sub t)
         Nothing   -> failE ("use of " ++ show g ++ " does not match its signature:\n  declared: " ++ show t ++ "\n  used    : " ++ show ut)
instVal g _ _ _ = failE ("not a value: " ++ show g)

funType :: C.Expr -> E ([(Mode,VType)],VType)
funType f = do t <- vt (typeOf f)
               case t of
                 VPtr (AFun params res) -> return (params,res)
                 _ -> failE ("expecting a function value: " ++ ppr t)

callWith :: ([VVal] -> E VExpr) -> [VType] -> VType -> [C.Expr] -> Type -> E VExpr
callWith call params res args resTp
  = do (ks,vs) <- unzip <$> mapM (\(p,arg) -> elabValAt p arg) (zip params args)
       expect <- vt resTp
       r <- fresh "r"
       (kr,vr) <- coerce res expect (Var r)
       app <- call vs
       let body = if alphaEq res expect then app else Let r res app (kr (Ret vr))
       return (compose ks body)

splitTypeApp :: C.Expr -> (Maybe (TName,C.VarInfo),[Type])
splitTypeApp expr
  = case expr of
      C.TypeApp (C.Var x info) tys -> (Just (x,info),tys)
      C.Var x info                 -> (Just (x,info),[])
      _                            -> (Nothing,[])

instArgs :: Type -> [Type] -> E [AType]
instArgs gtp tys
  = do e <- env
       tr (elabArgs (envNT e) (fst (splitForall gtp)) tys)

splitForall :: Type -> ([TypeVar],Type)
splitForall tp
  = case tp of
      TForall tvs t -> (tvs,t)
      TSyn _ _ t    -> splitForall t
      _             -> ([],tp)

-- values

elabValAt :: VType -> C.Expr -> E (K,VVal)
elabValAt expect@(VPtr a@(AFun qs _)) (C.Lam pars _ body) | length qs == length pars
  = do (k,lam) <- captureFields body (elabLam expect pars body)
       return (k, Ptr a lam)
elabValAt expect expr
  = do (k1,v) <- elabVal expr
       t <- vt (typeOf expr)
       (k2,v') <- coerce t expect v
       return (k1 . k2, v')

elabVal :: C.Expr -> E (K,VVal)
elabVal expr
  = case expr of
      C.Var (TName x tp) _ | x == nameUnreachable -> unreachable tp
      C.App f [] | isPrim nameCCtxHoleCreate f -> return (id, Hole)
      C.Var (TName x tp) info -> elabVar x tp info []
      C.TypeApp (C.Var (TName x tp) info) tys -> elabVar x tp info tys
      C.Lit lit -> return (id, Lit (elabLit lit))
      _ | isConApp expr -> case expandSyn (typeOf expr) of
                              TFun pars eff _ -> etaCon expr pars eff
                              TForall tvs _ -> generalize [typevarId tv | tv <- tvs, tvarStar tv] (elabCon expr []) (typeOf expr)
                              _ -> elabCon expr []
      C.App f args | isConApp f -> elabCon f args
      C.TypeApp e tys
        -> do (k1,v) <- elabVal e
              tys' <- instArgs (typeOf e) tys
              if null tys' then return (k1,v)
                else do a <- ptrType (typeOf e)
                        expect <- vt (typeOf expr)
                        (k2,v') <- coerce (VPtr (instA a tys')) expect (tapp v tys')
                        return (k1 . k2,v')
      C.TypeLam tvs e | not (any tvarStar tvs) -> elabVal e
      C.Lam pars _ body -> do t <- vt (typeOf expr)
                              (k,lam) <- captureFields body (elabLam t pars body)
                              (kg,v) <- genVal t lam
                              return (k . kg,v)
      C.TypeLam tvs (C.Lam pars _ body)
        -> do t <- vt (typeOf expr)
              (k,lam) <- captureFields body (withTVars (map typevarId tvs) (elabLam (stripForallV t) pars body))
              (kg,v) <- genVal t lam
              return (k . kg,v)
      C.TypeLam tvs e | isValue e -> elabTypeLam [typevarId tv | tv <- tvs, tvarStar tv] e (typeOf expr)
      _ -> do t <- vt (typeOf expr)
              x <- fresh "a"
              e <- elabExpr expr
              return (Let x t e, Var x)

elabTypeLam :: [TVar] -> C.Expr -> Type -> E (K,VVal)
elabTypeLam tvs e tp = generalize tvs (elabVal e) tp

-- a pointer value at its polymorphic type `tp`
generalize :: [TVar] -> E (K,VVal) -> Type -> E (K,VVal)
generalize tvs elab tp
  = do (k,v) <- withTVars tvs elab
       target <- vt tp
       (k2,v') <- genPtr target v
       return (k . k2, v')

unreachable :: Type -> E (K,VVal)
unreachable tp
  = do t <- vt tp
       let a = -2
       recordSig nameUnreachable (SigFun [a] [] (varV a))
       x <- fresh "u"
       (k,v) <- coerce (boxrep t) t (Var x)
       return (Let x (boxrep t) (Call nameUnreachable [rep t] []) . k, v)

etaCon :: C.Expr -> [(Name,Type)] -> Type -> E (K,VVal)
etaCon con pars eff
  = do xs <- mapM (\(_,tp) -> (\x -> TName x tp) <$> freshName "c") pars
       elabVal (C.Lam xs eff (C.App con [C.Var x C.InfoNone | x <- xs]))

-- A closure retains the fields it captures now, so its body uses established
-- component variables instead of reading through a parent captured by accident.
captureFields :: C.Expr -> E a -> E (K,a)
captureFields body action = do
  en <- env
  let fields = [(x,getter) | TName x _ <- S.toList (CV.fv body), Just getter <- [M.lookup x (envFields en)]]
      ks = [k | (_, (k,_)) <- fields]
      bound = [(x,(id,v)) | (x,(_,v)) <- fields]
  a <- withFields bound action
  return (compose ks,a)

elabLam :: VType -> [TName] -> C.Expr -> E AVal
elabLam (VPtr (AFun qs res)) pars body
  = do (ps,ks) <- unzip <$> mapM lamParam (zip pars qs)
       body' <- inClosure (withLocals (map getName pars) (elabExprAt res body))
       return (Lam ps res (compose ks body'))
elabLam t _ _ = failE ("expecting a function type for a lambda: " ++ ppr t)

lamParam :: (TName,(Mode,VType)) -> E ((Path,Mode,VType),K)
lamParam (p,(m,q))
  = do t <- vt (tnameType p)
       if alphaEq q t then return ((root (getName p),m,q),id)
         else do y <- fresh "a"
                 (k,v) <- coerce q t (Var y)
                 return ((y,m,q), k . Let (root (getName p)) t (Ret v))

stripForallV :: VType -> VType
stripForallV (VPtr (AForall _ a)) = VPtr a
stripForallV t = t

elabLit :: C.Lit -> Lit
elabLit lit
  = case lit of
      C.LitInt i    -> LitInt i
      C.LitFloat d  -> LitFloat d
      C.LitChar c   -> LitChar c
      C.LitString s -> LitString s

elabVar :: Name -> Type -> C.VarInfo -> [Type] -> E (K,VVal)
elabVar x tp info tys
  = do e <- env
       case M.lookup x (envHoles e) of
         Just (Just v) -> return (id, v)
         Just Nothing  -> failE ("the address of a hole outside of a context: " ++ show x)
         Nothing       -> elabNamed e x tp info tys

elabNamed :: Env -> Name -> Type -> C.VarInfo -> [Type] -> E (K,VVal)
elabNamed e x tp info tys
  = do expect <- vt (typeOf (mkTypeApp (C.Var (TName x tp) info) tys))
       if S.member x (envLocals e)
         then do tys' <- instArgs tp tys
                 let (k,v) = M.findWithDefault (id,Var (root x)) x (envFields e)
                 (ki,w) <- instLocal v tp tys' expect
                 return (k . ki,w)
         else do sig <- globalSig x tp info
                 case sig of
                   SigFun tvs ps r -> do (tysD,params,res) <- instFun x sig tp tys
                                         let a = AFun [(Owned,p) | p <- params] res
                                         f <- if any ((/= Owned) . fst) ps then Ptr a <$> etaOwned x tysD params res
                                                                           else return (tapp (Ptr (forallA tvs (AFun ps r)) (Fun x)) tysD)
                                         coerce (VPtr a) expect f
                   SigVal _ _   -> do (tysD,t) <- instVal x sig tp tys
                                      coerce t expect (Glob x tysD)
                   SigCon _ _ _ -> failE ("constructor used as a variable: " ++ show x)

-- closures only have owned parameters ([fun]): wrap a function that borrows (or takes a unique argument)
etaOwned :: Name -> [AType] -> [VType] -> VType -> E AVal
etaOwned x tysD params res
  = do ys <- mapM (const (fresh "e")) params
       return (Lam [(y,Owned,p) | (y,p) <- zip ys params] res (Call x tysD (map Var ys)))

instLocal :: VVal -> Type -> [AType] -> VType -> E (K,VVal)
instLocal v _ [] _ = return (id,v)
instLocal v tp tys' expect
  = do a <- ptrType tp
       coerce (VPtr (instA a tys')) expect (TyApp v tys')

ptrType :: Type -> E AType
ptrType tp = do t <- vt tp
                case t of
                  VPtr a -> return a
                  _      -> failE ("expecting a pointer type: " ++ ppr t)

mkTypeApp :: C.Expr -> [Type] -> C.Expr
mkTypeApp e []  = e
mkTypeApp e tys = C.TypeApp e tys

instA :: AType -> [AType] -> AType
instA (AForall tvs a) tys = inst tvs tys a
instA a _ = a

-- constructors

elabCon :: C.Expr -> [C.Expr] -> E (K,VVal)
elabCon conExpr args
  = do (info,vargs) <- dataArgs (resultType (typeOf conExpr))
       -- the context path of a constructor (`conReprCtxPath`) is recorded by `[ctx]` instead
       elabConArgs info vargs conExpr args

elabConArgs :: DataInfo -> [AType] -> C.Expr -> [C.Expr] -> E (K,VVal)
elabConArgs info vargs conExpr args
  = do let C.Con (TName cname scheme) _ = stripTypeApp conExpr
       if dataInfoIsOpen info
         then elabOpenCon info vargs cname scheme args
         else do con <- conInfoE info cname
                 elabConWith info vargs con args

elabConWith :: DataInfo -> [AType] -> ConInfo -> [C.Expr] -> E (K,VVal)
elabConWith info vargs con args
  = do let cname = conInfoName con
       idx <- tr (conIndex info cname)
       fields <- fieldTypes vargs con
       argTys <- mapM (vt . typeOf) args
       exSub <- tr (existsSub (conExists con) fields argTys)
       (ks,vs) <- unzip <$> mapM (\(t,arg) -> elabValAt t arg) (zip (map (subst exSub) fields) args)
       v <- conValue info vargs idx exSub (prodVal vs)
       return (compose ks, v)

elabOpenCon :: DataInfo -> [AType] -> Name -> Type -> [C.Expr] -> E (K,VVal)
elabOpenCon info vargs cname scheme args
  = do recordOpenSig info cname scheme
       fields <- schemeFields vargs scheme
       (ks,vs) <- unzip <$> mapM (\(t,arg) -> elabValAt t arg) (zip fields args)
       return (compose ks, Ptr (ACon (dataInfoName info) vargs) (OpenCon cname vargs vs))

recordOpenSig :: DataInfo -> Name -> Type -> E ()
recordOpenSig info cname scheme
  = do let tvs = [typevarId tv | tv <- dataInfoParams info, tvarStar tv]
       fields <- schemeFields (map AVar tvs) scheme
       recordSig cname (SigCon tvs fields (dataInfoName info))

schemeFields :: [AType] -> Type -> E [VType]
schemeFields vargs scheme
  = do e <- env
       tr (schemeFieldTypes (envNT e) vargs scheme)

existsSub :: [TVar] -> [VType] -> [VType] -> Tr Sub
existsSub [] _ _ = Right M.empty
existsSub tvs pats ts = foldM add M.empty (zip pats ts)
  where
    add sub (VPtr (AVar v), t) | v `elem` tvs = Right (M.insert v (rep t) sub)
    add sub (p, t) = maybe (Left ("cannot instantiate existential field " ++ ppr p ++ " with " ++ ppr t)) (Right . M.union sub) (match tvs p t)

stripTypeApp :: C.Expr -> C.Expr
stripTypeApp (C.TypeApp e _) = stripTypeApp e
stripTypeApp e = e

resultType :: Type -> Type
resultType tp
  = case expandSyn tp of
      TForall _ t  -> resultType t
      TFun _ _ res -> res
      t            -> t

dataArgs :: Type -> E (DataInfo,[AType])
dataArgs tp
  = do e <- env
       (name,args) <- case expandSyn tp of
                        TCon tc               -> return (typeconName tc,[])
                        TApp (TCon tc) args   -> return (typeconName tc,args)
                        t -> failE ("expecting a datatype: " ++ show t)
       info <- tr (dataInfoOf (envNT e) name)
       vargs <- tr (elabArgs (envNT e) (dataInfoParams info) args)
       return (info,vargs)

conInfoE :: DataInfo -> Name -> E ConInfo
conInfoE info cname
  = maybe (failE ("unknown constructor: " ++ show cname)) return
          (find (\c -> conInfoName c == cname) (dataInfoConstrs info))

fieldTypes :: [AType] -> ConInfo -> E [VType]
fieldTypes vargs con
  = do e <- env
       tr (conFieldTypes (envNT e) vargs con)

prodVal :: [VVal] -> VVal
prodVal []     = UnitV
prodVal [v]    = v
prodVal (v:vs) = Pair v (prodVal vs)

conValue :: DataInfo -> [AType] -> Int -> Sub -> VVal -> E VVal
conValue info vargs idx exSub v
  | isValueInfo info = do t <- dataType info vargs
                          let packed = packV (conTypes t) v
                          return (if conCount info > 1 then Inj idx t packed else packed)
  | otherwise = do shapes <- conShapes info vargs
                   let t = ACon (dataInfoName info) vargs
                   return (Ptr t (Roll t (injA shapes idx (shapeVal (shapes !! idx)))))
  where
    shapeVal (ABox t) = Box (packV t v)
    shapeVal _ = UnitA
    conTypes (VSum ts) | conCount info > 1 = ts !! idx
    conTypes t = t
    packV t@(VExists tvs _) w = Pack t (exTypes tvs) w
    packV _ w = w
    exTypes tvs = [M.findWithDefault atAny tv exSub | tv <- tvs]

dataType :: DataInfo -> [AType] -> E VType
dataType info vargs
  = do e <- env
       tr (valueBody (envNT e) info vargs)

conShapes :: DataInfo -> [AType] -> E [AType]
conShapes info vargs
  = do e <- env
       mapM (tr . conShape (envNT e) vargs) (dataInfoConstrs info)

-- constructor contexts

-- `@cctx-create(K, addr)` and `@cctx-extend(c, K, addr)` (that is, `c ++ ctx K`), where `addr`
-- is the address of the hole of `K` (`@field-addr-of`): the position of the hole in `K`
-- determines it. A context is plugged or appended to in place where `Core.CTail` knows it to be
-- unique (a linear primitive); otherwise it is first copied if it is shared.
elabCtx :: Maybe (Bool,C.Expr) -> C.Expr -> C.Expr -> Type -> E VExpr
elabCtx mbAcc res addr resTp
  = do en <- env
       unless (isFieldAddr en addr) (failE "a context whose hole is not the field of a constructor")
       t <- vt resTp
       b <- holeType t
       (k1,v) <- elabVal res
       case mbAcc of
         Nothing -> return (k1 (Ret (Context b v)))
         Just (linear,acc)
           -> do (k0,c) <- elabVal acc
                 return (k0 (k1 (Ret (Append (ctxCopy (not linear) c) (Context b v)))))

-- A closure (such as the continuation of an effect that may resume more than once) only owns
-- the contexts that it captures: it copies one that it passes to a unique parameter (if it is
-- shared).
captured :: Env -> C.Expr -> Bool
captured e arg
  = case arg of
      C.Var x _ -> S.member (getName x) (envCaptured e)
      _ -> False

ctxCopy :: Bool -> VVal -> VVal
ctxCopy True v = CtxCopy v
ctxCopy False v = v

-- the type of the hole of a context
holeType :: VType -> E AType
holeType t
  = case t of
      VCtx _ _ b -> return b
      _ -> failE ("expecting a context: " ++ ppr t)

-- the address of the hole of a context under construction: `@field-addr-of` or a variable
-- bound to it
isFieldAddr :: Env -> C.Expr -> Bool
isFieldAddr en expr
  = case expr of
      C.App f _ -> isPrim nameFieldAddrOf f
      C.Var x _ -> M.lookup (getName x) (envHoles en) == Just Nothing
      _ -> False

-- a value that contains the hole of a context under construction
hasHole :: Env -> C.Expr -> Bool
hasHole en expr
  = case expr of
      C.App f [] | isPrim nameCCtxHoleCreate f -> True
      C.App f args | isConApp f -> any (hasHole en) args
      C.Var x _ -> maybe False (/= Nothing) (M.lookup (getName x) (envHoles en))
      _ -> False

isPrim :: Name -> C.Expr -> Bool
isPrim name f
  = case stripTypeApp f of
      C.Var (TName g _) _ -> g == name
      _ -> False

-- matching

elabCase :: C.Expr -> [C.Branch] -> E VExpr
elabCase scrut brs
  = do let scrutTp = typeOf scrut
       expect <- vt scrutTp
       (k,v) <- elabValAt expect scrut
       body <- case [p | C.Branch [p] _ <- brs] of
                 (C.PatLit _ : _) -> elabLitCase v brs
                 _ | all isWild [p | C.Branch [p] _ <- brs] -> branchBody (head brs)
                 _ -> elabConCase scrutTp v brs
       return (k body)

isWild :: C.Pattern -> Bool
isWild C.PatWild = True
isWild _         = False

branchBody :: C.Branch -> E VExpr
branchBody (C.Branch _ [C.Guard _ e]) = elabExpr e
branchBody _ = failE "unexpected guards after matching"

elabLitCase :: VVal -> [C.Branch] -> E VExpr
elabLitCase v brs
  = do alts <- mapM (\b@(C.Branch [C.PatLit l] _) -> (,) (elabLit l) <$> branchBody b) [b | b@(C.Branch [C.PatLit _] _) <- brs]
       def  <- case [b | b@(C.Branch [C.PatWild] _) <- brs] of
                 (b:_) -> branchBody b
                 []    -> failE "literal match without default"
       return (CaseLit v alts def)

elabConCase :: Type -> VVal -> [C.Branch] -> E VExpr
elabConCase scrutTp v brs
  = do (info,vargs) <- dataArgs scrutTp
       if dataInfoIsOpen info then elabOpenCase info vargs v brs
       else if isValueInfo info then elabValueCase info vargs v brs
       else elabBoxedCase info vargs v brs

elabBoxedCase :: DataInfo -> [AType] -> VVal -> [C.Branch] -> E VExpr
elabBoxedCase info vargs v brs
  = do p <- fresh "d"
       z <- fresh "z"
       let cons = dataInfoConstrs info
           wild = [b | b@(C.Branch [C.PatWild] _) <- brs]
           matches c (C.Branch [C.PatCon pc _ _ _ _ _ _ _] _) = getName pc == conInfoName c
           matches _ _ = False
           selected = [(i,c) | (i,c) <- zip [1..] cons, null wild || any (matches c) brs]   -- by tag
       body <- case cons of
                 [con] -> conBranch vargs con (Left z) (findBranch con brs)
                 _ -> do alts <- mapM (boxedAlt vargs brs) selected
                         def <- case wild of
                                  b:_ | length selected < length cons -> do
                                    y <- fresh "default"
                                    e <- branchBody b
                                    return (Just (y,e))
                                  _ -> return Nothing
                         return (CaseA Owned z alts def)
       return (Deref Owned v p (Unroll Owned p z body))

boxedAlt :: [AType] -> [C.Branch] -> (Int,ConInfo) -> E (Int,Path,VExpr)
boxedAlt vargs brs (i,con)
  = do y <- fresh "y"
       e <- conBranch vargs con (Left y) (findBranch con brs)
       return (i,y,e)

elabValueCase :: DataInfo -> [AType] -> VVal -> [C.Branch] -> E VExpr
elabValueCase info vargs v brs
  = case dataInfoConstrs info of
      [con] -> conBranch vargs con (Right v) (findBranch con brs)
      cons  -> CaseV Owned v <$> mapM (valueAlt vargs brs) cons

valueAlt :: [AType] -> [C.Branch] -> ConInfo -> E (Path,VExpr)
valueAlt vargs brs con
  = do y <- fresh "y"
       b <- conBranch vargs con (Right (Var y)) (findBranch con brs)
       return (y,b)

elabOpenCase :: DataInfo -> [AType] -> VVal -> [C.Branch] -> E VExpr
elabOpenCase info vargs v brs
  = do p <- fresh "d"
       alts <- mapM (openAlt info vargs) [(c,b) | b@(C.Branch [C.PatCon{ C.patConInfo = c }] _) <- brs]
       def  <- case [b | b@(C.Branch [C.PatWild] _) <- brs] of
                 (b:_) -> branchBody b
                 []    -> failE "open match without default"
       return (Deref Owned v p (CaseOpen Owned p alts def))

-- one binder for each field
openAlt :: DataInfo -> [AType] -> (ConInfo,C.Branch) -> E (Name,[Path],VExpr)
openAlt info vargs (con,br@(C.Branch [pat] _))
  = do recordOpenSig info (conInfoName con) (conInfoType con)
       fields <- fieldTypes vargs con
       xs <- mapM (const (fresh "o")) fields
       getters <- concat <$> sequence [bindField (subBinder p) s (id,Var x) | (p,s,x) <- zip3 (C.patConPatterns pat) fields xs]
       body <- withFields getters (branchBody br)
       return (conInfoName con, xs, body)
openAlt _ _ _ = failE "unexpected open branch after matching"

findBranch :: ConInfo -> [C.Branch] -> Maybe C.Branch
findBranch con brs
  = case [b | b@(C.Branch [C.PatCon c _ _ _ _ _ _ _] _) <- brs, getName c == conInfoName con] of
      (b:_) -> Just b
      []    -> case [b | b@(C.Branch [C.PatWild] _) <- brs] of
                 (b:_) -> Just b
                 [] | conInfoIsLazy con -> Just (C.Branch [C.PatWild] [C.Guard C.exprTrue (C.Var (TName nameUnreachable (typeOf (head brs))) C.InfoNone)])
                    | otherwise -> Nothing

conBranch :: [AType] -> ConInfo -> Either Path VVal -> Maybe C.Branch -> E VExpr
conBranch _ con _ Nothing = failE ("missing branch for " ++ show (conInfoName con))
conBranch vargs con y (Just br@(C.Branch [pat] _))
  = withTVars (patExistIds pat) $ case pat of
      C.PatCon _ subs _ _ exists _ _ _ | not (null subs) -> do
        fields <- fieldTypes vargs con
        let exIds = [typevarId tv | tv <- exists, tvarStar tv]
            exSub = M.fromList (zip (conExists con) (map AVar exIds))
        (k,payload) <- openCon y (conExists con) exIds
        getters <- destructure (zip (map subBinder subs) (map (subst exSub) fields)) (id,payload)
        body <- withFields getters (branchBody br)
        return (k body)
      _ -> branchBody br
conBranch _ _ _ (Just _) = failE "unexpected branch after matching"

openCon :: Either Path VVal -> [TVar] -> [TVar] -> E (K,VVal)
openCon y exs exIds
  = do (k1,p) <- either unboxK (return . (,) id) y
       (k2,u) <- if null exs then return (id,p) else unpackK p exIds
       return (k1 . k2, u)

unboxK :: Path -> E (K,VVal)
unboxK y = do p <- fresh "p"
              return (Unbox Owned y p, Var p)

unpackK :: VVal -> [TVar] -> E (K,VVal)
unpackK v ids = do u <- fresh "e"
                   return (Unpack Owned v ids u, Var u)

patExistIds :: C.Pattern -> [TVar]
patExistIds (C.PatCon{ C.patExists = exists }) = map typevarId exists
patExistIds _ = []

patBinders :: C.Pattern -> [Name]
patBinders (C.PatCon _ subs _ _ _ _ _ _) = [getName x | C.PatVar x _ <- subs]
patBinders _ = []

subBinder :: C.Pattern -> Maybe TName
subBinder (C.PatVar x _) = Just x
subBinder _              = Nothing

-- Construct field getters without emitting reads. A variable occurrence asks
-- for its getter in the expression that actually uses the field.
-- Field i of n is at the steps `snd`ⁱ `fst`, and the last one at `snd`ⁿ⁻¹ (`[proj]`).
destructure :: [(Maybe TName,VType)] -> (K,VVal) -> E [(Name,(K,VVal))]
destructure [(x,s)] getter = bindField x s getter
destructure fields (k,p) = concat <$> mapM field (zip [0..] fields)
  where
    n = length fields
    field (i,(x,s)) = do
      y <- fresh "field"
      bindField x s (k . Proj Borrowed p (replicate i SSnd ++ [SFst | i < n-1]) y,Var y)

bindField :: Maybe TName -> VType -> (K,VVal) -> E [(Name,(K,VVal))]
bindField Nothing _ _ = return []
bindField (Just (TName x tp)) s (read,v) = do
  t <- vt tp
  (k,w) <- coerce s t v
  return [(x,(read . k,w))]
