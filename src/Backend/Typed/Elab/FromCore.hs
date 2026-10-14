-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

module Backend.Typed.Elab.FromCore( elabProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List( find )
import Control.Monad( foldM )
import Common.Name
import Common.NamePrim( nameFieldAddrOf )
import Common.Syntax( isDefFun, ParamInfo(..), Platform )
import Kind.Newtypes
import Type.Type
import qualified Core.Core as C
import Core.Core( TName(..), typeOf )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Elab.Types( typeDefs )
import Backend.Typed.TypeInfo
import Backend.Typed.Types
import Backend.Typed.Elab.Monad
import Backend.Typed.Elab.Coerce
import Backend.Typed.Names( nameUnreachable, nameSetCtxPath, isJoinName )
import Backend.Typed.Elab.Common( isValue )
import Backend.Typed.Pretty( ppr )

-- programs

elabProgram :: Platform -> Newtypes -> [C.Core] -> C.Core -> (Program,[String],[String])
elabProgram platform nt imports core
  = let defs    = C.flattenDefGroups (C.coreProgDefs core)
        isigs   = M.fromList [(n,withModes (if n == nameFieldAddrOf then Borrow : drop 1 pinfos else pinfos) sig) | (n,(tp,isFun,pinfos)) <- M.toList (importSigs (core:imports)), Right sig <- [typeSig nt tp isFun]]
        lsigs   = M.fromList [(C.defName d,sig) | d <- defs, Right sig <- [typeSig nt (C.defType d) (isDefFun (C.defSort d))]]
        env0    = Env nt S.empty S.empty (M.union lsigs isigs)
        tdefs   = typeDefs platform nt
        run (sigs,ds,errs,notes) def
          = let label msg = show (C.defName def) ++ ": " ++ msg
            in case runE (elabDef def) env0 (St 0 sigs []) of
                 Right ((d,sig),st) -> (M.insert (C.defName def) sig (stSigs st), ds ++ [d], errs, notes ++ map label (stNotes st))
                 Left err -> (sigs, ds, errs ++ [label err], notes)
        (sigs,ds,errs,notes) = foldl run (M.empty,[],[],[]) defs
    in (Program (C.coreProgName core) tdefs sigs ds, errs, notes)

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
       let args' = [(getName p,m,t) | (p,(m,t)) <- zip pars args]
       return (DefFun (C.defName def) tvs args' res body', SigFun tvs args res)

elabValDef :: C.Def -> E (Def,Sig)
elabValDef def
  = do e <- env
       (tvs,t) <- tr (elabScheme (envNT e) (typeOf (C.defExpr def)))
       body <- withTVars tvs (elabExprAt t (stripTypeLam (C.defExpr def)))
       return (DefVal (C.defName def) tvs t body, SigVal tvs t)

importSigs :: [C.Core] -> M.Map Name (Type,Bool,[ParamInfo])
importSigs cores
  = M.fromList ([(C.defName d, (C.defType d, isDefFun (C.defSort d), [])) | c <- cores, d <- C.flattenDefGroups (C.coreProgDefs c)]
                ++ [(C.externalName x, (C.externalType x, True, C.externalParams x)) | c <- cores, x@(C.External{}) <- C.coreProgExternals c])

-- only externals borrow parameters: their C code expects it
withModes :: [ParamInfo] -> Sig -> Sig
withModes pinfos sig
  = case sig of
      SigFun tvs ps r -> SigFun tvs [(if pinfo == Borrow then Borrowed else m, t) | ((m,t),pinfo) <- zip ps (pinfos ++ repeat Own)] r
      _ -> sig

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
      C.Let (C.DefNonRec (C.Def{ C.defName = j, C.defExpr = C.Lam pars _ e1 }) : dgs) body | isJoinName j
        -> do ps  <- mapM (\p -> (\t -> (getName p,Owned,t)) <$> vt (tnameType p)) pars
              e1' <- withLocals (map getName pars) (elabExpr e1)
              Join j ps e1' <$> elabExpr (C.Let dgs body)
      C.App (C.Var (TName j tp) _) args | isJoinName j, Just (pars,_,_) <- splitFunType tp
        -> do (ks,vs) <- unzip <$> mapM (\((_,ptp),arg) -> do t <- vt ptp
                                                              elabValAt t arg) (zip pars args)
              return (compose ks (Jump j vs))
      C.Let (C.DefNonRec def : dgs) body
        -> do t  <- vt (C.defType def)
              e1 <- elabExprAt t (C.defExpr def)
              e2 <- withLocals [C.defName def] (elabExpr (C.Let dgs body))
              return (Let (C.defName def) t e1 e2)
      C.Let (C.DefRec defs : _) _
        -> failE ("local recursive definition: " ++ show (map C.defName defs))
      C.TypeLam tvs e | not (any tvarStar tvs) -> elabExpr e
      C.TypeLam tvs e | not (isValue expr) -> elabGen [typevarId tv | tv <- tvs, tvarStar tv] e (typeOf expr)
      C.Case [scrut] brs -> elabCase scrut brs
      C.Case _ _ -> failE "case with multiple scrutinees after matching"
      C.App f args | not (isConApp f) -> elabApp f args (typeOf expr)
      _ -> do (k,v) <- elabVal expr
              return (k (Ret v))

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
  = do mbsig <- globalOf f
       case mbsig of
         Just (g,sig@(SigFun _ _ _),gtp,tys)
           -> do (tysD,params,res) <- instFun g sig gtp tys
                 callWith (Call g tysD) params res args resTp
         _ -> do (k1,fv) <- elabVal f
                 g <- fresh "f"
                 (params,res) <- funType f
                 body <- callWith (App g) (map snd params) res args resTp
                 return (k1 (Deref Owned fv g body))

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

callWith :: ([VVal] -> VExpr) -> [VType] -> VType -> [C.Expr] -> Type -> E VExpr
callWith call params res args resTp
  = do (ks,vs) <- unzip <$> mapM (\(p,arg) -> elabValAt p arg) (zip params args)
       expect <- vt resTp
       r <- fresh "r"
       (kr,vr) <- coerce res expect (Var r)
       let body = if alphaEq res expect then call vs else Let r res (call vs) (kr (Ret vr))
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
  = do lam <- elabLam expect pars body
       return (id, Ptr a lam)
elabValAt expect expr
  = do (k1,v) <- elabVal expr
       t <- vt (typeOf expr)
       (k2,v') <- coerce t expect v
       return (k1 . k2, v')

elabVal :: C.Expr -> E (K,VVal)
elabVal expr
  = case expr of
      C.Var (TName x tp) _ | x == nameUnreachable -> unreachable tp
      C.Var (TName x tp) info -> elabVar x tp info []
      C.TypeApp (C.Var (TName x tp) info) tys -> elabVar x tp info tys
      C.Lit lit -> return (id, Lit (elabLit lit))
      _ | isConApp expr -> case expandSyn (typeOf expr) of
                              TFun pars eff _ -> etaCon expr pars eff
                              TForall tvs _ -> generalize [typevarId tv | tv <- tvs, tvarStar tv] (elabCon expr []) (typeOf expr)
                              _ -> elabCon expr []
      C.App f args | isConApp f -> elabCon f args
      C.TypeLam tvs e | not (any tvarStar tvs) -> elabVal e
      C.Lam pars _ body -> do t <- vt (typeOf expr)
                              lam <- elabLam t pars body
                              genVal t lam
      C.TypeLam tvs (C.Lam pars _ body)
        -> do t <- vt (typeOf expr)
              lam <- withTVars (map typevarId tvs) (elabLam (stripForallV t) pars body)
              genVal t lam
      C.TypeLam tvs e | isValue e -> elabTypeLam [typevarId tv | tv <- tvs, tvarStar tv] e (typeOf expr)
      _ -> failE ("unsupported value expression: " ++ exprKind expr)

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

exprKind :: C.Expr -> String
exprKind expr
  = case expr of
      C.TypeLam _ e -> "type lambda over " ++ exprKind e
      C.TypeApp e _ -> "type application of " ++ exprKind e
      C.App _ _     -> "application"
      C.Let _ _     -> "let"
      C.Case _ _    -> "case"
      C.Var x _     -> "variable " ++ show (getName x)
      _             -> "other"

etaCon :: C.Expr -> [(Name,Type)] -> Type -> E (K,VVal)
etaCon con pars eff
  = do xs <- mapM (\(_,tp) -> (\x -> TName x tp) <$> fresh "c") pars
       elabVal (C.Lam xs eff (C.App con [C.Var x C.InfoNone | x <- xs]))

elabLam :: VType -> [TName] -> C.Expr -> E AVal
elabLam (VPtr (AFun qs res)) pars body
  = do (ps,ks) <- unzip <$> mapM lamParam (zip pars qs)
       body' <- withLocals (map getName pars) (elabExprAt res body)
       return (Lam ps res (compose ks body'))
elabLam t _ _ = failE ("expecting a function type for a lambda: " ++ ppr t)

lamParam :: (TName,(Mode,VType)) -> E ((Name,Mode,VType),K)
lamParam (p,(m,q))
  = do t <- vt (tnameType p)
       if alphaEq q t then return ((getName p,m,q),id)
         else do y <- fresh "a"
                 (k,v) <- coerce q t (Var y)
                 return ((y,m,q), k . Let (getName p) t (Ret v))

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
       expect <- vt (typeOf (mkTypeApp (C.Var (TName x tp) info) tys))
       if S.member x (envLocals e)
         then do tys' <- instArgs tp tys
                 instLocal x tp tys' expect
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

instLocal :: Name -> Type -> [AType] -> VType -> E (K,VVal)
instLocal x _ [] _ = return (id, Var x)
instLocal x tp tys' expect
  = do a <- ptrType tp
       coerce (VPtr (instA a tys')) expect (TyApp (Var x) tys')

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
       (k,v) <- elabConArgs info vargs conExpr args
       case stripTypeApp conExpr of
         C.Con (TName cname _) repr | Just (C.CtxField fname) <- C.conReprCtxPath repr
           -> do t <- vt (resultType (typeOf conExpr))
                 x <- fresh "cp"
                 let a = -3
                 recordSig nameSetCtxPath (SigFun [a] [(Owned,varV a),(Owned,vtString),(Owned,vtString)] (varV a))
                 return (k . Let x t (Call nameSetCtxPath [rep t] [v, Lit (LitString (show cname)), Lit (LitString (show (getName fname)))]), Var x)
         _ -> return (k,v)

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
       return (compose ks, Ptr (ACon (dataInfoName info) vargs) (OpenCon cname vargs (prodVal vs)))

recordOpenSig :: DataInfo -> Name -> Type -> E ()
recordOpenSig info cname scheme
  = do let tvs = [typevarId tv | tv <- dataInfoParams info, tvarStar tv]
       fields <- schemeFields (map AVar tvs) scheme
       recordSig cname (SigCon tvs (prodV fields) (dataInfoName info))

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
       shapes <- conShapes info vargs
       let cons = dataInfoConstrs info
       body <- caseChain fresh shapes z (\i y -> conBranch vargs (cons !! i) (Left y) (findBranch (cons !! i) brs))
       return (Deref Owned v p (Unroll Owned p z body))

elabValueCase :: DataInfo -> [AType] -> VVal -> [C.Branch] -> E VExpr
elabValueCase info vargs v brs
  = case dataInfoConstrs info of
      [con] -> conBranch vargs con (Right v) (findBranch con brs)
      cons  -> CaseV Owned v <$> mapM (valueAlt vargs brs) cons

valueAlt :: [AType] -> [C.Branch] -> ConInfo -> E (Name,VExpr)
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

openAlt :: DataInfo -> [AType] -> (ConInfo,C.Branch) -> E (Name,Name,VExpr)
openAlt info vargs (con,br@(C.Branch [pat] _))
  = do recordOpenSig info (conInfoName con) (conInfoType con)
       x <- fresh "o"
       fields <- fieldTypes vargs con
       body <- withLocals (patBinders pat) (branchBody br)
       k <- destructure (zip (map subBinder (C.patConPatterns pat)) fields) (Var x)
       return (conInfoName con, x, k body)
openAlt _ _ _ = failE "unexpected open branch after matching"

findBranch :: ConInfo -> [C.Branch] -> Maybe C.Branch
findBranch con brs
  = case [b | b@(C.Branch [C.PatCon c _ _ _ _ _ _ _] _) <- brs, getName c == conInfoName con] of
      (b:_) -> Just b
      []    -> case [b | b@(C.Branch [C.PatWild] _) <- brs] of
                 (b:_) -> Just b
                 [] | conInfoIsLazy con -> Just (C.Branch [C.PatWild] [C.Guard C.exprTrue (C.Var (TName nameUnreachable (typeOf (head brs))) C.InfoNone)])
                    | otherwise -> Nothing

conBranch :: [AType] -> ConInfo -> Either Name VVal -> Maybe C.Branch -> E VExpr
conBranch _ con _ Nothing = failE ("missing branch for " ++ show (conInfoName con))
conBranch vargs con y (Just br@(C.Branch [pat] _))
  = do body <- withTVars (patExistIds pat) (withLocals (patBinders pat) (branchBody br))
       case pat of
         C.PatCon _ subs _ _ exists _ _ _ | not (null subs) ->
           do fields <- fieldTypes vargs con
              let exIds = [typevarId tv | tv <- exists, tvarStar tv]
                  exSub = M.fromList (zip (conExists con) (map AVar exIds))
              (k1,payload) <- openCon y (conExists con) exIds
              k2 <- destructure (zip (map subBinder subs) (map (subst exSub) fields)) payload
              return (k1 (k2 body))
         _ -> return body
conBranch _ _ _ (Just _) = failE "unexpected branch after matching"

openCon :: Either Name VVal -> [TVar] -> [TVar] -> E (K,VVal)
openCon y exs exIds
  = do (k1,p) <- either unboxK (return . (,) id) y
       (k2,u) <- if null exs then return (id,p) else unpackK p exIds
       return (k1 . k2, u)

unboxK :: Name -> E (K,VVal)
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

destructure :: [(Maybe TName,VType)] -> VVal -> E K
destructure [(x,s)] p = bindField x s p
destructure ((x,s):rest) p
  = do y <- fresh "f"
       r <- fresh "q"
       k1 <- bindField x s (Var y)
       k2 <- destructure rest (Var r)
       return (Unpair Owned p y r . k1 . k2)
destructure [] _ = return id

bindField :: Maybe TName -> VType -> VVal -> E K
bindField Nothing _ _ = return id
bindField (Just (TName x tp)) s v
  = do t <- vt tp
       (k,w) <- coerce s t v
       return (k . Let x t (Ret w))
