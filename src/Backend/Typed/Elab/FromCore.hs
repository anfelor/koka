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
import Data.List( find, sortOn, partition )
import Data.Maybe( isJust, isNothing, listToMaybe )
import Control.Monad( foldM, unless )
import Control.Monad.Reader( local )
import Common.Name
import Common.NamePrim( nameInt32, nameInternalInt32, nameInt64, nameSSizeT, nameInternalSSizeT, nameIntPtrT, nameByte, nameCoreHnd, nameFieldAddrOf, nameCCtxHoleCreate, nameCCtxCreate, nameCCtxExtend, nameCCtxApply, nameCCtxEmpty, nameCCtxCompose, nameCCtxComposeExtend
                      , nameYielding, nameTrue, nameFalse, nameEffectOpen, nameLazyMemoize, nameLazyMemoizeTarget )
import Common.Syntax( isDefFun, ParamInfo(..) )
import qualified Common.Syntax as Syntax
import Kind.Newtypes
import Type.Type
import qualified Core.Core as C
import Core.Core( TName(..), typeOf )
import qualified Core.CoreVar as CV
import Core.Pretty()
import qualified Type.TypeVar as TV
import Lidar.Syntax
import Backend.Typed.LidarName( toLidar )
import qualified Lidar.Name as L
import Lidar.Build( K, compose, prodVal, padFields )
import Lidar.Traversal( child )
import Backend.Typed.Elab.Types( typeDefs )
import Backend.Typed.Elab.TypeInfo
import Lidar.Types
import Lidar.Elab.TypeMatch( match )
import Lidar.Elab.Representation
import Backend.Typed.Elab.Monad
import Backend.Typed.Elab.Coerce
import Backend.Typed.Elab.Lazy( whnfTests )
import Backend.Typed.Elab.Common( isValue, identityCast, isPrim, linearContexts, isLinearContextPrim, testsYield, nameUnreachable, nameYieldingNonFinal, isJoinName )
import Lidar.Pretty( ppr )

-- programs

elabProgram :: Newtypes -> Foreign -> [C.Core] -> C.Core -> (Program,[String],[String])
elabProgram nt ffi imports core
  = let defs    = map closeDef (filter (not . isLeftOut) (C.flattenDefGroups (C.coreProgDefs core)))
        externs = externsOf (core:imports)
        exts    = M.keysSet externs
        isigs   = M.fromList [(n,withModes modes sig) | (n,(tp,isFun,modes)) <- M.toList (importSigs (core:imports)), Right sig <- [typeSig nt (S.member n exts) n tp isFun]]
        (tdefs,tdefErrs) = typeDefs nt
        env0    = Env nt tdefs S.empty S.empty isigs M.empty S.empty M.empty VUnit M.empty exts False
        run (sigs,ds,errs,notes) def
          = let label msg = show (C.defName def) ++ ": " ++ msg
            in case runE (elabDef (inlineOf def) def) env0{ envTrusted = C.defName def `elem` trustedNulls } (St 0 sigs [] Nothing) of
                 Right ((d,sig),st) -> (M.insert (C.defName def) sig (stSigs st), ds ++ [d], errs, notes ++ map label (stNotes st))
                 Left err -> (sigs, ds, errs ++ [label err], notes)
        (sigs,ds,errs,notes) = foldl run (M.empty,[],tdefErrs,[]) defs
        -- Koka's annotation, with the small functions `inline`: as the C backend, which defines
        -- them in the header (`Backend.C.FromCore.genTopGroup`)
        small = S.fromList [C.defName d | C.DefNonRec d <- C.coreProgDefs core, C.isInlineable 5 d]
        inlineOf d | C.defInline d == Syntax.InlineAuto && S.member (C.defName d) small = InlineAlways
                   | otherwise = elabInline (C.defInline d)
    in (Program (toLidar (C.coreProgName core)) tdefs (M.mapKeys toLidar sigs) (M.mapKeys toLidar externs) ffi ds, errs, notes)

elabInline :: Syntax.DefInline -> DefInline
elabInline inl
  = case inl of
      Syntax.InlineNever  -> InlineNever
      Syntax.InlineAlways -> InlineAlways
      Syntax.InlineAuto   -> InlineAuto

-- The definitions that use a dummy as a value: `protect-prompt` puts its result `res`, which
-- is a dummy after `yield-capture` cleared the flag of a final yield, into `Finalize(res)` to
-- run the finalizers (see "What stays trusted" in `Plan/ORNULL-KCTX-PLAN.md`).
trustedNulls :: [Name]
trustedNulls = [hndName "protect-prompt"]

hndName :: String -> Name
hndName s = qualify nameCoreHnd (newName s)

-- the externals of a module and its imports
externsOf :: [C.Core] -> M.Map Name Extern
externsOf cores
  = M.fromList [(C.externalName x, Extern (C.externalFormat x) [(toLidar n,kType t) | (n,t) <- ps] (kType r))
               | c <- cores, x@(C.External{}) <- C.coreProgExternals c, let (ps,r) = kokaFunType (C.externalType x)]
  where
    kokaFunType tp = case tp of
                       TForall _ t -> kokaFunType t
                       TSyn _ _ t -> kokaFunType t
                       TFun ps _ r -> (ps,r)
                       _ -> ([],tp)

-- Koka leaves the type variables that nothing constrains free: they become `any`
closeDef :: C.Def -> C.Def
closeDef def = TV.subNew [(tv,typeAny) | tv <- TV.tvsList (TV.ftv def), tvarStar tv] TV.|-> def

-- Koka's accessors of the fields of its abstract `cctx` would expose the hole. A context is
-- abstract in the IR, so they are left out. So is the definition of `@open`, declared at
-- `a -> e2 b`: it is only applied, and its applications are elaborated as their argument
-- (`identityCast`).
isLeftOut :: C.Def -> Bool
isLeftOut def = C.defName def `elem` (nameEffectOpen : [newLocallyQualified "std/core/types" "cctx" f | f <- ["res","holeptr"]])

-- `inl`: whether a function is inlined
elabDef :: DefInline -> C.Def -> E (Def,Sig)
elabDef inl def
  = do (d,sig) <- case splitLam (C.defExpr def) of
                    Just (_,pars,body) | isDefFun (C.defSort def) -> elabFunDef inl def pars body
                    Nothing | isDefFun (C.defSort def) -> failE "function definition is not a lambda"
                    _ -> elabValDef def
       body <- whnfTests (defBody d)
       return (d{ defBody = body },sig)

elabFunDef :: DefInline -> C.Def -> [TName] -> C.Expr -> E (Def,Sig)
elabFunDef inl def pars body
  = do (tvs,args,res) <- funSig (C.defName def) (typeOf (C.defExpr def))
       (k,token) <- tokenBinder args
       body' <- withTVars tvs (withTypedLocals [(getName p,t) | (p,(_,t)) <- zip pars args] (tokenIn token (elabExprAt res body)))
       let params = withParamModes (defModes def) args
           args' = [(rootOf (getName p),m,t) | (p,(m,t)) <- zip pars params] ++ k
       return (DefFun (toLidar (C.defName def)) tvs args' Owned res body' inl, SigFun tvs params Owned res)

-- the token parameter of a function with the parameters `ps`, if it has one, and the token in
-- its body
tokenBinder :: [(Mode,VType)] -> E ([(Path,Mode,VType)],Maybe Path)
tokenBinder ps
  | snd (tokenParam ps) = do k <- fresh "k"
                             return ([(k,Owned,VToken)], Just k)
  | otherwise = return ([], Nothing)

elabValDef :: C.Def -> E (Def,Sig)
elabValDef def
  = do e <- env
       (tvs,t) <- tr (elabScheme (envNT e) (typeOf (C.defExpr def)))
       body <- withTVars tvs (tokenIn Nothing (elabExprAt t (stripTypeLam (C.defExpr def))))
       return (DefVal (toLidar (C.defName def)) tvs t body, SigVal tvs t)

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
      SigFun tvs ps q r -> SigFun tvs (withParamModes modes ps) q r
      _ -> sig

withParamModes :: [Mode] -> [(Mode,VType)] -> [(Mode,VType)]
withParamModes modes ps = [(m,t) | ((_,t),m) <- zip ps (modes ++ repeat Owned)]

typeSig :: Newtypes -> Bool -> Name -> Type -> Bool -> Tr Sig
typeSig nt isExt n tp isFun
  | isFun     = (\(tvs,args,res) -> SigFun tvs args Owned res) <$> funSigOf nt isExt n tp
  | otherwise = uncurry SigVal <$> elabScheme nt tp

-- The IR type of the function `n` (an external if `isExt`) of the Koka type `tp`:
--
-- * The tests of the yield flag, `yielding()` and `yielding-non-final()`, take the token like
--   an effectful external (Koka types them total), so that they are ordered after the calls
--   whose yields they test.
-- * Only the yield primitives among the externals return the dummy of a yield: the result of
--   any other external is not `V?`, so its uses need no test for null.
-- * The prompt functions of `std/core/hnd` take the result of an action, which may be the
--   dummy of a yield that they test for, at `V?` (`nullParams`).
funTypeOf :: Newtypes -> Bool -> Name -> Type -> Tr AType
funTypeOf nt isExt n tp = adjust <$> elabFunType nt tp
  where
    adjust a = case a of
                 AForall tvs b -> AForall tvs (adjust b)
                 AFun ps r -> let (ps',r') = if isFlagTest n && not (snd (tokenParam ps)) then (ps ++ [(Owned,VToken)], withToken r) else (ps,r)
                              in AFun [(m, if i `elem` nullParams n then orNull t else t) | (i,(m,t)) <- zip [0 :: Int ..] ps']
                                      (if isExt && n `notElem` yieldPrims then noNull r' else r')
                 _ -> a
    noNull r = maybe (unNull r) (withToken . unNull) (unToken r)

isFlagTest :: Name -> Bool
isFlagTest n = n `elem` [nameYielding, nameYieldingNonFinal]

-- the externals that return the dummy of a yield: they always yield
yieldPrims :: [Name]
yieldPrims = map hndName ["yield-extend", "yield-cont", "keep-yielding-final", "yield-to-prim", "yield-to-final", "unsafe-reyield-prim"]

-- the positions of the parameters of a prompt function that take the result of an action
nullParams :: Name -> [Int]
nullParams n = M.findWithDefault [] n (M.fromList [ (hndName "prompt", [5])                -- result
                                                  , (hndName "prompt-local-var", [1])      -- res
                                                  , (hndName "finally-prompt", [1])        -- res
                                                  , (hndName "initially-prompt", [1])      -- res
                                                  , (hndName "protect-prompt", [1])        -- res
                                                  , (hndName "yield-bind", [0])            -- x
                                                  , (hndName "yield-bind2", [0]) ])        -- x

funSigOf :: Newtypes -> Bool -> Name -> Type -> Tr ([TVar],[(Mode,VType)],VType)
funSigOf nt isExt n tp
  = do a <- funTypeOf nt isExt n tp
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

funSig :: Name -> Type -> E ([TVar],[(Mode,VType)],VType)
funSig n tp
  = do e <- env
       tr (funSigOf (envNT e) False n tp)

-- expressions

-- An expression at the type `t`, which its expressions in tail position take (`result`): the
-- result of each is coerced there, so that a result that may be the dummy of a yield (`W?`)
-- is tested where it is coerced.
elabExprAt :: VType -> C.Expr -> E VExpr
elabExprAt t e = withResult t (elabTail e)

-- an expression in tail position, at the type `result` (including the bodies of join points)
elabTail :: C.Expr -> E VExpr
elabTail expr
  = case expr of
      C.Let [] body -> elabTail body
      C.Let (C.DefNonRec (C.Def{ C.defName = j }) : _) _ | isJoinName j, testsYield expr
        -> region (elabJoin expr)
      _ -> elabJoin expr

-- In code without a token, a test for a yield is a `[total]` region (`region`), and so is a
-- scope of join points that contains one, as a region cannot jump to a join point outside.
elabJoin :: C.Expr -> E VExpr
elabJoin expr
  = case expr of
      C.Let (C.DefNonRec (C.Def{ C.defName = j, C.defExpr = lam }) : dgs) body | isJoinName j, Just (tvs,pars,e1) <- splitLam lam
        -> do let linear = linearContexts e1
                  tvs'   = [typevarId tv | tv <- tvs, tvarStar tv]
              (k,token) <- joinToken
              (ps,e1') <- withTVars tvs' $
                          do ps <- mapM (\p -> (\t -> (rootOf (getName p),paramMode Own (S.member (getName p) linear),t)) <$> vt (tnameType p)) pars
                             (,) (ps ++ k) <$> withTypedLocals [(getName p,t) | (p,(_,_,t)) <- zip pars ps] (tokenIn token (elabTail e1))
              Join (toLidar j) tvs' ps e1' <$> elabTail (C.Let dgs body)
      C.App f args | (Just (TName j tp,_),tys) <- splitTypeApp f, isJoinName j, Just (pars,_,_) <- splitFunType (typeOf f)
        -> do tys' <- instArgs tp tys
              (ks,vs) <- unzip <$> mapM (\((_,ptp),arg) -> do t <- vt ptp
                                                              elabValAt t arg) (zip pars args)
              (_,token) <- joinToken
              (kt,tv) <- takeTokenIf (isJust token)
              return (compose ks (kt (Jump (toLidar j) tys' (vs ++ tv))))
      -- `memoize-target(x, size, scan-size)` only informs Koka's C backend
      C.Let (C.DefNonRec (C.Def{ C.defExpr = C.App f _ }) : dgs) body | isPrim nameLazyMemoizeTarget f
        -> elabTail (C.Let dgs body)
      C.Let (C.DefNonRec def : dgs) body
        -> elabLet def (C.Let dgs body)
      C.Let (C.DefRec defs : _) _
        -> failE ("local recursive definition: " ++ show (map C.defName defs))
      C.TypeLam tvs e | not (any tvarStar tvs) -> elabTail e
      C.TypeLam tvs e | not (isValue expr) -> elabGen [typevarId tv | tv <- tvs, tvarStar tv] e (typeOf expr) >>= atResult (typeOf expr)
      _ | Just (e2,e3) <- yieldTest expr
        -> region $ do (kt,k) <- takeToken
                       kt <$> testYield k (elabTail e3) (elabTail e2)
      C.Case [scrut] brs -> elabCase scrut brs
      C.Var (TName x _) _ | x == nameUnreachable -> Unreachable <$> result
      C.Case _ _ -> failE "case with multiple scrutinees after matching"
      -- an identity external changes only effects: the tails of its argument are coerced to `result`
      _ | Just g <- identityCast expr, not (isValue g) -> elabTail g
      C.App f args | not (isConApp f), isNothing (identityCast expr), isNothing (rawLiteral expr) -> elabApp f args (typeOf expr)
      _ -> do (k,v,t) <- elabValT expr
              k <$> retAt t v

-- In a token-threaded expression, every join point takes the token, as the last parameter
-- (and its jumps pass it). The binder and the token in the body of a join point.
joinToken :: E ([(Path,Mode,VType)],Maybe Path)
joinToken = do r <- result
               if isJust (unToken r) then tokenBinder [(Owned,VToken)] else return ([],Nothing)

-- a value of type `t` at the type `result`, with the current token if that is token-threaded
retAt :: VType -> VVal -> E VExpr
retAt t v = do r <- result
               case unToken r of
                 Just r0 -> do (k,w) <- coerce t r0 v
                               (kt,tok) <- takeToken
                               return (k (kt (Ret (Tuple [w,tok]))))
                 Nothing -> do (k,w) <- coerce t r v
                               return (k (Ret w))

-- an expression of the Koka type `tp` at the type `result`
atResult :: Type -> VExpr -> E VExpr
atResult tp e = do t <- vt tp
                   r <- result
                   coerceExpr t r e

-- Koka's test for a yield, `match yielding() { True -> e₃; False -> e₂ }`: `e₂` and `e₃`. It is
-- an `[if-yielding]` on the current token (`testYield`).
yieldTest :: C.Expr -> Maybe (C.Expr,C.Expr)
yieldTest expr
  = case expr of
      C.Let [] e -> yieldTest e
      C.Case [C.App f []] brs | isPrim nameYielding f -> (,) <$> branch nameFalse brs <*> branch nameTrue brs
      _ -> Nothing
  where
    branch c brs = listToMaybe ([e | C.Branch [C.PatCon pc _ _ _ _ _ _ _] [C.Guard _ e] <- brs, getName pc == c]
                                ++ [e | C.Branch [C.PatWild] [C.Guard _ e] <- brs])

-- The parts of a context under construction are not bound: their uses become parts of the
-- `ctx` value (see `elabCtx`). Koka's test for a yield after `val x = e₁` (whose yielding
-- branch does not use `x`) is an `[if-yielding]` that extracts `x` (`letYield`), if `e₁` may be
-- the dummy; otherwise it tests a yield of an earlier call (as in `val y = f(); evv-set(w);
-- if yielding() …`), and is elaborated where it occurs (`yieldTest`).
elabLet :: C.Def -> C.Expr -> E VExpr
elabLet def body
  = do en <- env
       let x = C.defName def
       if isFieldAddr en (C.defExpr def) then withHole x Nothing (elabTail body)
       else if hasHole en (C.defExpr def)
         then do (k,v) <- elabVal (C.defExpr def)
                 k <$> withHole x (Just v) (elabTail body)
       -- Match binds a pattern variable where the source first needs it (`Match.guardChain`):
       -- the field is read there, once. Its binder stays a child of the box (`[fst]`, `[snd]`); a `let`
       -- would bind an owned root and acquire a reference.
       else if fieldAlias en (C.defExpr def)
         then do t <- vt (C.defType def)
                 (k,v) <- elabValAt t (C.defExpr def)
                 k <$> withFields [(x,(id,v))] (elabTail body)
         else do t <- vt (C.defType def)
                 dummy <- mayBeDummy (C.defExpr def)
                 case yieldTest body of
                   Just (e2,e3) | dummy, not (S.member x (S.map getName (CV.fv e3)))
                     -> region (letYield def t e2 e3)
                   _ -> do (k,t') <- bindExpr (rootOf x) t (C.defExpr def)
                           k <$> withTypedLocals [(x,t')] (elabTail body)
  where
    fieldAlias en (C.Var (TName y _) _) = M.member y (envFields en)
    fieldAlias _ _ = False

-- `val x = e₁` followed by a test for a yield: the result `r : t? ⊗ KCtx` of `e₁` is tested on
-- its token `r.1` (`[if-yielding]`), and the non-yielding branch extracts `x` from `r.0`
-- (`[is-null]`). Each branch continues with its new token.
letYield :: C.Def -> VType -> C.Expr -> C.Expr -> E VExpr
letYield def t e2 e3
  = do let u = withToken (orNull t)
           x = C.defName def
       e1' <- elabExprAt u (C.defExpr def)
       r <- fresh "r"
       r0 <- fresh "r"
       k <- fresh "k"
       w <- result
       test <- testYield (Var k) (elabTail e3)
                 (IsNull (Var r0) (Unreachable w) . (,) (rootOf x) <$> withTypedLocals [(x,t)] (elabTail e2))
       return (Let r u e1' (Proj (Var r) 0 r0 (Proj (Var r) 1 k test)))

-- `[if-yielding]` on the token `k`, with the yielding branch `m3` and the other branch `m2`,
-- each of which continues with its new token
testYield :: VVal -> E VExpr -> E VExpr -> E VExpr
testYield k m3 m2
  = IfYielding k <$> branch m3 <*> branch m2
  where
    branch m = do k' <- fresh "k"
                  e <- tokenIn (Just k') m
                  return (k',e)

-- `let x : t = e in □`, and the type of x. In a token-threaded expression, an `e` that calls
-- something that takes a token (`usesToken`) is elaborated at `t ⊗ KCtx`, whose token is the
-- next one; any other `e` does not see the token. In code without a token, such an `e` is one
-- `[total]` region (`region`). An `e` that may be the dummy of a yield,
-- which Koka does not test (`mayBeDummy`), is elaborated at `t?`: its uses test it for null,
-- unless they pass it on (to a prompt function of `std/core/hnd`).
bindExpr :: Path -> VType -> C.Expr -> E (K,VType)
bindExpr x t0 expr
  = do token <- currentToken
       dummy <- mayBeDummy expr
       let t = if dummy then orNull t0 else t0
       en <- env
       if isJust token && usesToken en expr
         then do let tt = withToken t
                 e <- elabExprAt tt expr
                 p <- fresh "p"
                 k <- fresh "k"
                 setToken (Just k)
                 return (Let p tt e . Proj (Var p) 0 x . Proj (Var p) 1 k, t)
         else do e <- tokenIn Nothing (withResult t ((if usesToken en expr then region else id) (elabTail expr)))
                 return (Let x t e, t)

-- Whether an expression may be the dummy of a yield, as one of its tails calls a function
-- whose result may be (`V?`), overapproximated as the type of the function is generic.
mayBeDummy :: C.Expr -> E Bool
mayBeDummy expr
  = case expr of
      C.App f args
        | Just g <- identityCast expr, not (isValue g) -> mayBeDummy g
        | Just g <- identityCast f -> mayBeDummy (C.App g args)
        | isConApp f -> return False
        | (Just (TName j _,_),_) <- splitTypeApp f, isJoinName j -> return False
        | any (`isPrim` f) [nameCCtxEmpty, nameCCtxCreate, nameCCtxExtend, nameCCtxApply, nameCCtxCompose] -> return False
        | otherwise -> do e <- env
                          case splitTypeApp f of
                            (Just (TName g _,_),_)
                              | S.member g (envLocals e), Just t <- M.lookup g (envBinders e) -> return (resultYields t)
                              | not (S.member g (envLocals e)), Just sig <- M.lookup g (envSigs e)
                              -> return (case sig of
                                           SigFun _ _ _ r -> yields r
                                           SigVal _ t -> resultYields t
                                           _ -> False)
                            _ -> resultYields <$> vt (typeOf f)   -- also a local bound in the expression
      C.Let dgs body -> or <$> mapM mayBeDummy (body : [e | d <- C.flattenDefGroups dgs, isJoinName (C.defName d), Just (_,_,e) <- [splitLam (C.defExpr d)]])
      C.Case _ brs -> or <$> mapM mayBeDummy [C.guardExpr g | br <- brs, g <- C.branchGuards br]
      C.TypeLam _ e -> mayBeDummy e
      _ -> return False
  where
    resultYields t = case t of
                       VPtr a -> resultA a
                       _ -> False
    resultA a = case a of
                  AForall _ b -> resultA b
                  AFun _ r -> yields r
                  _ -> False

-- Whether an expression (outside of its lambdas, but including the bodies of its join points,
-- which `matchCore` types as total) calls a function that takes a token, overapproximated: a
-- function is also taken at its generic type (an effect-polymorphic function at a total
-- instance takes a token), and one under an identity cast (`.open`, `unsafe-total`) at both
-- of its types, as elaboration calls it at its own (`elabApp`), as is a function returned by
-- a call of a global (`ownResult`). The tests of the yield flag
-- take a token too (`funTypeOf`), as does a function whose elaborated type takes one although
-- its Koka type is total here: a global value (a handler at `∀e. … -> e r`, used at a total
-- effect) or a local bound at such a type.
usesToken :: Env -> C.Expr -> Bool
usesToken en expr
  = case expr of
      C.App f args -> any calls (typeOf f : generic f ++ maybe [] (\g -> typeOf g : generic g) (identityCast f) ++ genericResult f) || any (`isPrim` f) [nameYielding, nameYieldingNonFinal]
                      || any elaborated (f : maybe [] (: []) (identityCast f)) || any (usesToken en) (f : args)
      C.TypeApp e _ -> usesToken en e
      C.TypeLam _ e -> usesToken en e
      C.Let dgs e -> usesToken en e || any bound (C.flattenDefGroups dgs)
      C.Case scs brs -> any (usesToken en) scs || or [usesToken en (C.guardTest g) || usesToken en (C.guardExpr g) | br <- brs, g <- C.branchGuards br]
      _ -> False
  where
    calls tp = case expandSyn tp of
                 TForall _ t -> calls t
                 TFun _ eff _ -> needsToken eff
                 _ -> False
    generic f = case splitTypeApp f of
                  (Just (TName _ gtp,_),_) -> [gtp]
                  _ -> []
    -- a function returned by a call of a global is called at its generic type (`ownResult`)
    genericResult f = case f of
                        C.App g _ -> [r | gtp <- generic g, Just r <- [resultOf gtp]]
                        _ -> []
    resultOf tp = case expandSyn tp of
                    TForall _ t -> resultOf t
                    TFun _ _ r -> Just r
                    _ -> Nothing
    bound d = case splitLam (C.defExpr d) of
                Just (_,_,body) | isJoinName (C.defName d) -> usesToken en body
                _ -> usesToken en (C.defExpr d)
    elaborated f = case splitTypeApp f of
                     (Just (TName g _,_),_)
                       | S.member g (envLocals en) -> maybe False takes (M.lookup g (envBinders en))
                       | otherwise -> case M.lookup g (envSigs en) of
                                        Just (SigFun _ ps _ _) -> snd (tokenParam ps)
                                        Just (SigVal _ t) -> takes t
                                        _ -> False
                     _ -> False
    takes t = case t of
                VPtr a -> takesA a
                _ -> False
    takesA a = case a of
                 AForall _ b -> takesA b
                 AFun ps _ -> snd (tokenParam ps)
                 _ -> False

-- A type abstraction over an expression that is not a value. Its result may be the dummy of a
-- yield (`tlam-yield1`), which has no type `(∀ā. A)*?`: it is passed on by a cast (`envTrusted`).
elabGen :: [TVar] -> C.Expr -> Type -> E VExpr
elabGen tvs e tp
  = do target <- vt tp
       case target of
         VPtr (AForall tvs' a)
           -> do let a' = inst tvs (map AVar tvs') a
                 body <- withTVars tvs' (tokenIn Nothing (local (\en -> en{ envTrusted = True }) (elabExprAt (VPtr a') e)))
                 return (Gen tvs' body)
         _ -> failE ("type abstraction at the monomorphic type " ++ ppr target)

isConApp :: C.Expr -> Bool
isConApp (C.Con _ _)     = True
isConApp (C.TypeApp e _) = isConApp e
isConApp _               = False

-- applications

-- An application at the type `result`. A function under an identity external (such as
-- `.open`) is called as it is: its result is coerced to `result`, and tested for a yield
-- where `result` may yield, as Koka's monadic translation decided from the identity
-- external's type.
elabApp :: C.Expr -> [C.Expr] -> Type -> E VExpr
elabApp f args resTp
  | Just g <- identityCast f
  = elabApp g args resTp
  | isPrim nameCCtxEmpty f
  = do t <- vt resTp
       b <- holeType t
       retAt t (Context b Hole)
  | isPrim nameCCtxCreate f, [res,addr] <- args
  = elabCtx Nothing res addr resTp >>= atResult resTp
  | isPrim nameCCtxExtend f, [acc,res,addr] <- args
  = elabCtx (Just (isLinearContextPrim f, acc)) res addr resTp >>= atResult resTp
  | isPrim nameCCtxApply f, [acc,_] <- args
  = do t <- vt (typeOf acc)
       (a,b) <- case t of
                  VCtx _ a b -> return (a,b)
                  _ -> failE ("plugging a non-context: " ++ ppr t)
       let shared = not (isLinearContextPrim f)
       callWith coerceExpr (\[c,v] -> do (k,c') <- ctxCopy shared t c
                                         return (k (Plug c' v))) [t, VPtr b] (VPtr a) args
  | isPrim nameCCtxCompose f
  = do t <- vt resTp
       ts@[tc,td] <- mapM (vt . typeOf) args
       callWith coerceExpr (\[c,d] -> do (kc,c') <- ctxCopy True tc c
                                         (kd,d') <- ctxCopy True td d
                                         return (kc (kd (Append c' d')))) ts t args
  | any (`isPrim` f) [nameCCtxHoleCreate, nameFieldAddrOf]
  = failE "a hole outside of a context"
  -- `memoize(x, v)` writes an indirection to `v` over the lazy value `x` under evaluation
  -- (`[memoize-ptr]`; `Passes.Lazy` makes `x` a cell)
  | isPrim nameLazyMemoize f, [x,v] <- args
  = do (info,_) <- dataArgs (typeOf x)
       ind <- maybe (failE ("memoizing a value that is not lazy: " ++ show (typeOf x))) return (lazyIndirectIndex info)
       t <- vt (typeOf x)
       (kx,x') <- elabValAt t x
       (kv,v') <- elabValAt t v
       atResult resTp (kx (kv (Memoize x' Delay ind v')))
  -- extends with the hole of a context that may be shared, without copying its path
  | isPrim nameCCtxComposeExtend f
  = failE "unsupported context primitive: @cctx-compose-extend"
elabApp f args resTp
  = do mbsig <- globalOf f
       case mbsig of
         Just (g,sig@(SigFun _ ps _ _),gtp,tys)
           -> do (tysD,params,res) <- instFun g sig gtp tys
                 e <- env
                 let copies = [m == Unique && captured e arg | ((m,_),arg) <- zip ps args] ++ repeat False
                 callWith (coerceCall g)
                          (\vs -> do (ks,vs') <- unzip <$> sequence (zipWith3 ctxCopy copies params vs)
                                     return (compose ks (Call (toLidar g) tysD vs'))) params res args
         _ -> do t <- vt (typeOf f)
                 own <- ownResult f t
                 (k1,fv,u) <- case own of
                                Just r -> do x <- fresh "a"
                                             (k,r') <- bindExpr x r f
                                             return (k, Var x, r')
                                Nothing -> elabValT f
                 case u of
                   -- a function value that would be wrapped (`wrapped`) is called at its own
                   -- type, and its result is tested for null by `callWith`: no wrapper is allocated
                   VPtr (AFun params res) | wrapped u t
                     -> k1 <$> callWith coerceExpr (applyFun (AFun params res) fv) (map snd params) res args
                   _ -> do (k2,fv') <- coerce u t fv
                           (params,res) <- funType f
                           body <- callWith coerceExpr (applyFun (AFun params res) fv') (map snd params) res args
                           return (k1 (k2 body))

-- The result type of a call `expr` of a global function at its own instance, where it is a
-- function that would be wrapped at its Koka type `t` (`wrapped`), as for an effect-polymorphic
-- function returned at a total effect (`unsafe-no-state-div-cast` in `force`)
ownResult :: C.Expr -> VType -> E (Maybe VType)
ownResult expr t
  = case (expr,t) of
      (C.App g args, VPtr (AFun _ _))
        | not (isConApp g), isNothing (identityCast expr), isNothing (identityCast g), not (isJoin g)
        -> do mbsig <- globalOf g
              case mbsig of
                Just (n,sig@SigFun{},gtp,tys) | length args == sigArity sig
                  -> do (_,_,res) <- instFun n sig gtp tys
                        return (if wrapped res t then Just res else Nothing)
                _ -> return Nothing
      _ -> return Nothing
  where
    isJoin g = case splitTypeApp g of
                 (Just (TName j _,_),_) -> isJoinName j
                 _ -> False
    sigArity (SigFun _ ps _ _) = length (fst (tokenParam ps))
    sigArity _ = -1

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
                               tr (typeSig (envNT e) (S.member g (envExterns e)) g gtp (isFunInfo info))
       recordSig g sig
       return sig

isFunInfo :: C.VarInfo -> Bool
isFunInfo (C.InfoArity _ _)  = True
isFunInfo (C.InfoExternal _) = True
isFunInfo _                  = False

instFun :: Name -> Sig -> Type -> [Type] -> E ([AType],[VType],VType)
instFun g (SigFun tvs params _ res) gtp tys
  = do e <- env
       tys' <- instArgs gtp tys
       useA <- tr (funTypeOf (envNT e) (S.member g (envExterns e)) g gtp)
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

-- A call of the arguments `args` at the types `params`, whose result of type `res` is
-- coerced to the type `result` by `coerceRes` (usually `coerceExpr`, which tests a result that
-- may be the dummy of a yield where Koka does not; see `coerceCall`).
-- In code without a token, a call that takes one is a `[total]` region.
callWith :: (VType -> VType -> VExpr -> E VExpr) -> ([VVal] -> E VExpr) -> [VType] -> VType -> [C.Expr] -> E VExpr
callWith coerceRes call params res args
  = (if token then region else id) $
    do (ks,vs) <- unzip <$> mapM (\(p,arg) -> elabValAt p arg) (zip (map snd params0) args)
       (kt,tv) <- takeTokenIf token
       expect <- result
       app <- call (vs ++ tv)
       compose ks . kt <$> coerceRes res expect app
  where
    (params0,token) = tokenParam [((),p) | p <- params]

-- The coercion of the result of a call of the global `g`. A yield primitive always yields, so
-- a test of its result does not continue (`coerceYielded`). The result of a final yield is
-- always the dummy: where Koka types it at a total type (`prompt` resumes with
-- `{ yield-to-final(m, …) }`), it is cast (`trusting`).
coerceCall :: Name -> VType -> VType -> VExpr -> E VExpr
coerceCall g = (if g == hndName "yield-to-final" then trusting else id) (if g `elem` yieldPrims then coerceYielded else coerceExpr)

-- a coercion that trusts Koka's typing (`envTrusted`)
trusting :: (VType -> VType -> VExpr -> E VExpr) -> VType -> VType -> VExpr -> E VExpr
trusting c from to e = local (\en -> en{ envTrusted = True }) (c from to e)

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
elabValAt expect@(VPtr a@(AFun qs _)) (C.Lam pars _ body) | length (fst (tokenParam qs)) == length pars
  = do (k,lam) <- captureFields body (elabLam expect pars body)
       return (k, Ptr a lam)
elabValAt expect expr
  = do (k1,v,t) <- elabValT expr
       (k2,v') <- coerce t expect v
       return (k1 . k2, v')

-- a value of the Koka type `t` of an expression, at `t`
elabVal :: C.Expr -> E (K,VVal)
elabVal expr
  = do (k1,v,u) <- elabValT expr
       t <- vt (typeOf expr)
       (k2,v') <- coerce u t v
       return (k1 . k2, v')

-- a value of an expression and its type: the Koka type `t`, or `t?` for a result that may be
-- the dummy of a yield (`bindExpr`), or a local bound to one
elabValT :: C.Expr -> E (K,VVal,VType)
elabValT expr
  = do t <- vt (typeOf expr)
       e <- env
       case elabValOf expr of
         _ | C.Var (TName x _) _ <- expr, Just bt <- M.lookup x (envBinders e), yields bt
           -> do (k,v) <- coerceInst bt (orNull t) (Var (rootOf x))
                 return (k,v,orNull t)
         Just m -> do (k,v) <- m
                      return (k,v,t)
         Nothing -> do x <- fresh "a"
                       (k,t') <- bindExpr x t expr
                       return (k, Var x, t')

-- the elaboration of an expression as a value of its Koka type, unless it is bound (`Nothing`)
elabValOf :: C.Expr -> Maybe (E (K,VVal))
elabValOf expr
  = case expr of
      C.Var (TName x tp) _ | x == nameUnreachable -> Just (unreachable tp)
      C.App f [] | isPrim nameCCtxHoleCreate f -> Just (return (id, Hole))
      C.Var (TName x tp) info -> Just (elabVar x tp info [])
      C.TypeApp (C.Var (TName x tp) info) tys -> Just (elabVar x tp info tys)
      C.Lit lit -> Just (return (id, elabLit lit))
      _ | Just l <- rawLiteral expr -> Just (return (id, Lit l))
      _ | isConApp expr -> Just $ case expandSyn (typeOf expr) of
                                    TFun pars eff _ -> etaCon expr pars eff
                                    TForall tvs _ -> generalize [typevarId tv | tv <- tvs, tvarStar tv] (elabCon expr []) (typeOf expr)
                                    _ -> elabCon expr []
      C.App f args | isConApp f -> Just (elabCon f args)
      C.TypeApp e tys
        -> Just $ do (k1,v) <- elabVal e
                     tys' <- instArgs (typeOf e) tys
                     if null tys' then return (k1,v)
                       else do a <- ptrType (typeOf e)
                               expect <- vt (typeOf expr)
                               (k2,v') <- coerceInst (VPtr (instA a tys')) expect (tapp v tys')
                               return (k1 . k2,v')
      C.TypeLam tvs e | not (any tvarStar tvs) -> Just (elabVal e)
      C.Lam pars _ body -> Just $ do t <- vt (typeOf expr)
                                     (k,lam) <- captureFields body (elabLam t pars body)
                                     (kg,v) <- genVal t lam
                                     return (k . kg,v)
      C.TypeLam tvs (C.Lam pars _ body)
        -> Just $ do t <- vt (typeOf expr)
                     (k,lam) <- captureFields body (withTVars (map typevarId tvs) (elabLam (stripForallV t) pars body))
                     (kg,v) <- genVal t lam
                     return (k . kg,v)
      C.TypeLam tvs e | isValue e -> Just (elabTypeLam [typevarId tv | tv <- tvs, tvarStar tv] e (typeOf expr))
      -- an identity external changes only effects: its argument, cast where it differs in `?`s and tokens
      _ | Just g <- identityCast expr, isValue g
        -> Just $ do (k1,v) <- elabVal g
                     from <- vt (typeOf g)
                     to <- vt (typeOf expr)
                     (k2,v') <- coerceInst from to v
                     return (k1 . k2,v')
      _ -> Nothing

elabTypeLam :: [TVar] -> C.Expr -> Type -> E (K,VVal)
elabTypeLam tvs e tp = generalize tvs (elabVal e) tp

-- a pointer value at its polymorphic type `tp`
generalize :: [TVar] -> E (K,VVal) -> Type -> E (K,VVal)
generalize tvs elab tp
  = do (k,v) <- withTVars tvs elab
       target <- vt tp
       (k2,v') <- genPtr target v
       return (k . k2, v')

-- the rest of an expression with `unreachable` in a value is dead
unreachable :: Type -> E (K,VVal)
unreachable tp
  = do t <- vt tp
       x <- fresh "u"
       return (Let x t (Unreachable t), Var x)

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
       ts <- mapM (vt . tnameType) pars
       (k,token) <- tokenBinder qs
       body' <- inClosure (withTypedLocals (zip (map getName pars) ts) (tokenIn token (elabExprAt res body)))
       return (Lam (ps ++ k) res (compose ks body'))
elabLam t _ _ = failE ("expecting a function type for a lambda: " ++ ppr t)

lamParam :: (TName,(Mode,VType)) -> E ((Path,Mode,VType),K)
lamParam (p,(m,q))
  = do t <- vt (tnameType p)
       if alphaEq q t then return ((rootOf (getName p),m,q),id)
         else do y <- fresh "a"
                 (k,v) <- coerce q t (Var y)
                 return ((y,m,q), k . Let (rootOf (getName p)) t (Ret v))

stripForallV :: VType -> VType
stripForallV (VPtr (AForall _ a)) = VPtr a
stripForallV t = t

-- the conversion of an integer literal to a raw type, in its range, is a raw literal
rawLiteral :: C.Expr -> Maybe Lit
rawLiteral expr
  = case expr of
      C.App f [C.Lit (C.LitInt i)]
        | t:_ <- [t | (n,t) <- conversions, isPrim n f], let (lo,hi) = intRange t, lo <= i, i <= hi
        -> Just (LitInt t i)
      _ -> Nothing
  where
    conversions = [(nameInt32,int32),(nameInternalInt32,int32),(nameInt64,IntType Signed W64)
                  ,(nameSSizeT,ssize),(nameInternalSSizeT,ssize),(nameIntPtrT,IntType Signed WPtr)
                  ,(nameByte,IntType Unsigned W8)]
    int32 = IntType Signed W32
    ssize = IntType Signed WSize

elabLit :: C.Lit -> VVal
elabLit lit
  = case lit of
      C.LitInt i    -> intLit i
      C.LitFloat d  -> Lit (LitFloat d)
      C.LitChar c   -> Lit (LitChar c)
      C.LitString s -> stringLit s

-- a literal of a raw type, as a pattern of `CaseLit`
rawPattern :: C.Lit -> E Lit
rawPattern lit
  = case lit of
      C.LitFloat d -> return (LitFloat d)
      C.LitChar c  -> return (LitChar c)
      _ -> failE ("a literal pattern of a type that is not raw: " ++ show lit)

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
                 let (k,v) = M.findWithDefault (id,Var (rootOf x)) x (envFields e)
                 (ki,w) <- case (tys', M.lookup x (envBinders e)) of
                             -- a use at other effects than its binder (`() -> int` as `() -> console int`)
                             ([],Just bt) -> coerceInst bt expect v
                             _ -> instLocal v tp tys' expect
                 return (k . ki,w)
         else do sig <- globalSig x tp info
                 case sig of
                   SigFun tvs ps _ r -> do (tysD,params,res) <- instFun x sig tp tys
                                           let a = AFun [(Owned,p) | p <- params] res
                                           f <- if any ((/= Owned) . fst) ps then Ptr a <$> etaOwned x tysD params res
                                                                             else return (tapp (Ptr (forallA tvs (AFun ps r)) (Fun (toLidar x))) tysD)
                                           coerceInst (VPtr a) expect f
                   SigVal _ _     -> do (tysD,t) <- instVal x sig tp tys
                                        coerceInst t expect (Glob (toLidar x) tysD)
                   SigCon _ _ _   -> failE ("constructor used as a variable: " ++ show x)

-- closures only have owned parameters ([fun]): wrap a function that borrows (or takes a unique argument)
etaOwned :: Name -> [AType] -> [VType] -> VType -> E AVal
etaOwned x tysD params res
  = do ys <- mapM (const (fresh "e")) params
       return (Lam [(y,Owned,p) | (y,p) <- zip ys params] res (Call (toLidar x) tysD (map Var ys)))

instLocal :: VVal -> Type -> [AType] -> VType -> E (K,VVal)
instLocal v _ [] _ = return (id,v)
instLocal v tp tys' expect
  = do a <- ptrType tp
       coerceInst (VPtr (instA a tys')) expect (TyApp v tys')

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
       e <- env
       v <- conValue (envTypes e) (toLidar (dataInfoName info)) vargs idx exSub (prodVal (padFields fields vs))
       return (compose ks, v)

elabOpenCon :: DataInfo -> [AType] -> Name -> Type -> [C.Expr] -> E (K,VVal)
elabOpenCon info vargs cname scheme args
  = do recordOpenSig info cname scheme
       fields <- schemeFields vargs scheme
       (ks,vs) <- unzip <$> mapM (\(t,arg) -> elabValAt t arg) (zip fields args)
       return (compose ks, Ptr (ACon (toLidar (dataInfoName info)) vargs) (OpenCon (toLidar cname) vargs vs))

recordOpenSig :: DataInfo -> Name -> Type -> E ()
recordOpenSig info cname scheme
  = do let tvs = [typevarId tv | tv <- dataInfoParams info, tvarStar tv]
       fields <- schemeFields (map AVar tvs) scheme
       recordSig cname (SigCon tvs fields (toLidar (dataInfoName info)))

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
       case mbAcc of
         Nothing -> do (k1,v) <- elabVal res
                       return (k1 (Ret (Context b v)))
         Just (linear,acc)
           -> do (k0,c) <- elabVal acc
                 (k1,v) <- elabVal res
                 tacc <- vt (typeOf acc)
                 (kc,c') <- ctxCopy (not linear) tacc c
                 return (k0 (k1 (kc (Append c' (Context b v)))))

-- A closure (such as the continuation of an effect that may resume more than once) only owns
-- the contexts that it captures: it copies one that it passes to a unique parameter (if it is
-- shared).
captured :: Env -> C.Expr -> Bool
captured e arg
  = case arg of
      C.Var x _ -> S.member (getName x) (envCaptured e)
      _ -> False

-- a copy of a context of type `t` that may be shared, bound by a `let` (if `True`)
ctxCopy :: Bool -> VType -> VVal -> E (K,VVal)
ctxCopy True t v = do x <- fresh "c"
                      return (Let x t (CtxCopy v), Var x)
ctxCopy False _ v = return (id,v)

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

-- matching

elabCase :: C.Expr -> [C.Branch] -> E VExpr
elabCase scrut brs
  = do let scrutTp = typeOf scrut
       expect <- vt scrutTp
       (k,v) <- elabValAt expect scrut
       body <- case [p | C.Branch [p] _ <- brs] of
                 (C.PatLit _ : _) -> elabLitCase expect v brs
                 _ | all isWild [p | C.Branch [p] _ <- brs] -> branchBody (head brs)
                 _ -> elabConCase scrutTp v brs
       return (k body)

isWild :: C.Pattern -> Bool
isWild C.PatWild = True
isWild _         = False

-- the body of a branch, in tail position
branchBody :: C.Branch -> E VExpr
branchBody (C.Branch _ [C.Guard _ e]) = branch (elabTail e)
branchBody _ = failE "unexpected guards after matching"

-- A match on literals of a raw type is a `CaseLit`. One on `int` or `string` literals compares
-- the scrutinee with each pattern in turn, by a call of the type's `(==)`.
elabLitCase :: VType -> VVal -> [C.Branch] -> E VExpr
elabLitCase t v brs
  = do let pats = [(l,b) | b@(C.Branch [C.PatLit l] _) <- brs]
           def  = case [b | b@(C.Branch [C.PatWild] _) <- brs] of
                    (b:_) -> branchBody b
                    []    -> failE "literal match without default"
       case pats of
         (C.LitInt _,_) : _ -> eqChain nameIntEq pats def
         (C.LitString _,_) : _ -> eqChain nameStringEq pats def
         _ -> do alts <- mapM (\(l,b) -> (,) <$> rawPattern l <*> branchBody b) pats
                 CaseLit v alts <$> def
  where
    eqChain eq pats def
      = do sig <- do e <- env
                     maybe (failE ("no signature for " ++ show eq)) return (M.lookup eq (envSigs e))
           recordSig eq sig
           tbool <- vt typeBool
           (bind,s) <- case v of
                         Var _ -> return (id, v)
                         _ -> do s <- fresh "s"
                                 return (Let s t (Ret v), Var s)
           let test (l,b) rest
                 = do x <- fresh "eq"
                      yes <- branchBody b
                      no <- rest
                      return (Let x tbool (Call (toLidar eq) [] [s, elabLit l])
                                (CaseV (Var x) [(0, child x (SInjV 0 (Con (toLidar nameFalse))), no)
                                               ,(1, child x (SInjV 1 (Con (toLidar nameTrue))), yes)]))
           bind <$> foldr test def pats

-- the equality functions of `int` and `string`, which compare literal patterns
nameIntEq, nameStringEq :: Name
nameIntEq = newQualified "std/core/int" "=="
nameStringEq = newQualified "std/core/string" "=="

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
       let cons = zip [0..] (dataInfoConstrs info)   -- by position
       body <- case cons of
                 [(_,con)] -> conBranch vargs con (Left z) (findBranch con brs)
                 _ | isLazyInfo info -> lazyCase vargs brs z cons
                   | otherwise -> sumCase vargs brs z cons (wildBody brs)
       return (Deref v p (Unroll p z body))

-- A case on the alternatives `cons` of the boxed sum `z`. Those without a branch of their own
-- take the default, if any; a case of the default alone is the default.
sumCase :: [AType] -> [C.Branch] -> Path -> [(Int,ConInfo)] -> Maybe (E VExpr) -> E VExpr
sumCase vargs brs z cons def
  = do let selected = [(i,c) | (i,c) <- cons, isNothing def || any (matches c) brs]
       alts <- mapM (boxedAlt vargs brs z) selected
       case def of
         Just d | null alts -> d
                | length selected < length cons -> do y <- fresh "default"
                                                      e <- d
                                                      return (CaseA z alts (Just (y,e)))
         _ -> return (CaseA z alts Nothing)

-- A match on a lazy value tests whether it is in WHNF (`[if-whnf]`), and then matches on its
-- strict alternatives or on its thunks. Only a lazy match can name thunks, as Koka forces the
-- value of every other match (`Type.Infer`); without a default, the thunks of a match that
-- names none are thus `unreachable`. Inlining can remove the force, so a default may cover
-- thunks as well as strict alternatives; it then appears on both sides, which is cheap as
-- `Elab.Match` makes every body that is not an atom a jump to a join point.
lazyCase :: [AType] -> [C.Branch] -> Path -> [(Int,ConInfo)] -> E VExpr
lazyCase vargs brs z cons
  = do s <- fresh "whnf"
       l <- fresh "delay"
       let (thunks,stricts) = partition (conInfoIsLazy . snd) cons
           named = [c | (_,c) <- thunks, any (matches c) brs]
           def = wildBody brs
       e1 <- sumCase vargs brs s stricts def
       e2 <- if null named && isNothing def then Unreachable <$> result
             else sumCase vargs brs l thunks def
       return (IfWhnf z (s,e1) (l,e2))

-- the body of the default branch
wildBody :: [C.Branch] -> Maybe (E VExpr)
wildBody brs = listToMaybe [branchBody b | b@(C.Branch [C.PatWild] _) <- brs]

matches :: ConInfo -> C.Branch -> Bool
matches con br
  = case br of
      C.Branch [C.PatCon pc _ _ _ _ _ _ _] _ -> getName pc == conInfoName con
      _ -> False

-- The binder is the path to the alternative, which names its constructor (`Traversal.injAStep`).
boxedAlt :: [AType] -> [C.Branch] -> Path -> (Int,ConInfo) -> E (Int,Path,VExpr)
boxedAlt vargs brs z (i,con)
  = do let y = child z (SInjA i (Con (toLidar (conInfoName con))))
       e <- conBranch vargs con (Left y) (findBranch con brs)
       return (i,y,e)

elabValueCase :: DataInfo -> [AType] -> VVal -> [C.Branch] -> E VExpr
elabValueCase info vargs v brs
  = case dataInfoConstrs info of
      [con] -> conBranch vargs con (Right v) (findBranch con brs)
      cons  -> CaseV v . map snd . sortOn fst <$> mapM (valueAlt vargs brs v) (zip [0..] cons)

-- an alternative with the position of its branch in the source, to keep the order of the tests.
-- The binder of a variable scrutinee is the path to the alternative, which names its constructor
-- (`Traversal.injVStep`).
valueAlt :: [AType] -> [C.Branch] -> VVal -> (Int,ConInfo) -> E (Int,(Int,Path,VExpr))
valueAlt vargs brs v (i,con)
  = do y <- case v of
              Var z -> return (child z (SInjV i (Con (toLidar (conInfoName con)))))
              _     -> fresh "y"
       b <- conBranch vargs con (Right (Var y)) (findBranch con brs)
       return (branchIndex con brs, (i,y,b))

elabOpenCase :: DataInfo -> [AType] -> VVal -> [C.Branch] -> E VExpr
elabOpenCase info vargs v brs
  = do p <- fresh "d"
       alts <- mapM (openAlt info vargs p) [(c,b) | b@(C.Branch [C.PatCon{ C.patConInfo = c }] _) <- brs]
       def  <- case [b | b@(C.Branch [C.PatWild] _) <- brs] of
                 (b:_) -> branchBody b
                 []    -> failE "open match without default"
       return (Deref v p (CaseOpen p alts def))

-- one binder for each field of the scrutinee `d`: its path, which names the field
-- (`Traversal.openSteps`)
openAlt :: DataInfo -> [AType] -> Path -> (ConInfo,C.Branch) -> E (L.Name,[Path],VExpr)
openAlt info vargs d (con,br@(C.Branch [pat] _))
  = do recordOpenSig info (conInfoName con) (conInfoType con)
       fields <- fieldTypes vargs con
       let c = child d (SOpen (toLidar (conInfoName con)))
           xs = case fields of
                  [_] -> [c]
                  _   -> [child c (SField i f) | (i,f) <- zip [0..] (take (length fields) (conFieldNames con))]
       getters <- concat <$> sequence [bindField (subBinder p) s (id,Var x) | (p,s,x) <- zip3 (C.patConPatterns pat) fields xs]
       body <- withFields getters (branchBody br)
       return (toLidar (conInfoName con), xs, body)
openAlt _ _ _ _ = failE "unexpected open branch after matching"

-- the position of the branch that `findBranch` selects, after all branches if there is none
branchIndex :: ConInfo -> [C.Branch] -> Int
branchIndex con brs
  = head ([i | (i,C.Branch [C.PatCon c _ _ _ _ _ _ _] _) <- zip [0..] brs, getName c == conInfoName con]
          ++ [i | (i,C.Branch [C.PatWild] _) <- zip [0..] brs] ++ [length brs])

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
        -- the padding of a thunk has no binder
        getters <- destructure (zip3 (map subBinder subs ++ repeat Nothing) (conFieldNames con) (map (subst exSub) fields)) (id,payload)
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
              return (Unbox y p, Var p)

unpackK :: VVal -> [TVar] -> E (K,VVal)
unpackK v ids = do u <- fresh "e"
                   return (Unpack v ids u, Var u)

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
-- The fields are a product (`[proj]`), unless there is only one. Getters of different fields
-- project the same product, which `Paths` merges where it is in scope. The binder of a field
-- of a variable is its path, which names the field (`Traversal.projStep`).
destructure :: [(Maybe TName,Field,VType)] -> (K,VVal) -> E [(Name,(K,VVal))]
destructure [(x,_,s)] getter = bindField x s getter
destructure fields (k,p)
  = concat <$> sequence [do y <- case p of
                                   Var z -> return (child z (SField i f))
                                   _     -> fresh "field"
                            bindField x s (k . Proj p i y,Var y)
                        | (i,(x,f,s)) <- zip [0..] fields]

bindField :: Maybe TName -> VType -> (K,VVal) -> E [(Name,(K,VVal))]
bindField Nothing _ _ = return []
bindField (Just (TName x tp)) s (read,v) = do
  t <- vt tp
  (k,w) <- coerce s t v
  return [(x,(read . k,w))]
