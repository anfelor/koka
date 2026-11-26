------------------------------------------------------------------------------
-- Copyright 2026, Anton Lorenzen
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-|
Elaboration of a dump's mono declarations into lidar's IR.

LCNF is already in A-normal form and its matches are one level deep, so elaboration maps each
form to the IR: @let@ to @let@, @cases@ to a case on an enumeration or on the alternatives of a
datatype, @proj@ to destructuring, @jp@/@jmp@ to joins and jumps, constants to calls and
constructor values, and the application of a local to the application of a closure.

A trivial structure is its relevant field: its constructor is the field, a @cases@ on it binds
the field to the scrutinee (and the other fields to erased values), and projecting the field is
the value itself.

An action (`funTypes`) takes lidar's effect token for the state of the world and returns it
beside its result. Elaboration keeps the current token, which stands for every local of the
state (`lcVoid`, bound to `()`): a call of an action takes it and gives the next one, and
returning a result of an action returns the token beside it. Join points in an action take the
token as their last parameter. Where code without a token calls an action, the call is a
`[total]` region.

Where the type of a value and the type it is used at differ, elaboration converts through
@any*@: @up@ and @down@ for pointers, @Scalar@ boxes for raw values, and boxed sums for
enumerations, as Lean boxes them. Closures take and return @any*@; a partial application of a
constant is a closure that converts the remaining arguments and the result.
-}
module Lidar.Lean.Elab( elabDump ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( zipWithM, mfilter )
import Data.Char( isAlphaNum, isDigit )
import Data.List( sortOn )
import Lidar
import Lidar.Build( K, compose, prodVal )
import Lidar.Env( M, evalM, asks, local, get, put )
import Lidar.Types( Types(alphaEq), vtInt, vtString, unToken, tokenParam )
import Lidar.Layout( isEnum )
import Lidar.Traversal( child )
import Lidar.Elab.Representation( boxA, shapeLeaves, leafCons, injA, caseSum, conValue )
import qualified Lidar.Lean.Dump as D
import Lidar.Lean.Decls

-- the declarations, the IR variable and type of each local, the parameter types of each
-- join point in scope, the default binder in scope of a case on a local (see `elabCases`),
-- the borrowed locals (see `closedJoin`), and the current token in an action
data Ctx = Ctx{ cDecls :: Decls, cLocals :: M.Map D.Var (Path,VType), cJoins :: M.Map D.Var (Name,[D.Var],[VType])
              , cRests :: M.Map D.Var Rest, cBorrowed :: S.Set D.Var, cToken :: Maybe Path }

-- A `cases` on a local inside the default of a `[case-a]` on it scrutinizes the default
-- binder instead, whose sum lacks the tags of the alternatives before it: binding the local's
-- default path again would bind it twice in its scope. `Rest p d tags`: the local at path `p`,
-- the binder `d` and the tags it lacks.
data Rest = Rest Path Path [Int]

-- the sum of the local at a path, as `unrollLocal` binds it
unrolled :: Path -> Path
unrolled p = child (child p SDeref) SRoll

type E a = M Ctx Int a

-- | The program of a dump, and the errors of the declarations that could not be elaborated.
elabDump :: D.Dump -> (Program,[String])
elabDump d
  = (Program (newModuleName (D.dumpModule d)) (dTypes ds) (dSigs ds) M.empty (Foreign [] [] []) defs, errs)
  where
    ds = declsOf d
    results = [(x, evalM (elabDecl x) (Ctx ds M.empty M.empty M.empty S.empty Nothing) 0) | x <- D.dumpDecls d]
    defs = [def | (_,Right (Just def)) <- results]
    errs = [D.declName x ++ ": " ++ err | (x,Left err) <- results]

elabDecl :: D.Decl -> E (Maybe Def)
elabDecl x
  = case D.declValue x of
      D.Extern _ -> return Nothing
      D.Body code ->
        do sigs <- asks (dSigs . cDecls)
           case M.lookup name sigs of
             Just (SigVal _ t) -> Just . DefVal name [] t <$> elabCode t code
             Just (SigFun _ ps _ r) ->
               do let (ps',token) = tokenParam ps
                      args = [(p,varPath (D.paramVar p) (D.paramName p),m,t) | (p,(m,t)) <- zip (D.declParams x) ps']
                  (tparam,withTok) <- tokenBinder token
                  body <- local (\c -> c{ cBorrowed = S.fromList [D.paramVar p | (p,_,Borrowed,_) <- args] })
                            (withLocals [(D.paramVar p,(v,t)) | (p,v,_,t) <- args]
                               (withTok (worlds (drop (length ps') (D.declParams x)) (elabCode r code))))
                  return (Just (DefFun name [] ([(v,m,t) | (_,v,m,t) <- args] ++ tparam) Owned r body InlineAuto))
             _ -> fail "no signature"
  where
    name = leanName (D.declName x)

------------------------------------------------------------------------------
-- Names and the context
------------------------------------------------------------------------------

-- the root of a local
varPath :: D.Var -> D.Name -> Path
varPath x n = root (varName x n)

-- the name of a local: its user name (made an identifier) and the number of its `FVarId`
varName :: D.Var -> D.Name -> Name
varName x n = newName (map ident n ++ "_" ++ reverse (takeWhile isDigit (reverse x)))
  where ident c = if isAlphaNum c then c else '_'

-- a fresh name, which no local has (their names do not start with `@`)
freshName :: String -> E Name
freshName s = do n <- get
                 put (n+1)
                 return (newName ("@" ++ s ++ show n))

fresh :: String -> E Path
fresh s = root <$> freshName s

withLocals :: [(D.Var,(Path,VType))] -> E a -> E a
withLocals xs = local (\c -> c{ cLocals = M.union (M.fromList xs) (cLocals c) })

bindLocal :: D.Var -> D.Name -> VType -> (Path -> E a) -> E a
bindLocal x n t k = withLocals [(x,(v,t))] (k v)
  where v = varPath x n

-- the token parameter of an action (if it is one), and the elaboration of its body with that
-- token
tokenBinder :: Bool -> E ([(Path,Mode,VType)], E a -> E a)
tokenBinder False = return ([], tokenIn Nothing)
tokenBinder True = do k <- fresh "k"
                      return ([(k,Owned,VToken)], tokenIn (Just k))

tokenIn :: Maybe Path -> E a -> E a
tokenIn k = local (\c -> c{ cToken = k })

-- the current token, as an argument (none outside of actions)
tokenArgs :: E [VVal]
tokenArgs = maybe [] (\k -> [Var k]) <$> asks cToken

-- locals of the state of the world, which the token stands for, bound to `()`
worlds :: [D.Param] -> E VExpr -> E VExpr
worlds ps m = foldr world m ps
  where world p k = bindLocal (D.paramVar p) (D.paramName p) VUnit $ \v -> Let v VUnit (Ret UnitV) <$> k

inds :: E (M.Map D.Name D.Inductive)
inds = asks (dInductives . cDecls)

irT :: D.Type -> E VType
irT t = do is <- inds
           return (irType is t)

------------------------------------------------------------------------------
-- Conversions through `any*`
------------------------------------------------------------------------------

-- `v : from` as a value of type `to`
coerce :: VType -> VType -> VVal -> E (K,VVal)
coerce from to v
  | alphaEq from to = return (id, v)
  | otherwise = do (k1,a) <- toAny from v
                   (k2,w) <- fromAny to a
                   return (k1 . k2, w)

-- the constant that erased values and the unit stand for at `any*` (Lean's `lean_box(0)`)
erasedAny :: VVal
erasedAny = Up (Ptr AUnit UnitA)

toAny :: VType -> VVal -> E (K,VVal)
toAny t v
  = case t of
      VPtr AAny -> return (id, v)
      VPtr _ -> return (id, Up v)
      VRaw r -> return (id, Up (Ptr (AScalar r) (Scalar v)))
      VUnit -> return (id, erasedAny)
      VSum ts | isEnum t ->
        do r <- fresh "box"
           alts <- mapM (\i -> do y <- fresh "e"
                                  return (i, y, Ret (Up (Ptr (boxA t) (injA (shapeLeaves t) i UnitA))))) [0 .. length ts - 1]
           return (Let r anyT (CaseV v alts), Var r)
      _ -> fail ("cannot convert a value of type " ++ ppr t ++ " to any*")

fromAny :: VType -> VVal -> E (K,VVal)
fromAny t a
  = case t of
      VPtr AAny -> return (id, a)
      VPtr b -> return (id, Down b a)
      VUnit -> return (id, UnitV)
      VRaw r ->
        do s <- fresh "s"
           x <- fresh "x"
           let d = child s SDeref
           return (Let s (VPtr (AScalar r)) (Ret (Down (AScalar r) a)) . Deref (Var s) d . Unscalar d x, Var x)
      VSum ts | isEnum t ->
        do s <- fresh "s"
           r <- fresh "e"
           let d = child s SDeref
           body <- caseSum (leafCons ts) (shapeLeaves t) d (\i _ -> return (Ret (Inj i t UnitV)))
           return (Let s (VPtr (boxA t)) (Ret (Down (boxA t) a)) . Deref (Var s) d . Let r t body, Var r)
      _ -> fail ("cannot convert any* to " ++ ppr t)

-- a local at type `t`
localVal :: D.Var -> VType -> E (K,VVal)
localVal x t
  = do ls <- asks cLocals
       case M.lookup x ls of
         Just (v,s) -> coerce s t (Var v)
         Nothing -> fail ("unknown local " ++ x)

localType :: D.Var -> E VType
localType x = do ls <- asks cLocals
                 maybe (fail ("unknown local " ++ x)) (return . snd) (M.lookup x ls)

-- an argument at type `t`
argVal :: D.Arg -> VType -> E (K,VVal)
argVal _ VToken = do k <- asks cToken
                     maybe (fail "an action called without a token") (\p -> return (id, Var p)) k
argVal a t
  = case a of
      D.AVar x -> localVal x t
      _ -> erased t

erased :: VType -> E (K,VVal)
erased t = coerce anyT t erasedAny

args :: [D.Arg] -> [VType] -> E (K,[VVal])
args as ts = do kvs <- zipWithM argVal as ts
                return (compose (map fst kvs), map snd kvs)

------------------------------------------------------------------------------
-- Code
------------------------------------------------------------------------------

-- the code of a function body (or join point) with result type `res`
elabCode :: VType -> D.Code -> E VExpr
elabCode res code
  = case code of
      D.Let x n t v k ->
        do tx <- irT t
           action <- callsAction v
           tok <- asks cToken
           case tok of
             Nothing | action ->
               do k0 <- fresh "k"
                  (kv,e,te) <- tokenIn (Just k0) (elabValue tx v)
                  te0 <- maybe (fail "an action without a token in its result") return (unToken te)
                  kv <$> bindValue x n tx (Total k0 e) te0 (elabCode res k)
             _ ->
               do (kv,e,te) <- elabValue tx v
                  case (unToken te, k) of
                    (Just _, D.Return y) | y == x, alphaEq te res -> return (kv e)
                    (Just te0, _) ->
                      do p <- fresh "p"
                         let field i = child p (SField i (posField i))
                         body <- bindValue x n tx (Ret (Var (field 0))) te0 (tokenIn (Just (field 1)) (elabCode res k))
                         return (kv (Let p te e (Proj (Var p) 0 (field 0) (Proj (Var p) 1 (field 1) body))))
                    (Nothing, _) -> kv <$> bindValue x n tx e te (elabCode res k)
      D.Fun f k ->
        do lam <- elabLam f
           bindLocal (D.funVar f) (D.funName f) anyT $ \p ->
             Let p anyT (Ret lam) <$> elabCode res k
      -- Perceus expects closed join points: the locals that the body captures become
      -- parameters (before those of the join point), which every jump passes on
      D.Jp f k ->
        do let own = [(D.paramVar p, D.paramName p, D.paramType p) | p <- D.funParams f]
           ts <- mapM (\(_,_,t) -> irT t) own
           (captured,params,body) <- closedJoin res [(varPath x n, (x,t)) | ((x,n,_),t) <- zip own ts] (D.funBody f)
           let j = varName (D.funVar f) (D.funName f)
           cont <- local (\c -> c{ cJoins = M.insert (D.funVar f) (j,captured,ts) (cJoins c) }) (elabCode res k)
           return (Join j [] params body cont)
      D.Jmp j as ->
        do js <- asks cJoins
           case M.lookup j js of
             Just (name,captured,ts) | length ts == length as ->
               do (kc,cvs) <- args (map D.AVar captured) =<< mapM localType captured
                  (k,vs) <- args as ts
                  tvs <- tokenArgs
                  return (kc (k (Jump name [] (cvs ++ vs ++ tvs))))
             _ -> fail ("jump to unknown join point " ++ j)
      D.Cases tname _ x alts -> elabCases res tname x alts
      D.Return x -> case unToken res of
                      Just r0 -> do (k,v) <- localVal x r0
                                    tvs <- tokenArgs
                                    if null tvs then fail "a result of an action without a token"
                                      else return (k (Ret (Tuple (v : tvs))))
                      Nothing -> do (k,v) <- localVal x res
                                    return (k (Ret v))
      D.Unreach _ -> return (Unreachable res)
      D.Unsupported -> fail "unsupported code"

-- `let x : tx = e in m`, for an expression `e : te`
bindValue :: D.Var -> D.Name -> VType -> VExpr -> VType -> E VExpr -> E VExpr
bindValue x n tx e te m
  = bindLocal x n tx $ \p ->
      do body <- m
         if alphaEq te tx then return (Let p tx e body)
           else do tmp <- fresh "v"
                   (kc,w) <- coerce te tx (Var tmp)
                   return (Let tmp te e (kc (Let p tx (Ret w) body)))

-- whether a `let` value calls an action (with all its arguments)
callsAction :: D.LetValue -> E Bool
callsAction v
  = case v of
      D.VConst c as -> do sigs <- asks (dSigs . cDecls)
                          ctors <- asks (dCtors . cDecls)
                          return $ case M.lookup (leanName c) sigs of
                                     Just (SigFun _ ps _ _) -> snd (tokenParam ps) && length as == length ps && not (M.member c ctors)
                                     _ -> False
      _ -> return False

-- The value of a `let` with type `t`, before its conversion to `t`: the code that binds its
-- operands, an expression, and the type of the expression.
elabValue :: VType -> D.LetValue -> E (K,VExpr,VType)
elabValue t v
  = case v of
      D.VLit (D.LNat n) -> return (id, Ret (Lit (LitInt n)), vtInt)
      D.VLit (D.LStr s) -> return (id, Ret (Lit (LitString s)), vtString)
      D.VLit l | Just (n,r) <- rawLit l, Just f <- rawOfNat r
               -> return (id, Call (leanName f) [] [Lit (LitInt n)], VRaw r)
      D.VErased -> do (k,w) <- erased t
                      return (k, Ret w, t)
      D.VProj tname i x -> elabProj tname (fromInteger i) x
      D.VConst c as -> elabConst c as
      D.VFVar f [] -> do ls <- asks cLocals
                         case M.lookup f ls of
                           Just (p,s) -> return (id, Ret (Var p), s)
                           Nothing -> fail ("unknown local " ++ f)
      D.VFVar f as -> do (k1,fv) <- localVal f anyT
                         (k2,e) <- apply fv as
                         return (k1 . k2, e, anyT)
      D.VLit l -> fail ("literal " ++ show l)
      D.VUnsupported -> fail "unsupported let value"
  where
    rawLit l = case l of
                 D.LU8 n -> Just (n,RUInt8)
                 D.LU16 n -> Just (n,RUInt16)
                 D.LU32 n -> Just (n,RUInt32)
                 D.LU64 n -> Just (n,RUInt64)
                 D.LUSize n -> Just (n,RUSize)
                 D.LNat _ -> Nothing
                 D.LStr _ -> Nothing

-- the application of a closure `fv : any*` to arguments, with result `any*`; it is cast to a
-- function of that arity, as Lean's `lean_apply_n` checks the arity at run time
apply :: VVal -> [D.Arg] -> E (K,VExpr)
apply fv as
  = do (k,vs) <- args as (map (const anyT) as)
       s <- fresh "f"
       let ft = AFun [(Owned,anyT) | _ <- as] anyT
           g = child s SDeref
       return (k, Let s (VPtr ft) (Ret (Down ft fv)) (Deref (Var s) g (App g vs)))

-- a constant applied to arguments: a constructor value, a call, a closure for a partial
-- application, or a call whose result is applied to the remaining arguments
elabConst :: D.Name -> [D.Arg] -> E (K,VExpr,VType)
elabConst c as
  = do ds <- asks cDecls
       case (M.lookup c (dCtors ds), M.lookup (leanName c) (dSigs ds)) of
         (Just ci, _) | not (isBuiltinType (ciType ci)) -> elabCon ci (drop (ciNumParams ci) as)
         (_, Just (SigFun _ ps _ r))
           | length as == length ps -> do (k,vs) <- args as (map snd ps)
                                          return (k, Call (leanName c) [] vs, r)
           | length as < length ps -> do (k,lam) <- closure (leanName c) ps r as
                                         return (k, Ret lam, anyT)
           | otherwise -> do (k1,vs) <- args (take (length ps) as) (map snd ps)
                             x <- fresh "r"
                             (k2,fv) <- coerce r anyT (Var x)
                             (k3,e) <- apply fv (drop (length ps) as)
                             return (k1 . Let x r (Call (leanName c) [] vs) . k2 . k3, e, anyT)
         (_, Just (SigVal _ t))
           | null as -> return (id, Ret (Glob (leanName c) []), t)
           | otherwise -> do (k1,fv) <- coerce t anyT (Glob (leanName c) [])
                             (k2,e) <- apply fv as
                             return (k1 . k2, e, anyT)
         _ -> fail ("unknown constant " ++ c)

-- The partial application of `f` to `as`: a closure that takes the remaining arguments at
-- `any*`, converts them, calls `f` and converts its result to `any*`. Closures do not pass
-- the token: the call of an action is a `[total]` region.
closure :: Name -> [(Mode,VType)] -> VType -> [D.Arg] -> E (K,VVal)
closure f ps r as
  = do let (given,rest) = splitAt (length as) (map snd ps)
           (rest',token) = tokenParam [((),t) | t <- rest]
       (k,vs) <- args as given
       xs <- mapM (const (fresh "a")) rest
       cs <- zipWithM (\x (_,t) -> coerce anyT t (Var x)) xs rest'
       y <- fresh "r"
       k0 <- fresh "k"
       let (call,r0) = case unToken r of
                         Just r0' | token -> (Total k0 (Call f [] (vs ++ map snd cs ++ [Var k0])), r0')
                         _ -> (Call f [] (vs ++ map snd cs), r)
       (kr,w) <- coerce r0 anyT (Var y)
       let body = compose (map fst cs) (Let y r0 call (kr (Ret w)))
           ft = AFun [(Owned,anyT) | _ <- rest] anyT
       return (k, Up (Ptr ft (Lam [(x,Owned,anyT) | x <- xs] anyT body)))

-- a local function: a closure that converts its arguments from `any*` and its result to
-- `any*`; the body of an action is a `[total]` region, as closures do not pass the token
elabLam :: D.FunDecl -> E VVal
elabLam (D.FunDecl _ _ ps t b)
  = do is <- inds
       let (ts0,r) = funTypes is (map D.paramType ps) (resultType (length ps) t)
           (ts,token) = tokenParam [((),s) | s <- ts0]
           (own,world) = splitAt (length ts) ps
       xs <- mapM (const (fresh "a")) ps
       let vs = [varPath (D.paramVar p) (D.paramName p) | p <- own]
       cs <- zipWithM (\x (_,s) -> coerce anyT s (Var x)) xs ts
       (tparam,withTok) <- tokenBinder token
       body <- local (\c -> c{ cRests = M.empty, cBorrowed = S.empty })
                 (withLocals (zip (map D.paramVar own) (zip vs (map snd ts))) (withTok (worlds world (elabCode r b))))
       y <- fresh "r"
       let (body',r0) = case (tparam, unToken r) of
                          ((k,_,_):_, Just r0') -> (Total k body, r0')
                          _ -> (body, r)
       (kr,w) <- coerce r0 anyT (Var y)
       let binds = [Let v s (Ret c) | (v,(_,s),(_,c)) <- zip3 vs ts cs]
           ft = AFun [(Owned,anyT) | _ <- ps] anyT
       return (Up (Ptr ft (Lam [(x,Owned,anyT) | x <- xs] anyT
                             (compose (map fst cs ++ binds) (Let y r0 body' (kr (Ret w)))))))

-- a constructor applied to its fields (without its parameters); that of a trivial structure
-- is its relevant field
elabCon :: CtorInfo -> [D.Arg] -> E (K,VExpr,VType)
elabCon ci as
  | length as /= length (ciFields ci) = fail ("partial application of a constructor of " ++ ciType ci)
  | otherwise
  = do t <- irT (D.TConst (ciType ci))
       triv <- trivialField (ciType ci)
       case triv of
         Just f -> do (k,v) <- argVal (as !! f) t
                      return (k, Ret v, t)
         Nothing -> elabConValue ci as

-- the relevant field of a trivial structure
trivialField :: D.Name -> E (Maybe Int)
trivialField tname
  = do is <- inds
       return $ case (typeKind is tname, M.lookup tname is) of
                  (KTrivial _ _, Just ind) | Just (_,_,f,_) <- D.indTrivial ind -> Just (fromInteger f)
                  _ -> Nothing

elabConValue :: CtorInfo -> [D.Arg] -> E (K,VExpr,VType)
elabConValue ci as
  = do let stored = [(a,ft) | (a,Just ft) <- zip as (ciFields ci)]
       (k,vs) <- args (map fst stored) (map snd stored)
       tdefs <- asks (dTypes . cDecls)
       t <- irT (D.TConst (ciType ci))
       w <- conValue tdefs (leanName (ciType ci)) [] (ciIndex ci) M.empty (prodVal vs)
       return (k, Ret w, t)

------------------------------------------------------------------------------
-- Destructuring
------------------------------------------------------------------------------

-- the alternatives of a reference datatype, by constructor index, and the type of each
refAlts :: D.Name -> E (AType,[(Int,AType)])
refAlts tname
  = do tdefs <- asks (dTypes . cDecls)
       case M.lookup (leanName tname) tdefs of
         Just TypeDef{ tdefBody = BodyRef body } ->
           return (body, case body of
                           ASum ts -> ts
                           _ -> [(0,body)])
         _ -> fail ("destructuring a value of " ++ tname ++ ", which is not a datatype")

-- `let ptr d = x in let roll r = d in k r`, for `x : T*` (converted to `T*` first if needed)
unrollLocal :: D.Var -> D.Name -> (Path -> E VExpr) -> E VExpr
unrollLocal x tname k
  = do t <- irT (D.TConst tname)
       (kx,v) <- localVal x t
       (bind,s) <- case v of
                     Var p -> return (id, p)
                     _ -> do s <- fresh "p"
                             return (Let s t (Ret v), s)
       let d = child s SDeref
           r = child d SRoll
       body <- k r
       return (kx (bind (Deref (Var s) d (Unroll d r body))))

-- The fields of an alternative `y` of a constructor, bound to the parameters `ps` of a
-- `cases` alternative (one for each field of the constructor) around the code of `k`.
bindFields :: CtorInfo -> AType -> Path -> [D.Param] -> E VExpr -> E VExpr
bindFields ci shape y ps k
  = case shape of
      ABox contents -> do let c = child y SContents
                          Unbox y c <$> fields (Just (c,contents))
      _ -> fields Nothing
  where
    stored = length [() | Just _ <- ciFields ci]
    fields cv = go cv 0 (zip ps (ciFields ci))
    go _ _ [] = k
    go cv i ((p,f):rest)
      = do tp <- irT (D.paramType p)
           case (f, cv) of
             (Just ft, Just (c,contents)) ->
               do (kf,fp) <- if stored == 1 then return (id,c)
                               else do let fp = child c (SField i (fieldOf contents i))
                                       return (Proj (Var c) i fp, fp)
                  body <- if alphaEq ft tp then withLocals [(D.paramVar p,(fp,tp))] (go cv (i+1) rest)
                          else do (kc,w) <- coerce ft tp (Var fp)
                                  bindLocal (D.paramVar p) (D.paramName p) tp $ \v ->
                                    kc . Let v tp (Ret w) <$> go cv (i+1) rest
                  return (kf body)
             (Just _, Nothing) -> fail ("a field of the constructor without fields of " ++ ciType ci)
             (Nothing, _) ->
               do (kc,w) <- erased tp
                  bindLocal (D.paramVar p) (D.paramName p) tp $ \v ->
                    kc . Let v tp (Ret w) <$> go cv i rest
    fieldOf contents i = case contents of
                           VProd fs | (f,_):_ <- drop i fs -> f
                           _ -> posField i

-- the only constructor of a structure type
structCtor :: D.Name -> E CtorInfo
structCtor tname
  = do ds <- asks cDecls
       case M.lookup tname (dInductives ds) of
         Just D.Inductive{ D.indCtors = [c] } | Just ci <- M.lookup (D.ctorName c) (dCtors ds) -> return ci
         _ -> fail ("projection of " ++ tname ++ ", which is not a structure")

-- `proj[i] x` of the structure type `tname`
elabProj :: D.Name -> Int -> D.Var -> E (K,VExpr,VType)
elabProj tname i x
  = do triv <- trivialField tname
       case triv of
         Just f | f == i -> do t <- irT (D.TConst tname)
                               (k,v) <- localVal x t
                               return (k, Ret v, t)
                | otherwise -> do (k,w) <- erased anyT
                                  return (k, Ret w, anyT)
         Nothing -> elabStructProj tname i x

elabStructProj :: D.Name -> Int -> D.Var -> E (K,VExpr,VType)
elabStructProj tname i x
  = do ci <- structCtor tname
       (body,_) <- refAlts tname
       case (drop i (ciFields ci), body) of
         (Just ft : _, ABox contents) ->
           do let s = length [() | Just _ <- take i (ciFields ci)]
              e <- unrollLocal x tname $ \y ->
                     do let c = child y SContents
                            fp = child c (SField s (posField s))
                        return (Unbox y c (case contents of
                                             VProd _ -> Proj (Var c) s fp (Ret (Var fp))
                                             _ -> Ret (Var c)))
              return (id, e, ft)
         (Nothing : _, _) -> do (k,w) <- erased anyT
                                return (k, Ret w, anyT)
         _ -> fail ("projection of field " ++ show i ++ " of " ++ tname)

elabCases :: VType -> D.Name -> D.Var -> [D.Alt] -> E VExpr
elabCases res tname x alts
  = do is <- inds
       ds <- asks cDecls
       trivial <- trivialField tname
       let explicit = [(ciIndex ci, (c,ci,ps,body)) | D.Alt c ps body <- alts, Just ci <- [M.lookup c (dCtors ds)]]
           dflt = [body | D.Default body <- alts]
           covered i = i `elem` map fst explicit
       if length explicit + length dflt /= length alts then fail ("an alternative of a case on " ++ tname) else
         case typeKind is tname of
           -- the alternative of a trivial structure binds its relevant field to the scrutinee
           KTrivial _ _ | [(_,(_,_,ps,code))] <- explicit, Just f <- trivial ->
             do let bind (j,p) k = do tp <- irT (D.paramType p)
                                      (kv,w) <- if j == f then localVal x tp else erased tp
                                      bindLocal (D.paramVar p) (D.paramName p) tp $ \v ->
                                        kv . Let v tp (Ret w) <$> k
                foldr bind (elabCode res code) (zip [0..] ps)
           KEnum cs ->
             do t <- irT (D.TConst tname)
                (k,v) <- localVal x t
                (wrap,other) <- defaultBranch res (length (filter (not . covered) [0 .. length cs - 1])) dflt
                bs <- mapM (\i -> do y <- fresh "c"
                                     e <- case lookup i explicit of
                                            Just (_,_,_,code) -> elabCode res code
                                            Nothing -> other
                                     return (i,y,e)) [0 .. length cs - 1]
                return (k (wrap (CaseV v bs)))
           KRef ->
             do (body,shapes) <- refAlts tname
                p0 <- fmap fst . M.lookup x <$> asks cLocals
                rest <- M.lookup x <$> asks cRests
                let shapeOf i = maybe AUnit id (lookup i shapes)
                    alt y (i,(_,ci,ps,code)) = bindFields ci (shapeOf i) y ps (elabCode res code)
                    other = maybe (return (Unreachable res)) (elabCode res) (headOf dflt)
                    -- a case on the sum `r`, whose tags are not in `excl`; if `r` is the local
                    -- at `mp`, its default records its binder for the cases on the local inside
                    caseSum mp r excl
                      = do let ex = [a | a@(i,_) <- sortOn fst explicit, i `notElem` excl]
                               done = excl ++ map fst ex
                               d = child r SRest
                               inDefault = case mp of
                                             Just p -> local (\c -> c{ cRests = M.insert x (Rest p d done) (cRests c) })
                                             Nothing -> id
                           as <- mapM (\a@(i,(c,_,_,_)) -> do let y = child r (SInjA i (Con (leanName c)))
                                                              e <- alt y a
                                                              return (i,y,e)) ex
                           if null as then other else
                             do de <- if all ((`elem` done) . fst) shapes then return Nothing
                                        else do e <- inDefault other
                                                return (Just (d,e))
                                return (CaseA r as de)
                case (body, rest, p0) of
                  (ASum _, Just (Rest p d excl), Just p') | p == p' -> caseSum (Just p) d excl
                  _ -> unrollLocal x tname $ \r ->
                         case (body, sortOn fst explicit) of
                           (ASum _, _) -> caseSum (mfilter ((== r) . unrolled) p0) r []
                           (_, [a]) -> alt r a
                           (_, []) | code:_ <- dflt -> elabCode res code
                           _ -> fail ("a case on " ++ tname ++ " with several alternatives")
           _ -> fail ("case on " ++ tname ++ ", which is not a datatype")
  where
    headOf (c:_) = Just c
    headOf [] = Nothing

-- The code of the default alternative of a case on an enumeration, for the alternatives it
-- covers (n of them), and a wrapper for the case: inline if it covers one alternative, and
-- otherwise a join point that each of them jumps to. Without a default, the case covers
-- every alternative.
defaultBranch :: VType -> Int -> [D.Code] -> E (K,E VExpr)
defaultBranch res n dflt
  = case dflt of
      code:_ | n > 1 -> do j <- freshName "default"
                           (captured,params,e) <- closedJoin res [] code
                           let jump = do (k,vs) <- args (map D.AVar captured) =<< mapM localType captured
                                         tvs <- tokenArgs
                                         return (k (Jump j [] (vs ++ tvs)))
                           return (Join j [] params e, jump)
             | otherwise -> return (id, elabCode res code)
      [] -> return (id, return (Unreachable res))

-- The parameters and body of a join point with the given parameters (paths, and the locals
-- they bind). Join points are closed, as Perceus requires: the locals that the body uses
-- (also through the join points it jumps to) become parameters in front of its own, and
-- jumps pass them (first in the returned list). A borrowed local (a borrowed parameter of the
-- function, or a capture of one) is captured borrowed, as the join point runs in the frame
-- that borrows it: captured owned, each jump would duplicate it and the body drop it after a
-- tail call, which then no longer is one (`String.fromUTF8Lossy.go`). In an action, a join
-- point takes the token as its last parameter.
closedJoin :: VType -> [(Path,(D.Var,VType))] -> D.Code -> E ([D.Var],[(Path,Mode,VType)],VExpr)
closedJoin res own code
  = do ls <- asks cLocals
       js <- asks cJoins
       bs <- asks cBorrowed
       let fvs = freeVars code
           used = S.union fvs (S.fromList [y | j <- S.toList fvs, Just (_,ys,_) <- [M.lookup j js], y <- ys])
           captured = [(y,t) | y <- S.toList used, y `notElem` map (fst . snd) own, Just (_,t) <- [M.lookup y ls]]
           mode y = if S.member y bs then Borrowed else Owned
       cs <- mapM (const (fresh "capture")) captured
       (tparam,withTok) <- tokenBinder . maybe False (const True) =<< asks cToken
       let params = [(c,mode y,t) | (c,(y,t)) <- zip cs captured] ++ [(p,Owned,t) | (p,(_,t)) <- own]
       body <- withLocals (zip (map fst captured ++ map (fst . snd) own) [(p,t) | (p,_,t) <- params]) (withTok (elabCode res code))
       return (map fst captured, params ++ tparam, body)

-- the free locals of code (and the join points it jumps to)
freeVars :: D.Code -> S.Set D.Var
freeVars code
  = case code of
      D.Let x _ _ v k -> S.union (valueVars v) (S.delete x (freeVars k))
      D.Fun f k -> S.union (funVars f) (S.delete (D.funVar f) (freeVars k))
      D.Jp f k -> S.union (funVars f) (S.delete (D.funVar f) (freeVars k))
      D.Jmp j as -> S.insert j (argVars as)
      D.Cases _ _ x alts -> S.insert x (S.unions (map altVars alts))
      D.Return x -> S.singleton x
      D.Unreach _ -> S.empty
      D.Unsupported -> S.empty
  where
    funVars (D.FunDecl _ _ ps _ b) = S.difference (freeVars b) (S.fromList (map D.paramVar ps))
    altVars alt = case alt of
                    D.Alt _ ps k -> S.difference (freeVars k) (S.fromList (map D.paramVar ps))
                    D.Default k -> freeVars k
                    D.AltUnsupported -> S.empty
    valueVars v = case v of
                    D.VProj _ _ x -> S.singleton x
                    D.VConst _ as -> argVars as
                    D.VFVar f as -> S.insert f (argVars as)
                    _ -> S.empty
    argVars as = S.fromList [x | D.AVar x <- as]
