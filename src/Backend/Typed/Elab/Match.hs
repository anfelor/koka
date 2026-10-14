-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Compilation of pattern matching to one-level single-scrutinee matches.

  Rows without a refutable pattern in the column that is matched are copied into
  every branch, so the body of each guard becomes a join point: a closed local
  function (its free variables are passed as arguments, its parameters are fresh)
  that is only called in tail position. Elaboration turns these into `Join` and
  `Jump`; `Simplify` inlines those with a single jump.

  The rows after a guard that can fail are matched again wherever the guard ends
  up. If that duplicates tests, they become a join point of their own instead
  (`fallback`), which every failure of the rows before jumps to.
-}
module Backend.Typed.Elab.Match( matchCore ) where

import Data.List( nubBy, findIndex )
import qualified Data.Set as S
import Common.Name
import Backend.Typed.Names
import Common.Unique
import Kind.Newtypes( Newtypes, newtypesLookupAny )
import Type.Type
import Core.Core
import Core.CoreVar( freeLocals, (|~>) )

type Bind = (TName,TName)
type Row  = ([Bind],[Pattern],[Guard])

matchCore :: Newtypes -> Core -> Unique Core
matchCore nt core
  = do defs <- mapM (matchDefGroup nt) (coreProgDefs core)
       return core{ coreProgDefs = defs }

matchDefGroup :: Newtypes -> DefGroup -> Unique DefGroup
matchDefGroup nt (DefRec defs)  = DefRec <$> mapM (matchDef nt) defs
matchDefGroup nt (DefNonRec def) = DefNonRec <$> matchDef nt def

matchDef :: Newtypes -> Def -> Unique Def
matchDef nt def
  = do e <- matchExpr nt (defExpr def)
       return def{ defExpr = e }

matchExpr :: Newtypes -> Expr -> Unique Expr
matchExpr nt expr
  = case expr of
      Lam pars eff body -> Lam pars eff <$> go body
      App f args        -> App <$> go f <*> mapM go args
      TypeLam tvs e     -> TypeLam tvs <$> go e
      TypeApp e tps     -> (\e' -> TypeApp e' tps) <$> go e
      Let dgs body      -> Let <$> mapM (matchDefGroup nt) dgs <*> go body
      Case scruts brs   -> do scruts' <- mapM go scruts
                              brs'    <- mapM (matchBranch nt) brs
                              matchCase (Env nt (typeOf expr) (unreachable (typeOf expr))) scruts' brs'
      _                 -> return expr
  where
    go = matchExpr nt

matchBranch :: Newtypes -> Branch -> Unique Branch
matchBranch nt (Branch pats guards)
  = Branch pats <$> mapM (\(Guard t e) -> Guard <$> matchExpr nt t <*> matchExpr nt e) guards

-- the result type and the result when no row matches
data Env = Env{ envNT :: Newtypes, envType :: Type, envFailure :: Expr }

matchCase :: Env -> [Expr] -> [Branch] -> Unique Expr
matchCase env scruts brs
  = do (binds,xs) <- unzip <$> mapM scrutVar scruts
       rows <- mapM joinBranch brs
       body <- matchRows env xs rows
       return (makeLet (concat binds) body)

matchRows :: Env -> [TName] -> [([DefGroup],Row)] -> Unique Expr
matchRows env xs rows
  = do tree <- withJoins rows <$> compile env xs (map snd rows)
       case findIndex (canFail . snd) (init rows) of
         Nothing -> return tree
         Just k  -> do let (pre,post) = splitAt (k+1) rows
                       (jdef,jump) <- closeJoin =<< matchRows env xs post
                       shared <- withJoins pre . makeLet [jdef] <$> compile env{ envFailure = jump } xs (map snd pre)
                       return (if tests shared < tests tree then shared else tree)
  where
    withJoins rs = makeLet (concatMap fst rs)
    canFail (_,_,guards) = not (any (\(Guard t _) -> isExprTrue t) guards)

tests :: Expr -> Int
tests expr
  = case expr of
      Lam _ _ e     -> tests e
      App f args    -> sum (map tests (f:args))
      TypeLam _ e   -> tests e
      TypeApp e _   -> tests e
      Let dgs e     -> sum [tests (defExpr d) | d <- flattenDefGroups dgs] + tests e
      Case ss brs   -> 1 + sum (map tests ss) + sum [tests t + tests e | Branch _ gs <- brs, Guard t e <- gs]
      _             -> 0

unreachable :: Type -> Expr
unreachable tp = Var (TName nameUnreachable tp) InfoNone

isUnreachable :: Expr -> Bool
isUnreachable (Var x _) = getName x == nameUnreachable
isUnreachable _         = False

joinBranch :: Branch -> Unique ([DefGroup],Row)
joinBranch (Branch pats guards)
  = do (joins,guards') <- unzip <$> mapM joinGuard guards
       return (concat joins, ([],pats,guards'))

joinGuard :: Guard -> Unique ([DefGroup],Guard)
joinGuard (Guard test body)
  | isAtom body = return ([],Guard test body)
  | otherwise   = do (jdef,jump) <- closeJoin body
                     return ([jdef],Guard test jump)
  where
    isAtom e = case e of
                 Var _ _     -> True
                 Lit _       -> True
                 Con _ _     -> True
                 TypeApp e' _ -> isAtom e'
                 _           -> False

closeJoin :: Expr -> Unique (DefGroup,Expr)
closeJoin body
  = do j  <- uniqueName "join"
       let xs = filter (not . isJoinName . getName) (tnamesList (freeLocals body))
       ps <- mapM (freshVar . typeOf) xs
       let lam = Lam ps typeTotal ([(x,Var p InfoNone) | (x,p) <- zip xs ps] |~> body)
       return (DefNonRec (makeDef j lam), App (Var (TName j (typeOf lam)) InfoNone) [Var x InfoNone | x <- xs])

scrutVar :: Expr -> Unique ([DefGroup],TName)
scrutVar (Var x _) = return ([],x)
scrutVar e = do x <- freshVar (typeOf e)
                return ([DefNonRec (makeDef (getName x) e)],x)

freshVar :: Type -> Unique TName
freshVar tp = do n <- uniqueName "m"
                 return (TName n tp)

compile :: Env -> [TName] -> [Row] -> Unique Expr
compile env _ [] = return (envFailure env)
compile env xs rows@(_:rest)
  = do let rows'@((binds,pats,guards):_) = map (stripVars xs) rows
       case findIndex isRefutable pats of
         Nothing -> do fallback <- compile env xs rest
                       return (makeLet (bindDefs (used guards binds)) (guardChain guards fallback))
         Just i  -> switch env xs i rows'

-- Koka names every pattern (`@pat`), mostly without using it
used :: [Guard] -> [Bind] -> [Bind]
used guards binds = [b | b@(y,_) <- binds, y `S.member` fvs]
  where fvs = S.unions [freeLocals t `S.union` freeLocals e | Guard t e <- guards]

bindDefs :: [Bind] -> [DefGroup]
bindDefs binds = [DefNonRec (makeDef (getName y) (Var x InfoNone)) | (y,x) <- reverse binds]

stripVars :: [TName] -> Row -> Row
stripVars xs (binds,pats,guards)
  = let (bs,ps) = unzip (zipWith strip xs pats)
    in (binds ++ concat bs, ps, guards)
  where
    strip x (PatVar y p) = let (bs,p') = strip x p in ((y,x):bs,p')
    strip _ p            = ([],p)

isRefutable :: Pattern -> Bool
isRefutable PatWild = False
isRefutable _       = True

guardChain :: [Guard] -> Expr -> Expr
guardChain [] fallback = fallback
guardChain (Guard test body : gs) fallback
  | isExprTrue test = body
  | otherwise       = Case [test] [Branch [patTrue] [Guard exprTrue body]
                                  ,Branch [PatWild] [Guard exprTrue (guardChain gs fallback)]]

switch :: Env -> [TName] -> Int -> [Row] -> Unique Expr
switch env xs i rows
  = do let x     = xs !! i
           heads = nubBy sameHead [p | (_,ps,_) <- rows, let p = ps !! i, isRefutable p]
       brs <- mapM (specialize env xs i rows) heads
       def <- if complete (envNT env) heads then return [] else defaultBranch env xs i rows
       return (Case [Var x InfoNone] (brs ++ def))

sameHead :: Pattern -> Pattern -> Bool
sameHead (PatCon c1 _ _ _ _ _ _ _) (PatCon c2 _ _ _ _ _ _ _) = getName c1 == getName c2
sameHead (PatLit l1) (PatLit l2) = l1 == l2
sameHead _ _ = False

specialize :: Env -> [TName] -> Int -> [Row] -> Pattern -> Unique Branch
specialize env xs i rows p@(PatCon c _ repr targs exists tres info skip)
  = do ys <- mapM freshVar targs
       let xs'   = take i xs ++ ys ++ drop (i+1) xs
           rows' = [row' | row <- rows, Just row' <- [specRow (length ys) row]]
       body <- compile env xs' rows'
       return (Branch [PatCon c [PatVar y PatWild | y <- ys] repr targs exists tres info skip] [Guard exprTrue body])
  where
    specRow n (bs,ps,gs)
      = case ps !! i of
          PatWild -> Just (bs, take i ps ++ replicate n PatWild ++ drop (i+1) ps, gs)
          q | sameHead p q -> Just (bs, take i ps ++ patConPatterns q ++ drop (i+1) ps, gs)
          _ -> Nothing
specialize env xs i rows p@(PatLit _)
  = do body <- compile env (dropAt i xs) [(bs,dropAt i ps,gs) | (bs,ps,gs) <- rows, let q = ps !! i, not (isRefutable q) || sameHead p q]
       return (Branch [p] [Guard exprTrue body])
specialize _ _ _ _ _ = error "Backend.Typed.Elab.Match.specialize: unexpected pattern"

-- without default rows the constructors are complete unless the rows are followed by a fallback
defaultBranch :: Env -> [TName] -> Int -> [Row] -> Unique [Branch]
defaultBranch env xs i rows
  = case [(bs,dropAt i ps,gs) | (bs,ps,gs) <- rows, not (isRefutable (ps !! i))] of
      [] | isUnreachable (envFailure env) -> return []
      rows' -> do body <- compile env (dropAt i xs) rows'
                  return [Branch [PatWild] [Guard exprTrue body]]

complete :: Newtypes -> [Pattern] -> Bool
complete nt heads@(PatCon{ patConInfo = info } : _)
  = case newtypesLookupAny (conInfoTypeName info) nt of
      Just di -> not (dataInfoIsOpen di) && length heads == length (dataInfoConstrs di)
      Nothing -> False
complete _ _ = False

dropAt :: Int -> [a] -> [a]
dropAt i xs = take i xs ++ drop (i+1) xs
