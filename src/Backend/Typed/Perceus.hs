-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{- Perceus: insert dup and drop instructions.

  Each expression is processed with the set of owned variables it must consume
  exactly once and a set of borrowed variables it may only inspect. Owned
  variables that are not free in an expression are dropped at its start.
  In `let x = e1 in e2`, the owned variables that are still needed in `e2` are
  borrowed in `e1`.

  Destructuring a dead owned variable moves its ownership to the binders
  (mode owned). Otherwise the binders are borrowed from the scrutinee (mode
  borrowed). Variables borrowed (transitively) from an owned pointer `z` are only
  duplicated where `z` is given up while they are still needed: where `z` is dead,
  they are duplicated and `z` is dropped; where `z` is consumed otherwise (passed on,
  or moved by a `let` or a destructuring), they are duplicated before. Parts of the
  contents of a box that is an alias of `z` (its pointer, from `[unfold]`, `[case]` or
  `[unpack]`) are instead taken from a copy of the whole contents,
  `let^ box p = y in let q = dup p in drop y; ...`, which drop specialization turns into
  a move (and `y` into a reuse credit) if `y` is unique. So a test such as `is-red(r)`
  does not duplicate `r`, and a nested pattern reuses the inner block where the outer
  value is dead. Reading the contents of a box is always borrowed. An unboxed scrutinee (product,
  sum, existential) is rebuilt from the binders where it is still needed (unless
  they are bound again there), so that its parts are moved and only duplicated if
  used twice; destructuring such a rebuilt value again just uses its parts.

  Exception (as Koka's Parc): `lazy-eval-locked` *takes* the fields of the lazy value
  `@lazy` in every branch that passes `@lazy` on. The parts of `@lazy` are borrowed
  without duplication and the contents of its box are taken as owned (`UnboxLazy`), so that
  the fields stay unique during evaluation; memoization then writes over the block of
  `@lazy` without dropping its old fields (see `Lazy`).

  The body of a join point is closed and processed like the body of a function; a jump
  is like a call, but nothing follows it, so owned variables are only dropped before it.
-}
module Backend.Typed.Perceus( perceusProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( foldM )
import Data.Maybe( isJust )
import Data.List( isSuffixOf )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Monad
import Backend.Typed.Check( Env(..), Gamma, envOf, bindAll, inferV, altTypes, paramModes, isTrivial )
import Backend.Typed.Types( inst, isPtr )

type VarSet = S.Set Name

-- `peLazy`: in `lazy-eval-locked`, the lazy value and the variables bound to its parts;
-- `peJoins`: the parameter modes of the join points in scope
-- `peDeps`: the borrowed variables in scope that are borrowed from an owned variable
data PEnv = PEnv{ peEnv :: Env, peGamma :: Gamma, peBorrowed :: VarSet, peLazy :: Maybe (Name,VarSet), peJoins :: M.Map Name [Mode]
                , peDeps :: M.Map Name Dep }

-- a variable borrowed from the owned pointer `depRoot`: an alias of it (its pointer at a boxed
-- type), a part of the contents of the box `y` (an alias or the root itself) at a path of
-- `Unpair`s (`True` for the second component), or anything else
data Dep = Dep{ depRoot :: Name, depKind :: DepKind }
data DepKind = Alias | Part Name [Bool] | Other

type P a = M () Int a

fresh :: String -> P Name
fresh s = state (\n -> (newHiddenName ("rc" ++ s ++ show n), n+1))

type K = Expr -> Expr

-- programs

perceusProgram :: Program -> (Program,[String])
perceusProgram prog
  = let env = envOf prog
        run d = case evalM (perceusDef env d) () 0 of
                  Right d' -> (d', [])
                  Left err -> (d, [show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs prog))
    in (prog{ progDefs = defs }, concat errs)

perceusDef :: Env -> Def -> P Def
perceusDef env def
  = case def of
      DefFun f tvs args res body
        -> do let lz = case args of
                         ((x,m,_):_) | owning m, "lazy-eval-locked" `isSuffixOf` nameLocal f -> Just (x, S.singleton x)
                         _ -> Nothing
              body' <- percE (paramEnv env args lz M.empty) (ownedParams args) body
              return (DefFun f tvs args res body')
      DefVal x tvs t body
        -> DefVal x tvs t <$> percE (PEnv env M.empty S.empty Nothing M.empty M.empty) S.empty body

-- the environment of the body of a function or join point
paramEnv :: Env -> [(Name,Mode,VType)] -> Maybe (Name,VarSet) -> M.Map Name [Mode] -> PEnv
paramEnv env ps lz js = PEnv env (M.fromList [(x,V t) | (x,_,t) <- ps]) (S.fromList [x | (x,Borrowed,_) <- ps]) lz js M.empty

ownedParams :: [(Name,Mode,VType)] -> VarSet
ownedParams ps = S.fromList [x | (x,m,t) <- ps, owning m, not (isTrivial (V t))]

typeOfV :: PEnv -> Val -> P Ty
typeOfV pe v = liftE (inferV (peEnv pe) (peGamma pe) v)

-- expressions

percE :: PEnv -> VarSet -> Expr -> P Expr
percE pe owned expr
  = do let live = fvE expr
           deps = [(x,d) | (x,d) <- M.toList (peDeps pe), S.member x live, S.member (depRoot d) owned]
       case [depRoot d | (_,d) <- deps, not (S.member (depRoot d) live)] of
         (z:_) -> settle pe owned expr z [xd | xd@(_,d) <- deps, depRoot d == z]
         [] -> case [x | (x,d) <- deps, consumedWith expr (depRoot d) x] of
                 xs@(_:_) -> do (k,pe1,own1,expr1) <- dupDeps pe owned xs expr
                                k <$> percE pe1 own1 expr1
                 [] -> do let dead = S.toList (owned `S.difference` live)
                          expr' <- percE' pe (owned `S.intersection` live) expr
                          return (foldr Drop expr' dead)

-- does `expr` consume the live owned `z` while `x`, borrowed from it, is still needed?
consumedWith :: Expr -> Name -> Name -> Bool
consumedWith expr z x
  = case expr of
      Ret _      -> True
      Call _ _ _ -> True
      App _ _    -> True
      Jump _ _   -> True
      Let _ _ _ e2 -> not (S.member z (fvE e2)) && S.member x (fvE e2)
      _ | Just ds <- destructOf expr
        -> case dsScrut ds of
             Var y -> y == z && not (isRead expr) && not (any (S.member z . fvE . snd) (dsAlts ds))
             v     -> S.member z (fvV v)
      _ -> False

-- duplicate variables borrowed from an owned variable before it is consumed
dupDeps :: PEnv -> VarSet -> [Name] -> Expr -> P (K,PEnv,VarSet,Expr)
dupDeps pe owned xs expr
  = do renames <- mapM (\x -> (,) x <$> fresh "b") xs
       ts <- mapM (tyOfVar pe) xs
       let k e = foldr (\((x,x'),t) b -> Let x' t (Ret (Dup (Var x))) b) e (zip renames ts)
       return (k, bind pe [(x',t) | ((_,x'),t) <- zip renames ts], owned `S.union` S.fromList (map snd renames),
               renameE (M.fromList renames) expr)

-- the owned `z` is dead but the variables `deps` borrowed from it are still needed: they are
-- duplicated and `z` is dropped, except that the parts of the contents of a box alias `y` are
-- taken from a copy of the whole contents (see the top)
settle :: PEnv -> VarSet -> Expr -> Name -> [(Name,Dep)] -> P Expr
settle pe owned expr z deps
  = do let parts = [(x,y,path) | (x,Dep _ (Part y path)) <- deps]
       box <- case parts of
                ((_,y,_):_) -> do t <- typeOfV pe (Var y)
                                  return (case t of { A (ABox s) -> Just (y,s); _ -> Nothing })
                [] -> return Nothing
       let taken  = case box of
                      Just (y,_) -> [(x,path) | (x,y',path) <- parts, y' == y]
                      Nothing    -> []
           others = [x | (x,_) <- deps, x `notElem` map fst taken]
       (k,pe1,own1,expr1) <- dupDeps pe owned others expr
       let own2 = S.delete z own1
       case box of
         Just (y,s) | not (null taken)
           -> do p <- fresh "p"
                 q <- fresh "q"
                 renames <- mapM (\(x,_) -> (,) x <$> fresh "t") taken
                 ts <- mapM (tyOfVar pe . fst) taken
                 wrap <- unpairs q [(path,x',t) | (((_,path),(_,x')),t) <- zip (zip taken renames) ts]
                 body <- percE (bind pe1 [(q,V s)]) (S.insert q own2) (wrap (renameE (M.fromList renames) expr1))
                 return (k (Unbox Borrowed (Var y) p (Let q (V s) (Ret (Dup (Var p))) (Drop y body))))
         _ -> k . Drop z <$> percE pe1 own2 expr1

-- bind variables to the parts of the product `v` at paths of `Unpair`s
unpairs :: Name -> [([Bool],Name,Ty)] -> P K
unpairs v xs
  = do let here  = [(x,t) | ([],x,t) <- xs]
           left  = [(path,x,t) | (False:path,x,t) <- xs]
           right = [(path,x,t) | (True:path,x,t) <- xs]
           k     = foldr (\(x,t) k' -> Let x t (Ret (Var v)) . k') id here
       if null left && null right then return k
         else do a  <- fresh "u"
                 b  <- fresh "u"
                 kl <- unpairs a left
                 kr <- unpairs b right
                 return (k . Unpair Owned (Var v) a b . kl . kr)

tyOfVar :: PEnv -> Name -> P Ty
tyOfVar pe x = maybe (fail ("unknown variable " ++ show x)) return (M.lookup x (peGamma pe))

percE' :: PEnv -> VarSet -> Expr -> P Expr
percE' pe owned (Unbox m (Var z) x e)
  | Just (lz,parts) <- peLazy pe, S.member z parts, S.member lz owned, S.member lz (fvE e)
  = do t <- typeOfV pe (Var z)
       [[tx]] <- liftE (altTypes (peEnv pe) t (Unbox m (Var z) x e))
       UnboxLazy (Var z) x <$> percE (bind pe [(x,tx)]) (owned `S.union` ownedOf [(x,tx)]) e
percE' pe owned expr
  | Just e <- knownValue expr
  = percE pe owned e
percE' pe owned expr
  | Just ds <- destructOf expr
  = atomic pe owned (dsScrut ds) (restFv ds) $ \pe1 own1 z ->
    do t   <- typeOfV pe1 z
       case rebuild pe1 own1 expr t z of
         Just es -> percE' pe1 own1 (dsBuild ds (dsMode ds) z es)
         Nothing -> do tss <- liftE (altTypes (peEnv pe1) t expr)
                       (m,es) <- destruct pe1 own1 z expr [zip xs ts | ((xs,_),ts) <- zip (dsAlts ds) tss] (map snd (dsAlts ds))
                       return (dsBuild ds m z es)
percE' pe owned expr
  = case expr of
      Ret v -> do (k,[v']) <- useVals pe owned [(Owned,v)]
                  return (k (Ret v'))
      Let x t e1 e2
        -> do let live2 = fvE e2
                  own2  = owned `S.intersection` live2
                  own1  = owned `S.difference` live2
              e1' <- percE pe{ peBorrowed = peBorrowed pe `S.union` own2 } own1 e1
              e2' <- percE (bind pe [(x,t)]) (own2 `S.union` ownedOf [(x,t)]) e2
              return (Let x t e1' e2')
      Call f tys vs
        -> do let ms = paramModes (peEnv pe) f (length vs)
              case [(i,v) | (i,(Borrowed,v)) <- zip [0..] (zip ms vs), not (isAtom v)] of
                ((i,v):_) -> do t <- typeOfV pe v
                                s <- fresh "a"
                                percE' pe owned (Let s t (Ret v) (Call f tys (take i vs ++ [Var s] ++ drop (i+1) vs)))
                [] -> do (k,vs') <- useVals pe owned (zip ms vs)
                         postCall pe owned (zip ms vs) k (Call f tys vs') (resultOfCall pe f tys)
      Jump j vs
        -> do ms <- maybe (fail ("unknown join point " ++ show j)) return (M.lookup j (peJoins pe))
              (k,vs') <- useVals pe owned (zip ms vs)
              return (k (Jump j vs'))
      Join j ps e1 e2
        -> do e1' <- percE (paramEnv (peEnv pe) ps Nothing (peJoins pe)) (ownedParams ps) e1
              e2' <- percE' pe{ peJoins = M.insert j [m | (_,m,_) <- ps] (peJoins pe) } owned e2
              return (Join j ps e1' e2')
      App f vs
        -> do (k,f':vs') <- useVals pe owned [(Owned,v) | v <- f:vs]
              return (k (App f' vs'))
      Gen tvs e -> Gen tvs <$> percE' pe owned e
      Drop x e -> Drop x <$> percE' pe owned e
      CaseLit v alts def
        -> do alts' <- mapM (\(l,e) -> (,) l <$> percE pe owned e) alts
              def'  <- percE pe owned def
              return (CaseLit v alts' def')
      _ -> fail "unexpected destructuring form"

-- destructuring

-- make the scrutinee a variable or global
atomic :: PEnv -> VarSet -> Val -> VarSet -> (PEnv -> VarSet -> Val -> P Expr) -> P Expr
atomic pe owned v liveRest cont
  = case v of
      Var _  -> cont pe owned v
      Glob _ _ -> cont pe owned v
      _ -> do t <- typeOfV pe v
              s <- fresh "s"
              let ownV     = (owned `S.intersection` fvV v) `S.difference` liveRest
                  rest     = owned `S.difference` ownV
              (k,[v']) <- useVals pe{ peBorrowed = peBorrowed pe `S.union` rest } ownV [(Owned,v)]
              body <- cont (bind pe [(s,t)]) (rest `S.union` ownedOf [(s,t)]) (Var s)
              return (k (Let s t (Ret v') body))

-- an owned unboxed scrutinee that is still needed is rebuilt from the binders in each
-- alternative (which allocates nothing), so that destructuring can move its parts
rebuild :: PEnv -> VarSet -> Expr -> Ty -> Val -> Maybe [Expr]
rebuild pe owned expr t (Var z)
  | S.member z owned, not lazyPart, any (S.member z . fvE . snd) alts, Just mks <- valueCons expr t
  , and [not (S.member z (fvE e)) || all (`notElem` bindersE e) xs | (xs,e) <- alts]
  = Just [replaceE (M.singleton z (mk (map Var xs))) e | (mk,(xs,e)) <- zip mks alts]
  where
    alts     = maybe [] dsAlts (destructOf expr)
    lazyPart = maybe False (S.member z . snd) (peLazy pe)
rebuild _ _ _ _ _ = Nothing

-- destructuring a rebuilt value: the binders are replaced by its parts
knownValue :: Expr -> Maybe Expr
knownValue expr
  = case expr of
      Unpair _ (Pair v w) x y e -> reduce [(x,v),(y,w)] e
      CaseV _ (Inj i _ v) alts | i < length alts -> let (x,e) = alts !! i in reduce [(x,v)] e
      _ -> Nothing
  where
    reduce bs e
      | all (cheap . snd) bs, all (`S.notMember` S.unions (map (fvV . snd) bs)) (bindersE e)
      = Just (replaceE (M.fromList bs) e)
      | otherwise = Nothing
    cheap v = case v of
                Var _ -> True
                Pair a b -> cheap a && cheap b
                Inj _ _ a -> cheap a
                Pack _ _ a -> cheap a
                Unit -> True
                Lit _ -> True
                _ -> False

valueCons :: Expr -> Ty -> Maybe [[Val] -> Val]
valueCons expr t
  = case (expr,t) of
      (Unpair{}, _)             -> Just [foldr1 Pair]
      (CaseV{}, V s@(VSum ts))  -> Just [Inj i s . head | i <- [0 .. length ts - 1]]
      (Unpack _ _ tvs _ _, V s) -> Just [Pack s (map VVar tvs) . head]
      _ -> Nothing

-- free variables of a destructuring expression without its scrutinee
restFv :: Destruct -> VarSet
restFv ds = S.unions [fvE e `S.difference` S.fromList xs | (xs,e) <- dsAlts ds]

destruct :: PEnv -> VarSet -> Val -> Expr -> [[(Name,Ty)]] -> [Expr] -> P (Mode,[Expr])
destruct pe owned (Var z) _ binderss bodies
  | Just (lz,parts) <- peLazy pe, S.member z parts, S.member lz owned
  = do es <- mapM (lazyBody lz parts) (zip binderss bodies)
       return (Borrowed,es)
  where
    lazyBody lz parts (bs,e)
      | not (S.member lz (fvE e)) = eagerBody pe owned [lz] (bs,e)
      | otherwise = percE (bind pe{ peBorrowed = peBorrowed pe `S.union` ownedOf bs
                                  , peLazy = Just (lz, parts `S.union` S.fromList (map fst bs)) } bs) owned e
destruct pe owned z expr binderss bodies
  = do let zOwned = case z of
                      Var x -> S.member x owned
                      _     -> False
           zName  = case z of
                      Var x -> [x]
                      _     -> []
           deadIn e = not (any (`S.member` fvE e) zName)
           moveAll  = zOwned && not (isRead expr) && all deadIn bodies
       if moveAll
         then do let own = owned `S.difference` S.fromList zName
                 es <- mapM (\(bs,e) -> percE (bind pe bs) (own `S.union` ownedOf bs) e) (zip binderss bodies)
                 return (Owned,es)
         else do es <- mapM (borrowedBody pe owned zOwned zName expr) (zip binderss bodies)
                 return (Borrowed,es)

-- the binders are borrowed from the scrutinee, and from its root if that is an owned pointer
borrowedBody :: PEnv -> VarSet -> Bool -> [Name] -> Expr -> ([(Name,Ty)],Expr) -> P Expr
borrowedBody pe owned zOwned zName expr (bs,e)
  | zOwned && isJust (peLazy pe) = eagerBody pe owned zName (bs,e)
  | otherwise
  = do deps <- case zName of
                 [z] -> depsOf pe owned expr z bs
                 _   -> return []
       if zOwned && null deps then eagerBody pe owned zName (bs,e)
         else percE (bind pe{ peBorrowed = peBorrowed pe `S.union` ownedOf bs
                            , peDeps = M.union (M.fromList deps) (peDeps pe) } bs) owned e

-- the binders of a borrowed destructuring of `z` that are borrowed from an owned pointer
depsOf :: PEnv -> VarSet -> Expr -> Name -> [(Name,Ty)] -> P [(Name,Dep)]
depsOf pe owned expr z bs
  = do zDep <- if S.member z owned
                 then do t <- typeOfV pe (Var z)
                         return (if pointer t then Just (Dep z Alias) else Nothing)
                 else return (M.lookup z (peDeps pe))
       return (case zDep of
                 Nothing -> []
                 Just (Dep r k) -> [(x, Dep r (kindOf k i t)) | (i,(x,t)) <- zip [0::Int ..] bs, not (isTrivial t)])
  where
    pointer t = case t of
                  V v -> isPtr v
                  A _ -> True
    kindOf k i t
      = case (k,expr) of
          (Alias, _) | keepsPointer expr, A _ <- t -> Alias
          (Alias, Unbox{})     -> Part z []
          (Part y p, Unpair{}) -> Part y (p ++ [i == 1])
          _ -> Other

-- the live binders of an owned scrutinee that is not a pointer (or a lazy value) are
-- duplicated at the start of the body, and the scrutinee is dropped after that if it is dead
eagerBody :: PEnv -> VarSet -> [Name] -> ([(Name,Ty)],Expr) -> P Expr
eagerBody pe owned zName (bs,e)
  = do let live    = fvE e
           dupped  = [(x,t) | (x,t) <- bs, not (isTrivial t), S.member x live]
       renames <- mapM (\(x,_) -> (,) x <$> fresh "b") dupped
       let sub     = M.fromList renames
           e1      = renameE sub e
           zDead   = not (any (`S.member` live) zName)
           own     = (if zDead then owned `S.difference` S.fromList zName else owned)
                     `S.union` S.fromList (map snd renames)
           pe1     = bind pe (bs ++ [(x',t) | ((_,x'),(_,t)) <- zip renames dupped])
       body <- percE pe1 own e1
       let withDrop = if zDead then foldr Drop body zName else body
       return (foldr (\((x,x'),(_,t)) b -> Let x' t (Ret (Dup (Var x))) b) withDrop (zip renames dupped))

-- values

useVals :: PEnv -> VarSet -> [(Mode,Val)] -> P (K,[Val])
useVals pe owned mvs
  = do let ownedOcc = concat [occurrences v | (m,v) <- mvs, owning m]
           borrowedOcc = concat [occurrences v | (Borrowed,v) <- mvs]
           lastOcc  = M.fromList [(x,i) | (i,x) <- zip [0::Int ..] ownedOcc, S.member x owned, x `notElem` borrowedOcc]
       (k,_,vs) <- foldM (\(k,i,acc) (m,v) -> do (k',i',v') <- useVal pe lastOcc m i v
                                                 return (k . k', i', acc ++ [v'])) (id,0,[]) mvs
       return (k,vs)

-- variable occurrences in owned positions (closures capture their free variables)
occurrences :: Val -> [Name]
occurrences val
  = case val of
      Var x -> [x]
      Lam _ _ _ -> S.toList (fvV val)
      Dup _ -> []
      Fun _ -> []
      Glob _ _ -> []
      Unit -> []
      Lit _ -> []
      NoReuse _ -> []
      Inj _ _ _ -> children
      Inl _ _ -> children
      Inr _ _ -> children
      Pair _ _ -> children
      Fold _ _ -> children
      Box _ -> children
      Pack _ _ _ -> children
      OpenCon _ _ _ -> children
      TyApp _ _ -> children
      BoxAt _ _ -> children
      BoxIn _ _ -> children
  where
    children = concatMap occurrences (childrenV val)

useVal :: PEnv -> M.Map Name Int -> Mode -> Int -> Val -> P (K,Int,Val)
useVal pe lastOcc Borrowed i v = return (id,i,v)
useVal pe lastOcc Unique i val = useVal pe lastOcc Owned i val
useVal pe lastOcc Owned i val
  = case val of
      Var x -> return (id, i+1, if moves x i || trivial x then val else Dup val)
      Glob _ _ -> do t <- typeOfV pe val
                     return (id, i, if isTrivial t then val else Dup val)
      Lam ps r e
        -> do let caps = S.toList (fvV val)
                  idxs = zip caps [i..]
                  dups = [x | (x,j) <- idxs, not (moves x j), not (trivial x)]
              renames <- mapM (\x -> (,) x <$> fresh "c") dups
              let sub  = M.fromList renames
                  e1   = renameE sub e
                  caps' = [M.findWithDefault x x sub | x <- caps]
                  g    = M.union (M.fromList ([(x',t) | (x,x') <- renames, Just t <- [M.lookup x (peGamma pe)]] ++ [(x,V t) | (x,_,t) <- ps])) (peGamma pe)
                  inner = PEnv (peEnv pe) g S.empty Nothing M.empty M.empty
                  own  = S.fromList ([x | x <- caps', maybe False (not . isTrivial) (M.lookup x g)] ++ [x | (x,_,t) <- ps, not (isTrivial (V t))])
              e' <- percE inner own e1
              let k = foldr (\(x,x') k' -> Let x' (tyOf x) (Ret (Dup (Var x))) . k') id renames
              return (k, i + length caps, Lam ps r e')
      Dup _ -> return (id,i,val)
      Fun _ -> children
      Unit -> children
      Lit _ -> children
      NoReuse _ -> children
      Inj _ _ _ -> children
      Inl _ _ -> children
      Inr _ _ -> children
      Pair _ _ -> children
      Fold _ _ -> children
      Box _ -> children
      Pack _ _ _ -> children
      OpenCon _ _ _ -> children
      TyApp _ _ -> children
      BoxAt _ _ -> children
      BoxIn _ _ -> children
  where
    children = do let step :: Val -> StateT (K,Int) (M () Int) Val
                      step v = do (k,j) <- get
                                  (k',j',v') <- lift (useVal pe lastOcc Owned j v)
                                  put (k . k', j')
                                  return v'
                  (val',(k,i')) <- runStateT (descendV step val) (id,i)
                  return (k,i',val')
    moves x j = M.lookup x lastOcc == Just j
    trivial x = maybe False isTrivial (M.lookup x (peGamma pe))
    tyOf x = M.findWithDefault (V VUnit) x (peGamma pe)

-- after a call: drop owned variables that were only passed as borrowed arguments
postCall :: PEnv -> VarSet -> [(Mode,Val)] -> K -> Expr -> P VType -> P Expr
postCall pe owned mvs k call resTp
  = do let borrowedVars = S.fromList (concat [occurrences v | (Borrowed,v) <- mvs])
           drops = S.toList (owned `S.intersection` borrowedVars)
       if null drops then return (k call)
         else do r <- fresh "r"
                 t <- resTp
                 return (k (Let r (V t) call (foldr Drop (Ret (Var r)) drops)))

isAtom :: Val -> Bool
isAtom (Var _) = True
isAtom (Glob _ _) = True
isAtom (Lit _) = True
isAtom Unit = True
isAtom _ = False

resultOfCall :: PEnv -> Name -> [VType] -> P VType
resultOfCall pe f tys
  = case M.lookup f (envSigs (peEnv pe)) of
      Just (SigFun tvs _ r) -> return (inst tvs tys r)
      _ -> fail ("unknown function " ++ show f)

-- environment

bind :: PEnv -> [(Name,Ty)] -> PEnv
bind pe bs = pe{ peGamma = bindAll bs (peGamma pe) }

ownedOf :: [(Name,Ty)] -> VarSet
ownedOf bs = S.fromList [x | (x,t) <- bs, not (isTrivial t)]
