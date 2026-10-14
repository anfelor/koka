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
  contents of a box that is an alias of `z` (its pointer, from `[deref]`, `[unroll]`,
  `[case]` or `[unpack]`) are instead taken from a copy of the whole contents,
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
module Backend.Typed.Passes.Perceus( perceusProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( foldM )
import Data.Maybe( isJust )
import Data.Functor.Const( Const(..) )
import Data.List( isSuffixOf )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env(..), Gamma, envOf, bindAll, inferV, altTypes, paramModes )
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

typeOfV :: PEnv -> VVal -> P VType
typeOfV pe v = liftE (inferV (peEnv pe) (peGamma pe) v)

-- Discard variables using their types, expanding unboxed aggregates into moves.
dropNames :: PEnv -> [Name] -> VExpr -> P VExpr
dropNames pe xs e = foldM step e (reverse xs)
  where
    step body x = do t <- tyOfVar pe x
                     dropValue (fresh "d") x t body

-- expressions

percE :: PEnv -> VarSet -> VExpr -> P VExpr
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
                          dropNames pe dead expr'

-- does `expr` consume the live owned `z` while `x`, borrowed from it, is still needed?
consumedWith :: VExpr -> Name -> Name -> Bool
consumedWith expr z x
  = case expr of
      Ret _      -> True
      Call _ _ _ -> True
      App _ _    -> True
      Jump _ _   -> True
      Let _ _ _ e2 -> not (S.member z (fvE e2)) && S.member x (fvE e2)
      _ | Just ds <- destructAOf expr
        -> dsScrut ds == z && not (isRead expr) && not (any (S.member z . fvE . snd) (dsAlts ds))
      _ | Just ds <- destructVOf expr
        -> case dsScrut ds of
             Var y -> y == z && not (isRead expr) && not (any (S.member z . fvE . snd) (dsAlts ds))
             v     -> S.member z (fvV v)
      _ -> False

-- duplicate variables borrowed from an owned variable before it is consumed
dupDeps :: PEnv -> VarSet -> [Name] -> VExpr -> P (K,PEnv,VarSet,VExpr)
dupDeps pe owned xs expr
  = do renames <- mapM (\x -> (,) x <$> fresh "b") xs
       ts <- mapM (tyOfVar pe) xs
       k <- dupAs [(x,x',t) | ((x,x'),t) <- zip renames ts]
       return (k, bind pe [(x',t) | ((_,x'),t) <- zip renames ts], owned `S.union` S.fromList (map snd renames),
               renameE (M.fromList renames) expr)

-- the owned `z` is dead but the variables `deps` borrowed from it are still needed: they are
-- duplicated and `z` is dropped, except that the parts of the contents of a box alias `y` are
-- taken from a copy of the whole contents (see the top)
settle :: PEnv -> VarSet -> VExpr -> Name -> [(Name,Dep)] -> P VExpr
settle pe owned expr z deps
  = do let parts = [(x,y,path) | (x,Dep _ (Part y path)) <- deps]
       box <- case parts of
                ((_,y,_):_) -> do t <- tyOfVar pe y
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
                 return (k (Unbox Borrowed y p (Let q s (Ret (DupV (Var p))) (Drop y body))))
         _ -> do body <- percE pe1 own2 expr1
                 k <$> dropNames pe [z] body

-- bind variables to the parts of the product `v` at paths of `Unpair`s
unpairs :: Name -> [([Bool],Name,Ty)] -> P K
unpairs v xs
  = do let here  = [(x,t) | ([],x,t) <- xs]
           left  = [(path,x,t) | (False:path,x,t) <- xs]
           right = [(path,x,t) | (True:path,x,t) <- xs]
       k <- foldr (.) id <$> mapM (\(x,t) -> letVal x t (Var v)) here
       if null left && null right then return k
         else do a  <- fresh "u"
                 b  <- fresh "u"
                 kl <- unpairs a left
                 kr <- unpairs b right
                 return (k . Unpair Owned (Var v) a b . kl . kr)

-- Only unboxed values can be returned and bound by `let`.
letVal :: Name -> Ty -> VVal -> P K
letVal x (V s) v = return (Let x s (Ret v))
letVal _ (A _) _ = fail "cannot bind an unboxed value at a boxed type"

-- Boxed duplicates are bound through a pointer and immediately dereferenced.
dupAs :: [(Name,Name,Ty)] -> P K
dupAs xs = foldr (.) id <$> mapM dupOne xs
  where
    dupOne (x,x',V t) = return (Let x' t (Ret (DupV (Var x))))
    dupOne (x,x',A a) = letA (fresh "p") x' a (DupA x)

tyOfVar :: PEnv -> Name -> P Ty
tyOfVar pe x = maybe (fail ("unknown variable " ++ show x)) return (M.lookup x (peGamma pe))

percE' :: PEnv -> VarSet -> VExpr -> P VExpr
percE' pe owned (Unbox m z x e)
  | Just (lz,parts) <- peLazy pe, S.member z parts, S.member lz owned, S.member lz (fvE e)
  = do t <- tyOfVar pe z
       [[tx]] <- liftE (altTypes (peEnv pe) t (Unbox m z x e))
       UnboxLazy z x <$> percE (bind pe [(x,tx)]) (owned `S.union` ownedOf [(x,tx)]) e
percE' pe owned expr
  | Just e <- knownValue expr
  = percE pe owned e
percE' pe owned expr
  | Just ds <- destructAOf expr
  = do let z = dsScrut ds
       t <- tyOfVar pe z
       tss <- liftE (altTypes (peEnv pe) t expr)
       (m,es) <- destruct pe owned (Just z) expr [zip xs ts | ((xs,_),ts) <- zip (dsAlts ds) tss] (map snd (dsAlts ds))
       return (dsBuild ds m z es)
percE' pe owned expr
  | Just ds <- destructVOf expr
  = atomic pe owned (dsScrut ds) (restFv ds) $ \pe1 own1 z ->
    do t   <- typeOfV pe1 z
       case rebuild pe1 own1 expr t z of
         Just es -> percE' pe1 own1 (dsBuild ds (dsMode ds) z es)
         Nothing -> do tss <- liftE (altTypes (peEnv pe1) (V t) expr)
                       (m,es) <- destruct pe1 own1 (valName z) expr [zip xs ts | ((xs,_),ts) <- zip (dsAlts ds) tss] (map snd (dsAlts ds))
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
              e2' <- percE (bind pe [(x,V t)]) (own2 `S.union` ownedOf [(x,V t)]) e2
              return (Let x t e1' e2')
      Call f tys vs
        -> do let ms = paramModes (peEnv pe) f (length vs)
              case [(i,v) | (i,(Borrowed,v)) <- zip [0..] (zip ms vs), not (isAtom v)] of
                ((i,v):_) -> do t <- typeOfV pe v
                                s <- fresh "a"
                                k <- letVal s (V t) v
                                percE' pe owned (k (Call f tys (take i vs ++ [Var s] ++ drop (i+1) vs)))
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
        -> do let move = S.member f owned && all (S.notMember f . fvV) vs
              f' <- if move then return f else fresh "f"
              kf <- if move then return id
                      else do t <- tyOfVar pe f
                              dupAs [(f,f',t)]
              (k,vs') <- useVals pe (if move then S.delete f owned else owned) [(Owned,v) | v <- vs]
              return (kf (k (App f' vs')))
      Gen tvs e -> Gen tvs <$> percE' pe owned e
      Drop x e -> Drop x <$> percE' pe owned e
      Free r e -> Free r <$> percE' pe owned e
      CaseLit v alts def
        -> do alts' <- mapM (\(l,e) -> (,) l <$> percE pe owned e) alts
              def'  <- percE pe owned def
              return (CaseLit v alts' def')
      _ -> fail "unexpected destructuring form"

-- destructuring

-- make the scrutinee a variable or global
atomic :: PEnv -> VarSet -> VVal -> VarSet -> (PEnv -> VarSet -> VVal -> P VExpr) -> P VExpr
atomic pe owned v liveRest cont
  = case v of
      Var _  -> cont pe owned v
      Glob _ _ -> cont pe owned v
      _ -> do t <- typeOfV pe v
              s <- fresh "s"
              let ownV     = (owned `S.intersection` fvV v) `S.difference` liveRest
                  rest     = owned `S.difference` ownV
              (k,[v']) <- useVals pe{ peBorrowed = peBorrowed pe `S.union` rest } ownV [(Owned,v)]
              body <- cont (bind pe [(s,V t)]) (rest `S.union` ownedOf [(s,V t)]) (Var s)
              kv <- letVal s (V t) v'
              return (k (kv body))

-- an owned unboxed scrutinee that is still needed is rebuilt from the binders in each
-- alternative (which allocates nothing), so that destructuring can move its parts
rebuild :: PEnv -> VarSet -> VExpr -> VType -> VVal -> Maybe [VExpr]
rebuild pe owned expr t (Var z)
  | S.member z owned, not lazyPart, any (S.member z . fvE . snd) alts, Just mks <- valueCons expr t
  , and [not (S.member z (fvE e)) || all (`notElem` bindersE e) xs | (xs,e) <- alts]
  = Just [replaceE (M.singleton z (mk (map Var xs))) e | (mk,(xs,e)) <- zip mks alts]
  where
    alts     = maybe [] dsAlts (destructVOf expr)
    lazyPart = maybe False (S.member z . snd) (peLazy pe)
rebuild _ _ _ _ _ = Nothing

-- destructuring a rebuilt value: the binders are replaced by its parts
knownValue :: VExpr -> Maybe VExpr
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
                UnitV -> True
                Lit _ -> True
                _ -> False

valueCons :: VExpr -> VType -> Maybe [[VVal] -> VVal]
valueCons expr t
  = case (expr,t) of
      (Unpair{}, _)          -> Just [foldr1 Pair]
      (CaseV{}, s@(VSum ts))  -> Just [Inj i s . head | i <- [0 .. length ts - 1]]
      (Unpack _ _ tvs _ _, s) -> Just [Pack s (map AVar tvs) . head]
      _ -> Nothing

-- free variables of a destructuring expression without its scrutinee
restFv :: Destruct v -> VarSet
restFv ds = S.unions [fvE e `S.difference` S.fromList xs | (xs,e) <- dsAlts ds]

destruct :: PEnv -> VarSet -> Maybe Name -> VExpr -> [[(Name,Ty)]] -> [VExpr] -> P (Mode,[VExpr])
destruct pe owned (Just z) _ binderss bodies
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
                      Just x -> S.member x owned
                      _     -> False
           zName  = case z of
                      Just x -> [x]
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
borrowedBody :: PEnv -> VarSet -> Bool -> [Name] -> VExpr -> ([(Name,Ty)],VExpr) -> P VExpr
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
depsOf :: PEnv -> VarSet -> VExpr -> Name -> [(Name,Ty)] -> P [(Name,Dep)]
depsOf pe owned expr z bs
  = do zDep <- if S.member z owned
                 then do t <- tyOfVar pe z
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
eagerBody :: PEnv -> VarSet -> [Name] -> ([(Name,Ty)],VExpr) -> P VExpr
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
       withDrop <- if zDead then dropNames pe zName body else return body
       k <- dupAs [(x,x',t) | ((x,x'),(_,t)) <- zip renames dupped]
       return (k withDrop)

-- values

useVals :: PEnv -> VarSet -> [(Mode,VVal)] -> P (K,[VVal])
useVals pe owned mvs
  = do let ownedOcc = concat [occurrences v | (m,v) <- mvs, owning m]
           borrowedOcc = concat [occurrences v | (Borrowed,v) <- mvs]
           lastOcc  = M.fromList [(x,i) | (i,x) <- zip [0::Int ..] ownedOcc, S.member x owned, x `notElem` borrowedOcc]
       (k,_,vs) <- foldM (\(k,i,acc) (m,v) -> do (k',i',v') <- useVal pe lastOcc m i v
                                                 return (k . k', i', acc ++ [v'])) (id,0,[]) mvs
       return (k,vs)

-- Variable occurrences in owned positions; closures capture their free variables.
occurrences :: VVal -> [Name]
occurrences val = case val of
  Var x -> [x]
  DupV _ -> []
  _ -> getConst (descendV (Const . occurrencesA) (Const . occurrences) val)

occurrencesA :: AVal -> [Name]
occurrencesA val = case val of
  Lam{} -> S.toList (fvA val)
  DupA _ -> []
  _ -> getConst (descendA (Const . (:[])) (Const . occurrencesA) (Const . occurrences) val)

useVal :: PEnv -> M.Map Name Int -> Mode -> Int -> VVal -> P (K,Int,VVal)
useVal _ _ Borrowed i v = return (id,i,v)
useVal pe lastOcc Unique i v = useVal pe lastOcc Owned i v
useVal pe lastOcc Owned i val
  = case val of
      Var x -> return (id,i+1,if M.lookup x lastOcc == Just i || maybe False isTrivial (M.lookup x (peGamma pe)) then val else DupV val)
      Glob _ _ -> do t <- typeOfV pe val
                     return (id,i,if isTrivial (V t) then val else DupV val)
      DupV _ -> return (id,i,val)
      _ -> useChildren pe lastOcc i (descendV (stepA pe lastOcc) (stepV pe lastOcc) val)

useA :: PEnv -> M.Map Name Int -> Int -> AVal -> P (K,Int,AVal)
useA pe lastOcc i val
  = case val of
      Lam ps r e
        -> do let caps = S.toList (fvA val)
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
              k <- dupAs [(x,x',tyOf x) | (x,x') <- renames]
              return (k, i + length caps, Lam ps r e')
      DupA _ -> return (id,i,val)
      _ -> useChildren pe lastOcc i (descendA stepName (stepA pe lastOcc) (stepV pe lastOcc) val)
  where
    moves x j = M.lookup x lastOcc == Just j
    trivial x = maybe False isTrivial (M.lookup x (peGamma pe))
    tyOf x = M.findWithDefault (V VUnit) x (peGamma pe)
    stepName :: Name -> StateT (K,Int) (M () Int) Name
    stepName x = do (k,j) <- get
                    put (k,j+1)
                    return x

useChildren :: PEnv -> M.Map Name Int -> Int -> StateT (K,Int) (M () Int) a -> P (K,Int,a)
useChildren _ _ i action
  = do (v,(k,j)) <- runStateT action (id,i)
       return (k,j,v)

stepV :: PEnv -> M.Map Name Int -> VVal -> StateT (K,Int) (M () Int) VVal
stepV pe occ v
  = do (k,i) <- get
       (k',j,w) <- lift (useVal pe occ Owned i v)
       put (k . k',j)
       return w

stepA :: PEnv -> M.Map Name Int -> AVal -> StateT (K,Int) (M () Int) AVal
stepA pe occ v
  = do (k,i) <- get
       (k',j,w) <- lift (useA pe occ i v)
       put (k . k',j)
       return w

valName :: VVal -> Maybe Name
valName (Var x) = Just x
valName _ = Nothing

-- after a call: drop owned variables that were only passed as borrowed arguments
postCall :: PEnv -> VarSet -> [(Mode,VVal)] -> K -> VExpr -> P VType -> P VExpr
postCall pe owned mvs k call resTp
  = do let borrowedVars = S.fromList (concat [occurrences v | (Borrowed,v) <- mvs])
           drops = S.toList (owned `S.intersection` borrowedVars)
       if null drops then return (k call)
         else do r <- fresh "r"
                 t <- resTp
                 body <- dropNames pe drops (Ret (Var r))
                 return (k (Let r t call body))

isAtom :: VVal -> Bool
isAtom (Var _) = True
isAtom (Glob _ _) = True
isAtom (Lit _) = True
isAtom UnitV = True
isAtom _ = False

resultOfCall :: PEnv -> Name -> [AType] -> P VType
resultOfCall pe f tys
  = case M.lookup f (envSigs (peEnv pe)) of
      Just (SigFun tvs _ r) -> return (inst tvs tys r)
      _ -> fail ("unknown function " ++ show f)

-- environment

bind :: PEnv -> [(Name,Ty)] -> PEnv
bind pe bs = pe{ peGamma = bindAll bs (peGamma pe) }

ownedOf :: [(Name,Ty)] -> VarSet
ownedOf bs = S.fromList [x | (x,t) <- bs, not (isTrivial t)]
