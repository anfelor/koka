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
  borrowed in `e1`; a `[let-yield]` is a `let` whose continuation is one of two branches,
  and `x` is only bound in the one where no effect yields.

  Destructuring a dead owned variable moves its ownership to the binders
  (mode owned). Otherwise the binders are borrowed from the scrutinee (mode
  borrowed). A borrowed variable whose path passes through an owned variable `z` (the
  longest such, its *owner*: see `Syntax.Path`) is only duplicated where `z` is given up while
  it is still needed:
  - where `z` is consumed (passed on, or moved by a `let` or a destructuring), it is
    duplicated before;
  - where `z` is dead and not a pointer, its parts that are bound take over its ownership
    (`z.fst` and `z.snd` once `z` is destructured);
  - where `z` is a dead pointer, a live alias of `z` (its pointer at a boxed type, from
    `[deref]`, `[unroll]`, `[case-a]` or `[split-a]`) takes over its ownership. Otherwise the
    contents of a box `y` on the way to the variable (an alias of `z` or `z` itself) are
    taken from the box, `dup y.contents; drop y`, which drop specialization turns into a
    move (and `y` into a reuse credit) if `y` is unique. Any other variable is duplicated,
    and `z` is dropped.
  So a test such as `is-red(r)` does not duplicate `r`, and a nested pattern reuses the
  inner block where the outer value is dead. Reading the contents of a box is always
  borrowed, while reading a dead owned scalar consumes it (`[unscalar]`). Duplicates keep
  their names (`[dup]`), so the paths always show where a variable comes from.

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
import Data.Functor.Const( Const(..) )
import Data.List( isSuffixOf )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env(..), Gamma, envOf, bindAll, inferV, altTypes, paramModes, trivialTy )
import Backend.Typed.Types( inst, isPtr )

type VarSet = S.Set Path

-- `peLazy`: in `lazy-eval-locked`, the lazy value, whose parts are borrowed from it;
-- `peJoins`: the parameter modes of the join points in scope
data PEnv = PEnv{ peEnv :: Env, peGamma :: Gamma, peBorrowed :: VarSet, peLazy :: Maybe Path, peJoins :: M.Map Name [Mode] }

type P a = M () NameSupply a

fresh :: String -> P Path
fresh s = state (freshPathFrom ("rc" ++ s))

-- programs

perceusProgram :: Program -> (Program,[String])
perceusProgram prog
  = let env = envOf prog
        run d = case evalM (perceusDef env d) () (freshFor d) of
                  Right d' -> (d', [])
                  Left err -> (d, [show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs prog))
    in (prog{ progDefs = defs }, concat errs)

perceusDef :: Env -> Def -> P Def
perceusDef env def
  = case def of
      DefFun f tvs args res body
        -> do let lz = case args of
                         ((x,m,_):_) | owning m, "lazy-eval-locked" `isSuffixOf` nameLocal f -> Just x
                         _ -> Nothing
              body' <- percE (paramEnv env args lz M.empty) (ownedParams env args) body
              return (DefFun f tvs args res body')
      DefVal x tvs t body
        -> DefVal x tvs t <$> percE (PEnv env M.empty S.empty Nothing M.empty) S.empty body

-- the environment of the body of a function or join point
paramEnv :: Env -> [(Path,Mode,VType)] -> Maybe Path -> M.Map Name [Mode] -> PEnv
paramEnv env ps lz js = PEnv env (M.fromList [(x,V t) | (x,_,t) <- ps]) (S.fromList [x | (x,Borrowed,_) <- ps]) lz js

ownedParams :: Env -> [(Path,Mode,VType)] -> VarSet
ownedParams env ps = S.fromList [x | (x,m,t) <- ps, owning m, not (trivialTy env (V t))]

typeOfV :: PEnv -> VVal -> P VType
typeOfV pe v = liftE (inferV (peEnv pe) (peGamma pe) v)

-- Discard variables using their types, expanding unboxed aggregates into moves. An
-- aggregate whose parts are bound is discarded by discarding its parts. A product
-- may have only one projection in scope, so expand its drop to cover both parts.
dropNames :: PEnv -> [Path] -> VExpr -> P VExpr
dropNames pe xs e = foldM step e (reverse xs)
  where
    step body x = do t <- tyOfVar pe x
                     let discard = dropValue (trivialTy (peEnv pe)) (fresh "d") (scopeOf (M.keys (peGamma pe))) x t body
                     case (t,partsOf pe x) of
                       (V VProd{},_) -> discard
                       (_,ps@(_:_)) | not (pointer t) -> dropNames pe ps body
                       _ -> discard

-- the parts of a variable that are bound and not of a trivial type
partsOf :: PEnv -> Path -> [Path]
partsOf pe z
  = [x | (x,t) <- takeWhile ((`within` z) . fst) (M.toAscList (M.dropWhileAntitone (<= z) (peGamma pe)))
       , length (stepsFrom z x) == 1, not (trivialTy (peEnv pe) t)]

-- the owner of a borrowed variable (see the top); the parts of the lazy value under
-- evaluation have none
ownerOf :: PEnv -> VarSet -> Path -> Maybe Path
ownerOf pe owned x
  | S.member x owned || maybe True (trivialTy (peEnv pe)) (M.lookup x (peGamma pe)) = Nothing
  | otherwise = case [z | z <- reverse (prefixes x), S.member z owned] of
                  (z:_) | Just z /= peLazy pe -> Just z
                  _ -> Nothing

pointer :: Ty -> Bool
pointer t
  = case t of
      V v -> isPtr v
      A _ -> True

-- the steps that keep the pointer of a boxed value (the binder is an alias)
keepsPtr :: Step -> Bool
keepsPtr s
  = case s of
      SDeref -> True
      SRoll -> True
      SInjA _ -> True
      SRest -> True
      SLo -> True
      SHi -> True
      _ -> False

-- expressions

percE :: PEnv -> VarSet -> VExpr -> P VExpr
-- Materialize a scheduled borrowed selection before settling its owner. The
-- selected binding can then survive the transfer, rather than being read back
-- from a backing snapshot afterward. A scalar read similarly copies trivial
-- contents into an independent root before its owner is settled. Only leading
-- reads are handled here; neither is moved across calls or guards.
percE pe owned expr@Unscalar{}
  = percE' pe owned expr
percE pe owned expr@(Deref _ (Var _) x (Unscalar _ z _ _))
  | x == z
  = percE' pe owned expr
percE pe owned expr
  | Just ds <- destructVOf expr, productProjection expr
  , dsMode ds == Borrowed, Var _ <- dsScrut ds
  = percE' pe owned expr
percE pe owned expr
  = do let live = fvE expr
           deps = [(x,z) | x <- S.toList live, Just z <- [ownerOf pe owned x]]
       case [z | (_,z) <- deps, not (S.member z live)] of
         (z:_) -> settle pe owned expr z [x | (x,z') <- deps, z' == z]
         [] -> case [x | (x,z) <- deps, consumedWith expr z x] of
                 xs@(_:_) -> percE pe (S.union owned (S.fromList xs)) expr >>= dupAll pe xs
                 [] -> do let dead = S.toList (owned `S.difference` live)
                          expr' <- percE' pe (owned `S.intersection` live) expr
                          dropNames pe dead expr'

-- does `expr` consume the live owned `z` while `x`, borrowed from it, is still needed?
consumedWith :: VExpr -> Path -> Path -> Bool
consumedWith expr z x
  = case expr of
      Proj{}     -> False
      Ret _      -> True
      Call _ _ _ -> True
      App _ _    -> True
      Jump _ _   -> True
      Let _ _ _ e2 -> not (S.member z (fvE e2)) && S.member x (fvE e2)
      LetYield _ _ _ e2 e3 -> let live = fvE e2 `S.union` fvE e3 in not (S.member z live) && S.member x live
      _ | Just ds <- destructAOf expr
        -> dsScrut ds == z && not (isRead expr) && not (any (S.member z . fvE . snd) (dsAlts ds))
      _ | Just ds <- destructVOf expr
        -> case dsScrut ds of
             Var y -> y == z && not (isRead expr) && not (any (S.member z . fvE . snd) (dsAlts ds))
             v     -> S.member z (fvV v)
      _ -> False

-- The owned `z` is dead but the variables `xs` borrowed from it are still needed (see the
-- top): its bound parts, its shortest live alias or the contents of a box take over its
-- ownership, and the other variables are duplicated.
settle :: PEnv -> VarSet -> VExpr -> Path -> [Path] -> P VExpr
settle pe owned expr z xs
  = do t <- tyOfVar pe z
       let owned' = S.delete z owned
       case [x | x <- xs, all keepsPtr (stepsFrom z x)] of
         _ | V v@VProd{} <- t -> do
               let fields = [f | f@(_,_,s) <- fieldsAt z v, not (trivialTy (peEnv pe) (V s))]
                   missing = [f | f@(y,_,_) <- fields, M.notMember y (peGamma pe)]
               if null missing
                 then percE pe (S.union owned' (S.fromList [y | (y,_,_) <- fields])) expr
                 else percE pe owned (projectAll M.empty Borrowed z missing expr)
           | not (pointer t) -> percE pe (S.union owned' (S.fromList (partsOf pe z))) expr
         (y:ys) -> percE pe (S.insert (foldr shorter y ys) owned') expr
         [] -> case [p | x <- xs, Just p <- [contentsOn x]] of
                 (p@(Path _ ss):_) -> do let y = Path (pathRoot z) (init ss)
                                             others = [x | x <- xs, not (x `within` p)]
                                         percE pe (S.insert p (S.union owned' (S.fromList others))) expr >>= dupAll pe (others ++ [p]) . Drop y
                 [] -> percE pe (S.union owned' (S.fromList xs)) expr >>= dropNames pe [z] >>= dupAll pe xs
  where
    shorter a b = if length (stepsFrom z a) <= length (stepsFrom z b) then a else b
    pathRoot (Path r _) = r
    -- the contents of an alias of `z` (or of `z`) on the way to `x`
    contentsOn x = case break (not . keepsPtr) (stepsFrom z x) of
                     (as,SContents:_) -> Just (foldl child z (as ++ [SContents]))
                     _ -> Nothing

-- Only unboxed values can be returned and bound by `let`.
letVal :: Path -> Ty -> VVal -> P K
letVal x (V s) v = return (Let x s (Ret v))
letVal _ (A _) _ = fail "cannot bind an unboxed value at a boxed type"

tyOfVar :: PEnv -> Path -> P Ty
tyOfVar pe x = maybe (fail ("unknown variable " ++ show x)) return (M.lookup x (peGamma pe))

percE' :: PEnv -> VarSet -> VExpr -> P VExpr
percE' pe owned (Unbox m z x e)
  | Just lz <- peLazy pe, z `within` lz, S.member lz owned, S.member lz (fvE e)
  = do t <- tyOfVar pe z
       [[tx]] <- liftE (altTypes (peEnv pe) t (Unbox m z x e))
       -- the taken contents are a root (see `[unbox-lazy]`)
       y <- fresh "l"
       UnboxLazy z y <$> percE (bind pe [(y,tx)]) (owned `S.union` ownedOf pe [(y,tx)]) (renamePath x y e)
-- the binder is a copy of trivial contents, so a dead owned scalar is consumed by the read
percE' pe owned expr@(Unscalar _ z x e)
  = do t <- tyOfVar pe z
       [[tx]] <- liftE (altTypes (peEnv pe) t expr)
       let move = S.member z owned && S.notMember z (fvE e)
           owned' = if move then S.delete z owned else owned
       Unscalar (if move then Owned else Borrowed) z x <$> percE (bind pe [(x,tx)]) owned' e
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
    do t <- typeOfV pe1 z
       let expr' = nameParts (dsBuild ds (dsMode ds) z (map snd (dsAlts ds)))
       case destructVOf expr' of
         Just ds' -> do tss <- liftE (altTypes (peEnv pe1) (V t) expr')
                        (m,es) <- destruct pe1 own1 (valName z) expr' [zip xs ts | ((xs,_),ts) <- zip (dsAlts ds') tss] (map snd (dsAlts ds'))
                        return (dsBuild ds' m z es)
         Nothing -> fail "expected a value destructuring"
percE' pe owned expr
  = case expr of
      Ret v -> do (k,[v']) <- useVals pe owned [(Owned,v)]
                  return (k (Ret v'))
      Let x t e1 e2
        -> do let live2 = fvE e2
                  own2  = owned `S.intersection` live2
                  own1  = owned `S.difference` live2
              e1' <- percE pe{ peBorrowed = peBorrowed pe `S.union` own2 } own1 e1
              e2' <- percE (bind pe [(x,V t)]) (own2 `S.union` ownedOf pe [(x,V t)]) e2
              return (hoistdupAll (\e1'' -> Let x t e1'' e2') e1')
      -- like a `let`, whose continuation is one of two branches; `x` is only bound in `e2`
      LetYield x t e1 e2 e3
        -> do let live = fvE e2 `S.union` fvE e3
                  own2 = owned `S.intersection` live
                  own1 = owned `S.difference` live
              e1' <- percE pe{ peBorrowed = peBorrowed pe `S.union` own2 } own1 e1
              e2' <- percE (bind pe [(x,V t)]) (own2 `S.union` ownedOf pe [(x,V t)]) e2
              e3' <- percE pe own2 e3
              return (hoistdupAll (\e1'' -> LetYield x t e1'' e2' e3') e1')
      Yielded _ -> return expr
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
        -> do e1' <- percE (paramEnv (peEnv pe) ps Nothing (peJoins pe)) (ownedParams (peEnv pe) ps) e1
              e2' <- percE' pe{ peJoins = M.insert j [m | (_,m,_) <- ps] (peJoins pe) } owned e2
              return (Join j ps e1' e2')
      App f vs
        -> do let move = S.member f owned && all (S.notMember f . fvV) vs
                  kf = if move then id else Dup f
              (k,vs') <- useVals pe (if move then S.delete f owned else owned) [(Owned,v) | v <- vs]
              return (kf (k (App f vs')))
      Gen tvs e -> Gen tvs <$> percE' pe owned e
      Drop x e -> Drop x <$> percE' pe owned e
      Free r e -> Free r <$> percE' pe owned e
      Dup x e -> percE pe (S.insert x owned) e >>= dupAll pe [x]
      CaseLit v alts def
        -> do alts' <- mapM (\(l,e) -> (,) l <$> percE pe owned e) alts
              def'  <- percE pe owned def
              return (CaseLit v alts' def')
      _ -> fail "unexpected destructuring form"

-- duplicate variables in place
dupAll :: PEnv -> [Path] -> VExpr -> P VExpr
dupAll pe xs e = ($ e) <$> dupK pe xs

dupK :: PEnv -> [Path] -> P K
dupK pe xs = compose <$> mapM step xs
  where
    step x = do t <- tyOfVar pe x
                dupValue (trivialTy (peEnv pe)) (fresh "u") (scopeOf (M.keys (peGamma pe))) x t

-- the dups at the start of the bound expression of a `let` come before the `let`, so that
-- it binds a value where it can (such as a unique one)
hoistdupAll :: (VExpr -> VExpr) -> VExpr -> VExpr
hoistdupAll k (Dup x e) = Dup x (hoistdupAll k e)
hoistdupAll k (Let x VUnit bound e)
  | retains bound = Let x VUnit bound (hoistdupAll k e)
hoistdupAll k e = k e

-- The unit-valued part of a derived duplication, with no calls or allocations.
retains :: VExpr -> Bool
retains (Ret UnitV) = True
retains (Dup _ e) = retains e
retains (Let _ VUnit e1 e2) = retains e1 && retains e2
retains e | Just ds <- destructVOf e, dsMode ds == Borrowed = all (retains . snd) (dsAlts ds)
retains _ = False

productProjection :: VExpr -> Bool
productProjection Proj{} = True
productProjection _ = False

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
              body <- cont (bind pe [(s,V t)]) (rest `S.union` ownedOf pe [(s,V t)]) (Var s)
              kv <- letVal s (V t) v'
              return (k (kv body))

-- free variables of a destructuring expression without its scrutinee
restFv :: Destruct v -> VarSet
restFv ds = S.unions [fvE e `S.difference` S.fromList xs | (xs,e) <- dsAlts ds]

destruct :: PEnv -> VarSet -> Maybe Path -> VExpr -> [[(Path,Ty)]] -> [VExpr] -> P (Mode,[VExpr])
destruct pe owned (Just z) _ binderss bodies
  | Just lz <- peLazy pe, z `within` lz, S.member lz owned
  = do es <- mapM (lazyBody lz) (zip binderss bodies)
       return (Borrowed,es)
  where
    lazyBody lz (bs,e)
      | not (S.member lz (fvE e)) = eagerBody pe owned [lz] (bs,e)
      | otherwise = percE (bind pe{ peBorrowed = peBorrowed pe `S.union` ownedOf pe bs } bs) owned e
destruct pe owned z expr binderss bodies
  = do let zOwned = case z of
                      Just x -> S.member x owned
                      _     -> False
           zName  = case z of
                      Just x -> [x]
                      _     -> []
           deadIn e = not (any (`S.member` fvE e) zName)
           moveAll  = zOwned && not (isRead expr) && not (productProjection expr) && all deadIn bodies
       if moveAll
         then do let own = owned `S.difference` S.fromList zName
                 es <- mapM (\(bs,e) -> percE (bind pe bs) (own `S.union` ownedOf pe bs) e) (zip binderss bodies)
                 return (Owned,es)
         else do es <- mapM (borrowedBody pe owned) (zip binderss bodies)
                 return (Borrowed,es)

-- the binders are borrowed from the scrutinee (and from its owner)
borrowedBody :: PEnv -> VarSet -> ([(Path,Ty)],VExpr) -> P VExpr
borrowedBody pe owned (bs,e) = percE (bind pe{ peBorrowed = peBorrowed pe `S.union` ownedOf pe bs } bs) owned e

-- the live binders of an owned scrutinee of the lazy value are duplicated at the start of the
-- body, and the scrutinee is dropped after that if it is dead
eagerBody :: PEnv -> VarSet -> [Path] -> ([(Path,Ty)],VExpr) -> P VExpr
eagerBody pe owned zName (bs,e)
  = do let live    = fvE e
           dupped  = [x | (x,t) <- bs, not (trivialTy (peEnv pe) t), S.member x live]
           zDead   = not (any (`S.member` live) zName)
           own     = (if zDead then owned `S.difference` S.fromList zName else owned)
                     `S.union` S.fromList dupped
       body <- percE (bind pe bs) own e
       withDrop <- if zDead then dropNames pe zName body else return body
       dupAll (bind pe bs) dupped withDrop

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
occurrences :: VVal -> [Path]
occurrences val = case val of
  Var x -> [x]
  DupV _ -> []   -- a global
  _ -> getConst (descendV (Const . occurrencesA) (Const . occurrences) val)

occurrencesA :: AVal -> [Path]
occurrencesA val = case val of
  Lam{} -> S.toList (fvA val)
  _ -> getConst (descendA (Const . (:[])) (Const . occurrencesA) (Const . occurrences) val)

useVal :: PEnv -> M.Map Path Int -> Mode -> Int -> VVal -> P (K,Int,VVal)
useVal _ _ Borrowed i v = return (id,i,v)
useVal pe lastOcc Unique i v = useVal pe lastOcc Owned i v
useVal pe lastOcc Owned i val
  = case val of
      Var x -> do k <- if M.lookup x lastOcc == Just i then return id else dupK pe [x]
                  return (k,i+1,val)
      Glob _ _ -> do t <- typeOfV pe val
                     return (id,i,if trivialTy (peEnv pe) (V t) then val else DupV val)
      DupV _ -> return (id,i,val)
      _ -> useChildren pe lastOcc i (descendV (stepA pe lastOcc) (stepV pe lastOcc) val)

useA :: PEnv -> M.Map Path Int -> Int -> AVal -> P (K,Int,AVal)
useA pe lastOcc i val
  = case val of
      Lam ps r e
        -> do let caps = S.toList (fvA val)
                  idxs = zip caps [i..]
                  dups = [x | (x,j) <- idxs, not (moves x j), not (trivial x)]
              let g    = M.union (M.fromList [(x,V t) | (x,_,t) <- ps]) (peGamma pe)
                  inner = PEnv (peEnv pe) g S.empty Nothing M.empty
                  own  = S.fromList ([x | x <- caps, maybe False (not . trivialTy (peEnv pe)) (M.lookup x g)] ++ [x | (x,_,t) <- ps, not (trivialTy (peEnv pe) (V t))])
              e' <- percE inner own e
              k <- dupK pe dups
              return (k, i + length caps, Lam ps r e')
      _ -> useChildren pe lastOcc i (descendA stepName (stepA pe lastOcc) (stepV pe lastOcc) val)
  where
    moves x j = M.lookup x lastOcc == Just j
    trivial x = maybe False (trivialTy (peEnv pe)) (M.lookup x (peGamma pe))
    stepName :: Path -> StateT (K,Int) (M () NameSupply) Path
    stepName x = do (k,j) <- get
                    put (k,j+1)
                    return x

useChildren :: PEnv -> M.Map Path Int -> Int -> StateT (K,Int) (M () NameSupply) a -> P (K,Int,a)
useChildren _ _ i action
  = do (v,(k,j)) <- runStateT action (id,i)
       return (k,j,v)

stepV :: PEnv -> M.Map Path Int -> VVal -> StateT (K,Int) (M () NameSupply) VVal
stepV pe occ v
  = do (k,i) <- get
       (k',j,w) <- lift (useVal pe occ Owned i v)
       put (k . k',j)
       return w

stepA :: PEnv -> M.Map Path Int -> AVal -> StateT (K,Int) (M () NameSupply) AVal
stepA pe occ v
  = do (k,i) <- get
       (k',j,w) <- lift (useA pe occ i v)
       put (k . k',j)
       return w

valName :: VVal -> Maybe Path
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

bind :: PEnv -> [(Path,Ty)] -> PEnv
bind pe bs = pe{ peGamma = bindAll bs (peGamma pe) }

ownedOf :: PEnv -> [(Path,Ty)] -> VarSet
ownedOf pe bs = S.fromList [x | (x,t) <- bs, not (trivialTy (peEnv pe) t)]
