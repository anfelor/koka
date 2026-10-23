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
    copied before. A use of an alias of `z` (see below) needs `z` itself (`needs`), so `z`
    stays owned and the consumer gets a copy of `z` instead;
  - where `z` is dead and not a pointer, its parts that are bound take over its ownership
    (`z.fst` and `z.snd` once `z` is destructured);
  - where `z` is a dead pointer, a live alias of `z` (its pointer at a boxed type, from
    `[deref]`, `[unroll]`, `[case-a]` or `[split-a]`) takes over its ownership. Otherwise the
    variables are copied and `z` is dropped. Where a variable is in the contents of a box `y`
    on the way to it (an alias of `z` or `z` itself), `y` is dropped instead, which drop
    specialization turns into a move of the copied parts (and `y` into a reuse credit) if `y`
    is unique.
  So a test such as `is-red(r)` does not duplicate `r`, and a nested pattern reuses the
  inner block where the outer value is dead. Reading the contents of a box is always
  borrowed, while reading a dead owned scalar consumes it (`[unscalar]`).

  A copy of a variable is a new root (`[dup]`) that replaces it in the code that takes the
  copy, which uses the copies of the parts of the variable in scope that it needs, and the
  parts of a copy that it binds itself (`renameCopies`). Only the function of `[app]` is
  copied at a boxed type, through the pointer it is the dereference of.

  A variable of a trivial type needs no references, but one in the contents of a box is read
  from the block of the box, which may be freed or reused once the box is consumed. It is
  therefore copied (a load) where it is first read (`loadsOf`) or before its owner is given
  up while it is still needed, whichever comes first, and the later uses read the copy.

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
import Data.List( isSuffixOf, partition )
import Data.Maybe( isJust, isNothing )
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
  | S.member x owned || maybe True (unrestricted pe x) (M.lookup x (peGamma pe)) = Nothing
  | otherwise = case [z | z <- reverse (prefixes x), S.member z owned] of
                  (z:_) | Just z /= peLazy pe -> Just z
                  _ -> Nothing

-- A variable of a trivial type needs no references, unless it is in the contents of a box,
-- where it is read from the block (see `copy`).
unrestricted :: PEnv -> Path -> Ty -> Bool
unrestricted pe x t = trivialTy (peEnv pe) t && isNothing (boxOf x)

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
-- contents into an independent root before its owner is settled, and a read of the
-- contents of a box binds them, so that they are copied instead of the box. Only leading
-- reads are handled here; none is moved across calls or guards.
percE pe owned expr@Unscalar{}
  = percE' pe owned expr
percE pe owned expr@Unbox{}
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
         -- each branch of a destructuring of a part of `z` settles `z` with what it uses
         (z:_) | Just x <- scrutVar expr, x /= z, x `within` z -> percE' pe owned expr
               | otherwise -> settle pe owned expr z [x | (x,z') <- deps, z' == z]
         [] -> case [x | (x,z) <- deps, consumedWith expr z x] of
                 xs@(_:_) -> withCopies pe owned xs return expr
                 [] -> do let dead = S.toList (owned `S.difference` live)
                          expr' <- percE' pe (owned `S.intersection` live) expr
                          dropNames pe dead expr'

-- does `expr` consume the live owned `z` while `x`, borrowed from it, is still needed? (The
-- function of `[app]` is duplicated by `[app]`.)
consumedWith :: VExpr -> Path -> Path -> Bool
consumedWith expr z x
  = case expr of
      Proj{}     -> False
      Ret _      -> True
      Call _ _ _ -> True
      App f _    -> x /= f
      Jump{}     -> True
      Let _ _ _ e2 -> not (S.member z (needs (fvE e2))) && S.member x (fvE e2)
      LetYield _ _ _ e2 e3 -> let live = fvE e2 `S.union` fvE e3 in not (S.member z (needs live)) && S.member x live
      _ | Just ds <- destructAOf expr
        -> dsScrut ds == z && not (isRead expr) && not (any (S.member z . uncurry neededAlt) (dsAlts ds))
      _ | Just ds <- destructVOf expr
        -> case dsScrut ds of
             Var y -> y == z && not (isRead expr) && not (any (S.member z . uncurry neededAlt) (dsAlts ds))
             v     -> S.member z (fvV v) && not (S.member z (needs (restFv ds)))
      _ -> False

-- An alias is its pointer at run time (`keepsPtr`), so a use of it needs the variables that it
-- is an alias of.
needs :: VarSet -> VarSet
needs xs = S.union xs (S.fromList [Path r (take k ss) | Path r ss <- S.toList xs, k <- [0 .. length ss - 1], all keepsPtr (drop k ss)])

-- the variables that an alternative needs from before its destructuring
neededAlt :: [Path] -> VExpr -> VarSet
neededAlt xs e = needs (S.filter (\y -> not (any (y `within`) xs)) (fvE e))

-- The owned `z` is dead but the variables `xs` borrowed from it are still needed (see the
-- top): its bound parts, its shortest live alias or the contents of a box take over its
-- ownership, and the other variables are copied.
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
         [] -> let discard = case [p | x <- xs, Just p <- [contentsOn x]] of
                               (Path r ss:_) -> return . Drop (Path r (init ss))
                               [] -> dropNames pe [z]
               in withCopies pe owned' xs discard expr
  where
    shorter a b = if length (stepsFrom z a) <= length (stepsFrom z b) then a else b
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
percE' pe owned expr
  | xs@(_:_) <- loadsOf pe expr
  = withCopiesThen percE' pe owned xs return expr
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
  = atomic pe owned (dsScrut ds) (needs (restFv ds)) $ \pe1 own1 z ->
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
        -> do let live2 = needs (fvE e2)
                  own2  = owned `S.intersection` live2
                  own1  = owned `S.difference` live2
              e1' <- percE pe{ peBorrowed = peBorrowed pe `S.union` own2 } own1 e1
              e2' <- percE (bind pe [(x,V t)]) (own2 `S.union` ownedOf pe [(x,V t)]) e2
              return (hoistdupAll (\e1'' -> Let x t e1'' e2') e1')
      -- like a `let`, whose continuation is one of two branches; `x` is only bound in `e2`
      LetYield x t e1 e2 e3
        -> do let live = needs (fvE e2 `S.union` fvE e3)
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
      Jump j ts vs
        -> do ms <- maybe (fail ("unknown join point " ++ show j)) return (M.lookup j (peJoins pe))
              (k,vs') <- useVals pe owned (zip ms vs)
              return (k (Jump j ts vs'))
      Join j tvs ps e1 e2
        -> do e1' <- percE (paramEnv (peEnv pe) ps Nothing (peJoins pe)) (ownedParams (peEnv pe) ps) e1
              e2' <- percE' pe{ peJoins = M.insert j [m | (_,m,_) <- ps] (peJoins pe) } owned e2
              return (Join j tvs ps e1' e2')
      App f vs
        -> do let move = S.member f owned && all (S.notMember f . fvV) vs
              (kf,f') <- if move then return (id,f) else (\(d,_,y,_) -> (d,y)) <$> copy pe f
              (k,vs') <- useVals pe (if move then S.delete f owned else owned) [(Owned,v) | v <- vs]
              return (kf (k (App f' vs')))
      Gen tvs e -> Gen tvs <$> percE' pe owned e
      Drop x e -> Drop x <$> percE' pe owned e
      Free r e -> Free r <$> percE' pe owned e
      Dup x y e -> do t <- tyOfVar pe x
                      Dup x y <$> percE (bind pe [(y,t)]) (S.union owned (ownedOf pe [(y,t)])) e
      CaseLit v alts def
        -> do alts' <- mapM (\(l,e) -> (,) l <$> percE pe owned e) alts
              def'  <- percE pe owned def
              return (CaseLit v alts' def')
      _ -> fail "unexpected destructuring form"

-- copies

-- A copy of a variable for a use that takes it: a new root with a duplicate of the variable,
-- or of the pointer of a closure, which it is the dereference of (a closure is not under a
-- sum). It comes with the duplication, the variable, and the binders of the copy. A variable
-- of a trivial type is not copied, unless it is in the contents of a box: its copy loads it
-- out of the block (see `loadsOf`).
copy :: PEnv -> Path -> P (K,Path,Path,[(Path,Ty)])
copy pe x
  = do t <- tyOfVar pe x
       case (t,x) of
         _ | unrestricted pe x t -> return (id,x,x,[])
         (V _,_) -> do y <- fresh "u"
                       return (Dup x y,x,y,[(y,t)])
         (A _,Path r ss) | (SDeref : rest) <- reverse ss
           -> do let p = Path r (reverse rest)
                 tp <- tyOfVar pe p
                 q <- fresh "u"
                 let y = child q SDeref
                 return (Dup p q . Deref Borrowed (Var q) y,x,y,[(q,tp),(y,t)])
         _ -> fail ("duplication of a boxed variable that is not a dereferenced pointer: " ++ show x)

-- The trivial variables in the contents of boxes that an expression reads before its
-- subexpressions in tail position: they are copied there, so that every later use reads the
-- copy (a load), even after the box is consumed. A projection or unpack of a variable binds a
-- part of it without reading it, and a dup copies it already.
loadsOf :: PEnv -> VExpr -> [Path]
loadsOf pe expr = [x | x <- S.toList here, Just t <- [M.lookup x (peGamma pe)], trivialTy (peEnv pe) t, isJust (boxOf x)]
  where
    here = case expr of
           Let _ _ e1 _ -> fvE e1
           LetYield _ _ e1 _ _ -> fvE e1
           Proj _ (Var _) _ _ _ -> S.empty
           Unpack _ (Var _) _ _ _ -> S.empty
           Dup{} -> S.empty
           _ -> getConst (descendE (Const . S.singleton) (Const . fvV) (\_ _ -> Const S.empty) expr)

-- Copy the variables `xs` for an expression, which takes the copies as owned; `k` comes
-- between the copies and the expression.
withCopies :: PEnv -> VarSet -> [Path] -> (VExpr -> P VExpr) -> VExpr -> P VExpr
withCopies = withCopiesThen percE

-- Only the outermost products among `xs` are copied: a copy of a product owns its fields,
-- so a part of it in `xs` is bound as a borrowed projection of the copy instead of getting
-- another owned reference (the expression copies it again if it needs one).
-- Loading trivial fields must not restart the owner check before this expression.
-- The copied scrutinee no longer names its box, so that would settle the box before
-- the case instead of letting each alternative take its parts for reuse.
withCopiesThen :: (PEnv -> VarSet -> VExpr -> P VExpr) -> PEnv -> VarSet -> [Path] -> (VExpr -> P VExpr) -> VExpr -> P VExpr
withCopiesThen cont pe owned xs k expr
  = do let covered x z = x /= z && x `within` z &&
                         case M.lookup z (peGamma pe) of
                           Just (V t) -> isJust (partAt t (stepsFrom z x))
                           _ -> False
           roots = [x | x <- xs, not (any (covered x) xs)]
       cs <- mapM (copy pe) roots
       let parts = [(x,renamePrefix z y x,y,stepsFrom z x)
                   | (_,z,y,_) <- cs, z /= y, x <- xs, covered x z]
           ren = [(x,y) | (_,x,y,_) <- cs, x /= y] ++ [(x,y) | (x,y,_,_) <- parts]
           bs  = concat [bs' | (_,_,_,bs') <- cs]
           projections = [Proj Borrowed (Var z) ss y | (_,y,z,ss) <- parts]
       body <- cont (bind pe bs) (S.union owned (ownedOf pe [b | b@(y,_) <- bs, y `elem` map snd ren]))
                     (compose projections (renameCopies (peGamma pe) ren expr))
       compose [d | (d,_,_,_) <- cs] <$> k body

-- The copies replace their variables: a part of a variable that is bound later is a part of
-- its copy, while the parts in scope keep their names unless explicitly renamed too.
renameCopies :: Gamma -> [(Path,Path)] -> VExpr -> VExpr
renameCopies g ren
  = renameE (M.union (M.fromList ren) (M.fromList [(y,y) | y <- M.keys g, any (\(x,_) -> y /= x && y `within` x) ren]))

-- the copies at the start of the bound expression of a `let` come before the `let`, so that
-- it binds a value where it can (such as a unique one)
hoistdupAll :: (VExpr -> VExpr) -> VExpr -> VExpr
hoistdupAll k (Dup x y e) = Dup x y (hoistdupAll k e)
hoistdupAll k e = k e

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
           deadIn (bs,e) = not (any (`S.member` neededAlt (map fst bs) e) zName)
           moveAll  = zOwned && not (isRead expr) && not (productProjection expr) && all deadIn (zip binderss bodies)
       if moveAll
         then do let own = owned `S.difference` S.fromList zName
                 es <- mapM (\(bs,e) -> percE (bind pe bs) (own `S.union` ownedOf pe bs) e) (zip binderss bodies)
                 return (Owned,es)
         else do es <- mapM (borrowedBody pe owned) (zip binderss bodies)
                 return (Borrowed,es)

-- the binders are borrowed from the scrutinee (and from its owner)
borrowedBody :: PEnv -> VarSet -> ([(Path,Ty)],VExpr) -> P VExpr
borrowedBody pe owned (bs,e) = percE (bind pe{ peBorrowed = peBorrowed pe `S.union` ownedOf pe bs } bs) owned e

-- the live binders of an owned scrutinee of the lazy value are copied at the start of the
-- body, and the scrutinee is dropped after that if it is dead; a binder that is an alias of
-- the dead scrutinee takes over its ownership instead
eagerBody :: PEnv -> VarSet -> [Path] -> ([(Path,Ty)],VExpr) -> P VExpr
eagerBody pe owned zName (bs,e)
  = do let live    = fvE e
           zDead   = not (any (`S.member` live) zName)
           alias x = zDead && any (\z -> x `within` z && all keepsPtr (stepsFrom z x)) zName
           (moved,copied) = partition alias [x | (x,t) <- bs, not (trivialTy (peEnv pe) t), S.member x live]
           own     = (if zDead then owned `S.difference` S.fromList zName else owned)
                     `S.union` S.fromList moved
       withCopies (bind pe bs) own copied (if zDead && null moved then dropNames pe zName else return) e

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
      Var x | M.lookup x lastOcc == Just i -> return (id,i+1,val)
            | otherwise -> do (d,_,y,_) <- copy pe x
                              return (d,i+1,Var y)
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
              cs <- mapM (copy pe) dups
              let e1   = renameCopies (peGamma pe) [(x,y) | (_,x,y,_) <- cs, x /= y] e
                  g    = M.unions [M.fromList [(x,V t) | (x,_,t) <- ps], M.fromList (concat [bs | (_,_,_,bs) <- cs]), peGamma pe]
                  inner = PEnv (peEnv pe) g S.empty Nothing M.empty
                  own  = S.fromList ([x | x <- S.toList (fvA (Lam ps r e1)), maybe False (not . trivialTy (peEnv pe)) (M.lookup x g)] ++ [x | (x,_,t) <- ps, not (trivialTy (peEnv pe) (V t))])
              e' <- percE inner own e1
              return (compose [d | (d,_,_,_) <- cs], i + length caps, Lam ps r e')
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
