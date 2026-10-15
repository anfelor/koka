-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{- Linearity checker for programs after Perceus.

  Variables of a type without pointers are unrestricted. Every other variable reaches an owned
  block through its *root* (`Ref`). An owned variable is its own root and must be consumed exactly
  once on every path. A borrowed variable may only be inspected or duplicated; one that was
  obtained by destructuring an owned variable is borrowed from that variable's root and becomes
  invalid once the root is consumed. The binder of a borrowed destructuring that keeps the pointer
  (`keepsPointer`) of an owned variable (or of an alias) at a boxed type is an *alias*: it is the
  root's pointer, and consuming it (or testing whether it is unique) consumes (or tests) the root.
  `UnboxLazy` takes the contents of a box of the lazy value in `lazy-eval-locked`: the
  binder is owned and the box is left as it is (its block is then written over without
  dropping its old fields, see `Lazy`).

  A unique variable is owned and holds the only reference to its block, so `UnboxRu` may
  take its contents and keep its block as a credit. An owned variable is unique in the
  first branch of `IsUnique`; unique parameters, the binders of unique destructuring, and a
  `let` of a unique value (a unique variable, a fresh context, an append or `ctx-copy c`) are
  unique too. A context is plugged or appended only through a unique value. Any borrowed use
  of a unique root, or of a variable borrowed from it, may duplicate the reference, after
  which it is only owned.

  The check is bottom-up: a term gives the roots it uses (`Use`), whether it borrows from each,
  and whether it consumes it, owned or unique. Sequencing (`andThen`) rejects a use of a root
  after it is consumed, and a unique use after a borrowed one. Branches must consume the same
  roots. A binder must be consumed in its scope, and only a unique one may be consumed as unique.
  A `let` binder is unique if its value is and it is used as unique.

  The body of a join point is checked like the body of a function whose owned parameters
  include the variables it captures; a jump is checked like a call that also consumes the
  captured variables.

  The names in the description of a credit denote the values they were bound to, also out of
  their scope. The checker tracks the structural values of variables (`Values`): a variable is
  an alias of a value built from variables whose values are not known structurally, which
  denote themselves. A variable named in the description of a credit in scope may only be bound
  again to an alias of its value (`bindValues`), so the description keeps its meaning; a jump
  binds the parameters of a join point. A closed body starts without known values.

  This checks the modes of the typing rules in `Syntax` (the types are checked by `Check`).
  Keep it in sync with the rules: a change here must be reflected there, and vice versa.
-}
module Backend.Typed.Linear( checkLinear ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Applicative( (<|>) )
import Control.Monad( unless, when, forM_, foldM )
import Data.Functor.Const( Const(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env(..), Gamma, envOf, bindAll, inferV, inferA, inferVar, inferAVar, altTypes, unboxRuBinds, paramModes, altPattern )

-- how a variable reaches an owned block, its root: an owned variable or an alias is consumed
-- through its root (itself, or the owned variable it is the pointer of); a borrowed variable
-- is borrowed from its root (if any)
data Ref = Own Name | Borrow (Maybe Name)

rootOf :: Ref -> Maybe Name
rootOf (Own z) = Just z
rootOf (Borrow r) = r

-- the variables in scope that are not of a trivial type
type Refs = M.Map Name Ref

-- the variables with a known structural value; the others denote the value they were bound to
type Values = M.Map Name VVal

data Scope = Scope{ scRefs :: Refs, scValues :: Values }

-- how a term uses a root: whether it borrows from it, and whether it consumes it (owned or unique)
data Usage = Usage{ borrowed :: Bool, consumed :: Maybe Mode }

-- the roots used by a term
type Use = M.Map Name Usage

-- the uses of an expression, and its value if it is known
type Res = (Use, Maybe VVal)

type L a = M Scope () a

-- the parameters of the join points in scope, and the variables they capture
type Joins = M.Map Name ([(Name,Mode,VType)],[Name])

checkLinear :: Program -> [String]
checkLinear prog
  = [show (defName d) ++ ": " ++ err | d <- progDefs prog, Left err <- [checkDef (envOf prog) d]]

checkDef :: Env -> Def -> Either String ()
checkDef env def
  = case def of
      DefFun _ _ args _ body
        -> run (M.fromList [(x,V t) | (x,_,t) <- args]) (params args) body
      DefVal _ _ _ body -> run M.empty [] body
  where
    run g ps body = evalM (closed ps (checkE env g M.empty body)) (Scope M.empty M.empty) ()

-- the parameters that are not of a trivial type
params :: [(Name,Mode,VType)] -> [(Name,Mode)]
params ps = [(x,m) | (x,m,t) <- ps, not (isTrivial (V t))]

-- uses

-- `u1` is evaluated before `u2`
andThen :: Use -> Use -> L Use
andThen u1 u2
  = do forM_ (M.toList (M.intersectionWith (,) u1 u2)) $ \(z,(s1,s2)) ->
         do when (consumed s1 /= Nothing) (fail ("use of consumed or invalid variable " ++ show z))
            when (borrowed s1 && consumed s2 == Just Unique)
              (fail ("unique use of a variable after a borrowed use: " ++ show z))
       return (M.unionWith both u1 u2)

both :: Usage -> Usage -> Usage
both (Usage b1 c1) (Usage b2 c2) = Usage (b1 || b2) (if c1 == Just Unique then c1 else c2 <|> c1)

-- the uses of terms that are evaluated in order
uses :: [L Use] -> L Use
uses = foldM (\u c -> c >>= andThen u) M.empty

-- a term with uses `u` is evaluated before an expression
before :: L Use -> L Res -> L Res
before c1 c2
  = do u1 <- c1
       (u2,v) <- c2
       u <- andThen u1 u2
       return (u,v)

-- every branch must consume the same roots; the value is known if the branches agree on it
branches :: [Res] -> L Res
branches rs
  = do case map (consumedRoots . fst) rs of
         (c1:rest) -> forM_ rest $ \c2 ->
                        unless (c1 == c2) (fail ("branches consume different variables: " ++ show c1 ++ " vs. " ++ show c2))
         [] -> return ()
       return (M.unionsWith both (map fst rs), agreed (map snd rs))
  where
    consumedRoots u = M.keys (M.filter ((/= Nothing) . consumed) u)
    agreed (v:vs) | all (== v) vs = v
    agreed _ = Nothing

-- leaving the scope of new roots with their mode: they must be consumed (as unique only if they are)
leave :: [(Name,Mode)] -> Use -> L Use
leave xs u
  = do forM_ xs $ \(x,m) ->
         case M.lookup x u >>= consumed of
           Just c -> when (c == Unique && m /= Unique) (fail ("unique use of a variable that is not unique: " ++ show x))
           Nothing -> fail ("owned variable is not consumed: " ++ show x)
       return (foldr (M.delete . fst) u xs)

withRefs :: Refs -> L a -> L a
withRefs rs = local (\sc -> sc{ scRefs = M.union rs (scRefs sc) })

-- the scope of binders that are new roots with a mode
roots :: Mode -> [(Name,Ty)] -> L Res -> L Res
roots m bs check
  = do let xs = [x | (x,t) <- bs, not (isTrivial t)]
       (u,v) <- withRefs (M.fromList [(x,Own x) | x <- xs]) check
       u' <- leave [(x,m) | x <- xs] u
       return (u',v)

-- A body (of a function, closure or join point) whose only variables are its parameters. A
-- variable outside it may be bound again on the way to it, so no values are known.
closed :: [(Name,Mode)] -> L Res -> L ()
closed ps check
  = do (u,_) <- local (const (Scope (M.fromList [(x, if owning m then Own x else Borrow Nothing) | (x,m) <- ps]) M.empty)) check
       _ <- leave [(x,m) | (x,m) <- ps, owning m] u
       return ()

-- values

-- The value of a value in terms of variables without a known structural value. Credits have no
-- identity, since descriptions never contain one.
valueOf :: Gamma -> Values -> VVal -> Maybe VVal
valueOf g vs val
  = case val of
      Var x | Just (V (VReuse _ _)) <- M.lookup x g -> Just UnitV
            | Just v <- M.lookup x vs -> valueOf g vs v
            | otherwise -> Just val
      DupV v -> valueOf g vs v
      NoReuse _ _ -> Just UnitV
      Pair a b -> Pair <$> valueOf g vs a <*> valueOf g vs b
      Inj i t v -> Inj i t <$> valueOf g vs v
      Pack t ts v -> Pack t ts <$> valueOf g vs v
      UnitV -> Just val
      Lit _ -> Just val
      _ -> Nothing

-- the descriptions carried by a value of a type
descriptions :: VType -> [Contents]
descriptions t
  = case t of
      VReuse _ p -> maybe [] pure p
      VProd a b -> descriptions a ++ descriptions b
      VSum ts -> concatMap descriptions ts
      VExists _ b -> descriptions b
      _ -> []

-- the variables named in the descriptions of the variables in scope, also through their values
describedNames :: Gamma -> Scope -> S.Set Name
describedNames g sc
  = S.unions [fvV p `S.union` maybe S.empty fvV (valueOf g (scValues sc) p)
             | x <- M.keys (scRefs sc), Just (V t) <- [M.lookup x g], Contents _ p _ <- descriptions t]

-- Bind variables to their values (`Nothing` if unknown). A variable named in a description may
-- only be bound again to an alias of its value; otherwise the values that name it are forgotten.
bindValues :: Gamma -> [(Name,Maybe VVal)] -> L a -> L a
bindValues g xs check = foldr bind check xs
  where
    bind :: (Name,Maybe VVal) -> L a -> L a
    bind (x,v) k
      = do sc <- ask
           let vs = scValues sc
               alias = v == valueOf g vs (Var x)
           when (not alias && S.member x (describedNames g sc))
             (fail ("variable named in the description of a credit is bound again to a different value: " ++ show x))
           let forgotten = M.filter (S.notMember x . fvV) (M.delete x vs)
               vs' = case v of
                       _ | alias -> vs
                       Just w | S.notMember x (fvV w) -> M.insert x w forgotten
                       _ -> forgotten
           local (\sc' -> sc'{ scValues = vs' }) k

-- the values of the binders of an alternative whose scrutinee has the value `sv`; a scrutinee
-- without a known structural value is refined to the pattern of the alternative
altValues :: Gamma -> Maybe VVal -> Maybe VVal -> [Name] -> L a -> L a
altValues g sv pat xs check
  = case (pat,sv) of
      (Just p, Just (Var y)) -> bindValues g unknown (local (\sc -> sc{ scValues = M.insert y p (scValues sc) }) check)
      (Just p, Just w) | Just ms <- match p w -> bindValues g [(x, lookup x ms) | x <- xs] check
      _ -> bindValues g unknown check
  where
    unknown = [(x,Nothing) | x <- xs]
    match (Var x) w = Just [(x,w)]
    match (Pair a b) (Pair c d) = (++) <$> match a c <*> match b d
    match (Inj i _ a) (Inj j _ c) | i == j = match a c
    match (Pack _ _ a) (Pack _ _ c) = match a c
    match _ _ = Nothing

-- variables

refOf :: Name -> L Ref
refOf x
  = do rs <- asks scRefs
       maybe (fail ("unbound variable " ++ show x)) return (M.lookup x rs)

trivialVar :: Gamma -> Name -> Bool
trivialVar g x = maybe False isTrivial (M.lookup x g)

-- consume an owned variable (as unique if the mode is), that is, its root
consumeAs :: Mode -> Gamma -> Name -> L Use
consumeAs m g x
  | trivialVar g x = return M.empty
  | otherwise
  = do r <- refOf x
       case r of
         Own z -> return (M.singleton z (Usage False (Just m)))
         Borrow _ | m == Unique -> fail ("unique use of a variable that is not unique: " ++ show x)
                  | otherwise   -> fail ("owned use of borrowed variable " ++ show x)

consume, uniqueName :: Gamma -> Name -> L Use
consume = consumeAs Owned
uniqueName = consumeAs Unique

inspect :: Gamma -> Name -> L Use
inspect g x
  | trivialVar g x = return M.empty
  | otherwise
  = do r <- refOf x
       return (maybe M.empty (\z -> M.singleton z (Usage True Nothing)) (rootOf r))

-- values

ownedV :: Env -> Gamma -> VVal -> L Use
ownedV env g val
  = case val of
      Var x -> consume g x
      DupV v -> liftE (inferV env g val) >> borrowedV env g v
      Glob _ _ -> do t <- V <$> liftE (inferV env g val)
                     unless (isTrivial t) (fail ("owned use of global " ++ show val))
                     return M.empty
      UnitV -> return M.empty
      Lit _ -> return M.empty
      NoReuse _ _ -> return M.empty
      Inj _ _ _ -> children
      Pair _ _ -> children
      Ptr _ _ -> children
      Pack _ _ _ -> children
      TyApp _ _ -> children
      Hole -> return M.empty
      Context _ k -> ownedV env g k
      Plug c v -> uses [uniqueV env g c, ownedV env g v]
      Append c d -> uses [uniqueV env g c, uniqueV env g d]
      CtxCopy c -> ownedV env g c
  where
    children = uses (getConst (descendV (\a -> Const [ownedA env g a]) (\v -> Const [ownedV env g v]) val))

ownedA :: Env -> Gamma -> AVal -> L Use
ownedA env g val
  = case val of
      Fun _ -> do liftE (inferA env g val) >>= ownedParams
                  return M.empty
      Lam ps _ e
        -> do unless (all (\(_,m,_) -> m == Owned) ps) (fail ("closure with parameters that are not owned: " ++ show val))
              let caps = S.toList (fvA val)
              closed ([(x,Owned) | x <- caps, not (trivialVar g x)] ++ params ps)
                     (checkE env (bindAll [(x,V t) | (x,_,t) <- ps] g) M.empty e)
              uses (map (consume g) caps)
      UnitA -> return M.empty
      InjA _ _ v -> ownedA env g v
      Roll _ v -> ownedA env g v
      Box v -> ownedV env g v
      OpenCon _ _ v -> ownedV env g v
      BoxAt r v -> uses [consume g r, ownedV env g v]
      BoxIn x v -> uses [consume g x, ownedV env g v]

-- a unique value is a unique variable or a fresh context
uniqueV :: Env -> Gamma -> VVal -> L Use
uniqueV env g val
  = case val of
      Var x -> uniqueName g x
      Context _ k -> ownedV env g k
      CtxCopy c -> ownedV env g c
      Append c d -> uses [uniqueV env g c, uniqueV env g d]
      _ -> fail ("unique use of a value that is not unique: " ++ show val)

borrowedV :: Env -> Gamma -> VVal -> L Use
borrowedV env g val
  = case val of
      Var x -> inspect g x
      Glob _ _ -> return M.empty
      Lit _ -> return M.empty
      UnitV -> return M.empty
      TyApp v _ -> borrowedV env g v
      _ -> fail ("borrowed use of a non-atomic value: " ++ show val)

-- closures only have owned parameters
ownedParams :: AType -> L ()
ownedParams a = unless (all (== Owned) (modes a)) (fail ("closure with parameters that are not owned: " ++ show a))
  where
    modes (AFun ps _) = map fst ps
    modes (AForall _ t) = modes t
    modes _ = []

-- expressions

checkE :: Env -> Gamma -> Joins -> VExpr -> L Res
checkE env g js (UnboxLazy v x e)
  = do t   <- liftE (inferVar g v)
       [[tx]] <- liftE (altTypes env t (UnboxLazy v x e))
       let bs = [(x,tx)]
       before (inspect g v) (roots Owned bs (bindValues g [(x,Nothing)] (checkE env (bindAll bs g) js e)))
checkE _ _ _ expr
  | isRead expr, Just ds <- destructAOf expr, owning (dsMode ds)
  = fail ("owned read of the contents of a box: " ++ show (dsScrut ds))
checkE env g js expr
  | Just ds <- destructAOf expr = destructE (liftE (inferVar g (dsScrut ds))) (dsMode ds) (Var (dsScrut ds)) (dsAlts ds)
  | Just ds <- destructVOf expr = destructE (V <$> liftE (inferV env g (dsScrut ds))) (dsMode ds) (dsScrut ds) (dsAlts ds)
  where
    destructE infer m v alts
      = do when (not (keepsPointer expr) && m == Unique)
             (fail ("unique destructuring of a value that is not a pointer: " ++ show v))
           t <- infer
           tss <- liftE (altTypes env t expr)
           destruct env g js m (keepsPointer expr) v
             [(altPattern expr t i xs, zip xs ts, e) | (i,((xs,e),ts)) <- zip [0..] (zip alts tss)]
checkE env g js expr
  = case expr of
      Ret v -> do u <- ownedV env g v
                  vs <- asks scValues
                  return (u, valueOf g vs v)
      -- the binder is unique if it is used as unique (and the value is unique)
      Let x t e1 e2 -> do vs <- asks scValues
                          r1 <- case e1 of
                                  Ret v -> return (Left v)
                                  _ -> Right <$> checkE env g M.empty e1
                          let v1 = either (valueOf g vs) snd r1
                          (u2,v) <- withRefs (M.singleton x (Own x))
                                      (bindValues g [(x,v1)] (checkE env (M.insert x (V t) g) js e2))
                          let unique = (M.lookup x u2 >>= consumed) == Just Unique
                          (m,u1) <- case r1 of
                                      Left w | unique -> (,) Unique <$> uniqueV env g w
                                             | otherwise -> (,) Owned <$> ownedV env g w
                                      Right (u,_) -> return (Owned,u)
                          u <- andThen u1 =<< leave [(x,m) | not (isTrivial (V t))] u2
                          return (u,v)
      Call f _ vs -> unknown (args [] (paramModes env f (length vs)) vs)
      Jump j vs -> case M.lookup j js of
                     Just (ps,caps) -> do bound ps caps vs
                                          unknown (args caps [m | (_,m,_) <- ps] vs)
                     Nothing -> fail ("jump to unknown join point " ++ show j)
      Join j ps e1 e2 -> do let caps = [x | x <- S.toList (fvE e1 `S.difference` S.fromList [x | (x,_,_) <- ps]), not (trivialVar g x)]
                            closed (params ps ++ [(x,Owned) | x <- caps])
                                   (checkE env (bindAll [(x,V t) | (x,_,t) <- ps] g) js e1)
                            checkE env g (M.insert j (ps,caps) js) e2
      App f vs -> do ft <- liftE (inferVar g f)
                     case ft of
                       A a -> ownedParams a
                       _ -> fail "unboxed function operand"
                     unknown (uses (consume g f : map (ownedV env g) vs))
      Gen _ e -> unknown (fst <$> checkE env g M.empty e)
      Drop x e -> before (consume g x) (checkE env g js e)
      Free r e -> before (consume g r) (checkE env g js e)
      Dup x y e -> do a <- liftE (inferAVar g x)
                      when (containsReuse (A a)) (fail "cannot duplicate a reuse credit")
                      t <- liftE (inferVar g x)
                      let bs = [(y,t)]
                      before (inspect g x) (roots Owned bs (bindValues g [(y,Nothing)] (checkE env (bindAll bs g) js e)))
      -- the test uses the root without borrowing from it, which is unique in the first branch
      IsUnique x e1 e2 -> do r <- refOf x
                             z <- case r of
                                    Own z -> return z
                                    Borrow _ -> fail ("uniqueness test of a variable that is not owned: " ++ show x)
                             (u1,v1) <- checkE env g js e1
                             r2 <- checkE env g js e2
                             before (return (M.singleton z (Usage False Nothing)))
                                    (branches [(M.adjust (\s -> s{ consumed = Owned <$ consumed s }) z u1, v1), r2])
      UnboxRu z x r e
        -> do bs <- liftE (unboxRuBinds g z x r)
              before (uniqueName g z) (roots Owned bs (bindValues g [(x,Nothing),(r,Nothing)] (checkE env (bindAll bs g) js e)))
      CaseLit v alts def -> before (borrowedV env g v) (branches =<< mapM (checkE env g js) (def : map snd alts))
      _ -> fail "unexpected destructuring form"
  where
    unknown c = do u <- c
                   return (u,Nothing)
    -- owned and unique arguments (and captured variables) first: a borrowed argument must not
    -- be derived from one of them
    args caps ms vs = uses ([ownedV env g v | (Owned,v) <- zip ms vs] ++
                            map (consume g) caps ++
                            [uniqueV env g v | (Unique,v) <- zip ms vs] ++
                            [borrowedV env g v | (Borrowed,v) <- zip ms vs])
    -- a jump binds the parameters that the descriptions of the parameters and captured
    -- variables name, which must be aliases of the arguments
    bound :: [(Name,Mode,VType)] -> [Name] -> [VVal] -> L ()
    bound ps caps vs
      = do values <- asks scValues
           let named = S.unions [fvV p | t <- [t | (_,_,t) <- ps] ++ [t | x <- caps, Just (V t) <- [M.lookup x g]]
                                       , Contents _ p _ <- descriptions t]
           forM_ [(x,v) | ((x,_,_),v) <- zip ps vs, S.member x named] $ \(x,v) ->
             unless (valueOf g values v == valueOf g values (Var x))
               (fail ("variable named in the description of a credit is bound again to a different value: " ++ show x))

-- the binders of a borrowed destructuring of `z` are borrowed from its root, except that one
-- that keeps the pointer of an owned `z` (or of an alias) at a boxed type is an alias
destruct :: Env -> Gamma -> Joins -> Mode -> Bool -> VVal -> [(Maybe VVal,[(Name,Ty)],VExpr)] -> L Res
destruct env g js m keeps v alts
  = do sc <- ask
       let ref = case v of { Var z -> M.lookup z (scRefs sc); _ -> Nothing }
           sv = valueOf g (scValues sc) v
           binders bs | owning m  = roots m bs
                      | otherwise = withRefs (M.fromList [(x, borrowedFrom ref t) | (x,t) <- bs])
           use = case m of
                   Owned -> ownedV env g v
                   Unique -> uniqueV env g v
                   Borrowed -> borrowedV env g v
       before use (branches =<< sequence [binders bs (altValues g sv pat (map fst bs) (checkE env (bindAll bs g) js e))
                                         | (pat,bs,e) <- alts])
  where
    borrowedFrom (Just (Own z)) t | keeps && isA t = Own z
    borrowedFrom r _ = Borrow (r >>= rootOf)

isA :: Ty -> Bool
isA (A _) = True
isA (V _) = False
