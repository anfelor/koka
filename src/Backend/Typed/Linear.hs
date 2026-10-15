-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{- Linearity checker for programs after Perceus.

  Variables of a type without pointers are unrestricted. Every other variable is
  either owned, and must be consumed exactly once on every path, or borrowed,
  and may only be inspected or duplicated. A borrowed variable that was obtained
  by destructuring an owned variable becomes invalid once that variable is consumed.
  The binder of a borrowed destructuring that keeps the pointer (`keepsPointer`) at a boxed
  type is an *alias* of the owned variable: consuming the alias (or testing whether it is
  unique) takes over the owned variable, whose borrowed variables are then borrowed from the alias.
  `UnboxLazy` takes the contents of a box of the lazy value in `lazy-eval-locked`: the
  binder is owned and the box is left as it is (its block is then written over without
  dropping its old fields, see `Lazy`).

  A unique variable is owned and holds the only reference to its block, so `UnboxRu` may
  take its contents and keep its block as a credit. An owned variable is unique in the
  first branch of `IsUnique`; unique parameters, the binders of unique destructuring, and a
  `let` of a unique value (a unique variable, a fresh context, an append or `ctx-copy c`) are
  unique too. A context is plugged or appended only through a unique value. Any borrowed use
  of a unique variable, or of a variable borrowed from it, may duplicate the reference, after
  which it is only owned.

  The body of a join point is checked like the body of a function whose owned parameters
  include the variables it captures; a jump is checked like a call that also consumes the
  captured variables. Nothing follows a jump in its branch, so the variables left
  at a jump (including the parents of borrowed arguments) are compared with the other
  branches and consumed after the whole join.

  This checks the modes of the typing rules in `Syntax` (the types are checked by `Check`).
  Keep it in sync with the rules: a change here must be reflected there, and vice versa.
-}
module Backend.Typed.Linear( checkLinear ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( unless, when, forM_, void )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env(..), Gamma, envOf, bindAll, inferV, inferA, inferVar, inferAVar, altTypes, boxContents, reuseSize, paramModes )

-- the mode of a variable, for a borrowed one the owned variable it is borrowed from (if any),
-- and whether it is an alias of that variable (the same pointer)
data Status = Status{ stMode :: Mode, stRoot :: Maybe Name, stAlias :: Bool }
            deriving (Eq,Show)

owned', unique' :: Status
owned'  = Status Owned Nothing False
unique' = Status Unique Nothing False

owns :: Status -> Bool
owns = owning . stMode

isUnique :: Delta -> Name -> Bool
isUnique d x = fmap stMode (M.lookup x d) == Just Unique

type Delta = M.Map Name Status

type L a = M () Delta a

-- the modes of the parameters of the join points in scope, and the variables they capture
type Joins = M.Map Name ([Mode],[Name])

checkLinear :: Program -> [String]
checkLinear prog
  = [show (defName d) ++ ": " ++ err | d <- progDefs prog, Left err <- [checkDef (envOf prog) d]]

checkDef :: Env -> Def -> Either String ()
checkDef env def
  = case def of
      DefFun _ _ args _ body
        -> run (M.fromList [(x,V t) | (x,_,t) <- args]) (paramDelta args) body
      DefVal _ _ _ body -> run M.empty M.empty body
  where
    run g d body = evalM (scopeEnd (checkE env g M.empty body)) () d

-- the variables of a parameter list with their modes
paramDelta :: [(Name,Mode,VType)] -> Delta
paramDelta ps = M.fromList [(x, Status m Nothing False) | (x,m,t) <- ps, not (isTrivial (V t))]

-- at the end of a scope no owned variable may be left
scopeEnd :: L () -> L ()
scopeEnd action
  = do action
       d <- get
       let left = [x | (x,st) <- M.toList d, owns st]
       unless (null left) (fail ("owned variables are not consumed: " ++ show left))

-- consume an owned variable; borrowed variables derived from it become invalid
consume :: Gamma -> Name -> L ()
consume g x
  | trivialVar g x = return ()
  | otherwise
  = do promote x
       d <- get
       case M.lookup x d of
         Just st | owns st -> put (M.filter ((/= Just x) . stRoot) (M.delete x d))
                 | otherwise -> fail ("owned use of borrowed variable " ++ show x)
         Nothing -> fail ("use of consumed or invalid variable " ++ show x)

-- an alias of an owned variable takes it over
promote :: Name -> L ()
promote x
  = do d <- get
       case M.lookup x d of
         Just (Status Borrowed (Just z) True)
           | Just stz <- M.lookup z d, owns stz
           -> put (M.insert x stz (M.map (\st -> if stRoot st == Just z then st{ stRoot = Just x } else st) (M.delete z d)))
         _ -> return ()

inspect :: Gamma -> Name -> L ()
inspect g x
  | trivialVar g x = return ()
  | otherwise
  = do d <- get
       unless (M.member x d) (fail ("use of consumed or invalid variable " ++ show x))
       r <- rootOf x
       case r of
         Just z | isUnique d z -> put (M.insert z owned' d)
         _ -> return ()

trivialVar :: Gamma -> Name -> Bool
trivialVar g x = maybe False isTrivial (M.lookup x g)

rootOf :: Name -> L (Maybe Name)
rootOf x
  = do d <- get
       return (case M.lookup x d of
                 Just (Status Borrowed r _) -> r
                 Just _                   -> Just x
                 Nothing                  -> Nothing)

addVars :: [(Name,Ty)] -> Status -> L ()
addVars bs st
  = do d <- get
       put (foldr (\(x,_) -> M.insert x st) d [b | b@(_,t) <- bs, not (isTrivial t)])

-- leaving the scope of binders: owned ones must have been consumed
leave :: [(Name,Ty)] -> L ()
leave bs
  = do d <- get
       forM_ bs $ \(x,_) ->
         when (maybe False owns (M.lookup x d)) (fail ("owned variable is not consumed: " ++ show x))
       put (foldr M.delete d (map fst bs))

-- values

ownedV :: Env -> Gamma -> VVal -> L ()
ownedV env g val
  = case val of
      Var x -> consume g x
      DupV v -> liftE (inferV env g val) >> borrowedV env g v
      Glob _ _ -> do t <- V <$> liftE (inferV env g val)
                     unless (isTrivial t) (fail ("owned use of global " ++ show val))
      UnitV -> return ()
      Lit _ -> return ()
      NoReuse _ -> return ()
      Inj _ _ _ -> children
      Pair _ _ -> children
      Ptr _ _ -> children
      Pack _ _ _ -> children
      TyApp _ _ -> children
      Hole -> return ()
      Context _ k -> ownedV env g k
      Plug c v -> uniqueV env g c >> ownedV env g v
      Append c d -> uniqueV env g c >> uniqueV env g d
      CtxCopy c -> ownedV env g c
  where
    children = void (descendV (\a -> ownedA env g a >> return a) (\v -> ownedV env g v >> return v) val)

ownedA :: Env -> Gamma -> AVal -> L ()
ownedA env g val
  = case val of
      Fun _ -> liftE (inferA env g val) >>= ownedParams
      Lam ps _ e
        -> do unless (all (\(_,m,_) -> m == Owned) ps) (fail ("closure with parameters that are not owned: " ++ show val))
              let caps = S.toList (fvA val)
              mapM_ (consume g) caps
              d <- get
              let g' = bindAll [(x,V t) | (x,_,t) <- ps] g
                  inner = M.fromList ([(x,owned') | x <- caps, not (trivialVar g x)] ++
                                      [(x,owned') | (x,_,t) <- ps, not (isTrivial (V t))])
              put inner
              scopeEnd (checkE env g' M.empty e)
              put d
      UnitA -> return ()
      InjA _ _ v -> ownedA env g v
      Roll _ v -> ownedA env g v
      Box v -> ownedV env g v
      OpenCon _ _ v -> ownedV env g v
      BoxAt r v -> consume g r >> ownedV env g v
      BoxIn x v -> consume g x >> ownedV env g v

-- a unique value is a unique variable or a fresh context
uniqueV :: Env -> Gamma -> VVal -> L ()
uniqueV env g val
  = case val of
      Var x -> uniqueName g x
      Context _ k -> ownedV env g k
      CtxCopy c -> ownedV env g c
      Append c d -> uniqueV env g c >> uniqueV env g d
      _ -> fail ("unique use of a value that is not unique: " ++ show val)

isUniqueV :: Delta -> VVal -> Bool
isUniqueV d val
  = case val of
      Var x -> isUnique d x
      Context _ _ -> True
      CtxCopy _ -> True
      Append _ _ -> True
      _ -> False

uniqueName :: Gamma -> Name -> L ()
uniqueName g x
  = do promote x
       d <- get
       unless (isUnique d x) (fail ("unique use of a variable that is not unique: " ++ show x))
       consume g x

borrowedV :: Env -> Gamma -> VVal -> L ()
borrowedV env g val
  = case val of
      Var x -> inspect g x
      Glob _ _ -> return ()
      Lit _ -> return ()
      UnitV -> return ()
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

checkE :: Env -> Gamma -> Joins -> VExpr -> L ()
checkE env g js (UnboxLazy v x e)
  = do t   <- liftE (inferVar g v)
       [[tx]] <- liftE (altTypes env t (UnboxLazy v x e))
       inspect g v
       let bs = [(x,tx)]
       addVars bs owned'
       checkE env (bindAll bs g) js e
       leave bs
checkE _ _ _ expr
  | isRead expr, Just ds <- destructAOf expr, owning (dsMode ds)
  = fail ("owned read of the contents of a box: " ++ show (dsScrut ds))
checkE env g js expr
  | Just ds <- destructAOf expr
  = do when (not (keepsPointer expr) && dsMode ds == Unique)
         (fail ("unique destructuring of a value that is not a pointer: " ++ show (dsScrut ds)))
       t <- liftE (inferVar g (dsScrut ds))
       tss <- liftE (altTypes env t expr)
       let z = dsScrut ds
       destruct env g js (dsMode ds) (keepsPointer expr) (Just z)
         (consume g z) (uniqueName g z) (inspect g z)
         [(zip xs ts,e) | ((xs,e),ts) <- zip (dsAlts ds) tss]
  | Just ds <- destructVOf expr
  = do when (not (keepsPointer expr) && dsMode ds == Unique)
         (fail ("unique destructuring of a value that is not a pointer: " ++ show (dsScrut ds)))
       t <- V <$> liftE (inferV env g (dsScrut ds))
       tss <- liftE (altTypes env t expr)
       let v = dsScrut ds
           name = case v of { Var z -> Just z; _ -> Nothing }
       destruct env g js (dsMode ds) (keepsPointer expr) name
         (ownedV env g v) (uniqueV env g v) (borrowedV env g v)
         [(zip xs ts,e) | ((xs,e),ts) <- zip (dsAlts ds) tss]
checkE env g js expr
  = case expr of
      Ret v -> ownedV env g v
      Let x t e1 e2 -> do d <- get
                          let st = case e1 of
                                     Ret v | isUniqueV d v -> unique'
                                     _ -> owned'
                          checkE env g M.empty e1
                          addVars [(x,V t)] st
                          checkE env (M.insert x (V t) g) js e2
                          leave [(x,V t)]
      Call f _ vs -> args [] (paramModes env f (length vs)) vs
      Jump j vs -> case M.lookup j js of
                     Just (ms,caps) -> args caps ms vs
                     Nothing -> fail ("jump to unknown join point " ++ show j)
      Join j ps e1 e2 -> do let caps = [x | x <- S.toList (fvE e1 `S.difference` S.fromList [x | (x,_,_) <- ps]), not (trivialVar g x)]
                            d <- get
                            put (paramDelta ps `M.union` M.fromList [(x,owned') | x <- caps])
                            scopeEnd (checkE env (bindAll [(x,V t) | (x,_,t) <- ps] g) js e1)
                            put d
                            checkE env g (M.insert j ([m | (_,m,_) <- ps],caps) js) e2
      App f vs -> do ft <- liftE (inferVar g f)
                     case ft of
                       A a -> ownedParams a
                       _ -> fail "unboxed function operand"
                     consume g f
                     mapM_ (ownedV env g) vs
      Gen _ e -> checkE env g M.empty e
      Drop x e -> consume g x >> checkE env g js e
      Free r e -> consume g r >> checkE env g js e
      Dup x y e -> do a <- liftE (inferAVar g x)
                      when (containsReuse (A a)) (fail "cannot duplicate a reuse credit")
                      inspect g x
                      let bs = [(y,A a)]
                      addVars bs owned'
                      checkE env (bindAll bs g) js e
                      leave bs
      IsUnique x e1 e2 -> do promote x
                             d <- get
                             unless (maybe False owns (M.lookup x d)) (fail ("uniqueness test of a variable that is not owned: " ++ show x))
                             branches [modify (M.insert x unique') >> checkE env g js e1, checkE env g js e2]
      UnboxRu z x r e
        -> do s <- liftE (inferAVar g z >>= boxContents)
              n <- liftE (reuseSize s)
              uniqueName g z
              let bs = [(x,V s),(r,V (VReuse n (Just (Var x))))]
              addVars bs owned'
              checkE env (bindAll bs g) js e
              leave bs
      CaseLit v alts def -> do borrowedV env g v
                               branches (map (checkE env g js) (def : map snd alts))
      _ -> fail "unexpected destructuring form"
  where
    -- owned and unique arguments (and captured variables) first: a borrowed argument must not
    -- be derived from one of them
    args caps ms vs = do sequence_ [ownedV env g v | (Owned,v) <- zip ms vs]
                         mapM_ (consume g) caps
                         sequence_ [uniqueV env g v | (Unique,v) <- zip ms vs]
                         sequence_ [borrowedV env g v | (Borrowed,v) <- zip ms vs]

destruct :: Env -> Gamma -> Joins -> Mode -> Bool -> Maybe Name -> L () -> L () -> L () -> [([(Name,Ty)],VExpr)] -> L ()
destruct env g js m keeps name own unique borrow alts
  = do st <- case (m,name) of
               (Owned,_) -> own >> return (const owned')
               (Unique,_) -> unique >> return (const unique')
               (Borrowed,Just z) -> do borrow
                                       r <- rootOf z
                                       d <- get
                                       let zAlias = maybe False (\s -> owns s || stAlias s) (M.lookup z d)
                                       return (\t -> Status Borrowed r (keeps && zAlias && isA t))
               (Borrowed,Nothing) -> borrow >> return (const (Status Borrowed Nothing False))
       branches [do sequence_ [addVars [b] (st t) | b@(_,t) <- bs]
                    checkE env (bindAll bs g) js e
                    leave bs
                | (bs,e) <- alts]

-- every branch must consume the same owned variables
branches :: [L ()] -> L ()
branches cs
  = do d <- get
       ds <- mapM (\c -> do put d
                            c
                            get) cs
       case ds of
         [] -> return ()
         (d1:rest) -> do forM_ rest $ \d2 ->
                           unless (owned d1 == owned d2)
                             (fail ("branches consume different variables: " ++ show (owned d1) ++ " vs. " ++ show (owned d2)))
                         put (M.mapWithKey (\x st -> if st == unique' && any (\d2 -> not (isUnique d2 x)) rest then owned' else st) d1)
  where
    owned d = M.keys (M.filter owns d)

isA :: Ty -> Bool
isA (A _) = True
isA (V _) = False
