-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{- Linearity checker for programs after Perceus.

  Variables of a trivial type (without pointers, also through named types: `trivialTy`) are
  unrestricted. Every other variable is a path (see
  `Syntax.Path`) and has the mode of its owner, the longest variable on its path that is a
  root (or, in the body of a join point, a variable it captures). An owned root holds one
  reference, which must be consumed exactly once on every path; a borrowed root (a borrowed
  parameter, or a binder of a borrowed destructuring of a value that is not a variable) holds
  a reference that may only be inspected.

  The variables at the steps from a variable are its parts: a reference to a variable is one
  reference to each of its parts (both components of a pair, the contents and the credit of a
  box, and the only part at any other step), so consuming a part takes it out of its parent,
  and a parent is consumed once all of its parts are. The binder of `[deref]`, `[unroll]`,
  `[case-a]`, `[split-a]` or `[unpack]` of a boxed value is the pointer of its scrutinee, so
  consuming or testing it consumes or tests the scrutinee (`key`). So does a part whose
  sibling is of a trivial type, which is determined from the type of the parent: a projection
  binds only its field, not the products around it (`[proj]`). In an alternative whose binder of a trivial type is all of
  the scrutinee (`Nothing`), the scrutinee needs no references. The mode of a
  destructuring of a variable is therefore irrelevant (an owned destructuring is a borrowed one
  whose parts are consumed), except that a unique destructuring consumes a unique scrutinee:
  its alternatives must consume it, and it is then a unique use of the scrutinee. `UnboxLazy`
  takes the contents of a box of the lazy value in `lazy-eval-locked`: the binder is a new
  owned root and the box is left as it is (its block is then written over without dropping
  its old fields, see `Lazy`). `Unscalar` copies the trivial contents of a scalar into a root,
  so its mode matters: an owned read consumes the scalar.

  `dup x` gives `x` one more reference under the same name, so a variable may hold several:
  the references are counted (`Counts`), where a reference to a variable stands for one to
  each of its parts (`refine`). After `dup z.fst; drop z`, for example, `z.fst` still holds a
  reference, and so does `z.fst` after a `let` that consumes the other parts of `z`.

  A unique variable is owned and holds the only reference to its block, so `UnboxRu` may
  take its contents and keep its block as a credit. An owned variable is unique in the
  first branch of `IsUnique`; unique parameters and a `let` of a unique value (a unique
  variable, a fresh context, an append or `ctx-copy c`) are unique too, and so are the
  pointers of the scrutinee of a unique destructuring. A context is plugged or appended only
  through a unique value. Any borrowed use of a unique variable, or of a variable on its path,
  may duplicate the reference, after which it is only owned.

  The check is bottom-up: a term gives the references it consumes (negative for those it
  creates with `dup`), the references that must exist before it, and the variables it borrows
  and consumes as unique (`Use`). Sequencing (`andThen`) adds them up and rejects a unique use
  after a borrowed one. Branches must consume the same references. A root must be consumed
  once in its scope (a borrowed one not at all), it must never be needed twice, and only a
  unique one may be consumed as unique (`leave`).

  The body of a join point is checked like the body of a function whose parameters include
  the variables it captures: unique if the body uses them as unique, borrowed if their owner
  is borrowed and the body does not consume them (a join point is not recursive and runs in
  the scope of its definition), and owned otherwise, with as many references as the body
  consumes (Γ_c is a multiset). The jumps use them in the same way, so a `let` before the
  join point is unique if the body uses its variable as unique. A jump is checked like a call that also passes the
  captured variables.

  Descriptions need no check here: a root is bound only once in a definition (`Check`) and
  the variables at its paths always denote its parts, so a name in a description denotes the
  same value everywhere. Only a jump binds variables again, the parameters of its join point,
  which descriptions in their types do not name (`[join]`).

  This checks the modes of the typing rules in `Syntax` (the types are checked by `Check`).
  Keep it in sync with the rules: a change here must be reflected there, and vice versa.
-}
module Backend.Typed.Linear( checkLinear ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( unless, when, forM_, foldM )
import Data.List( inits )
import Data.Functor.Const( Const(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env(..), Gamma, envOf, bindAll, inferV, inferA, inferVar, inferAVar, altTypes, unboxRuBinds, paramModes, trivialTy )

-- the mode of the variables at and below each owner: the roots in scope, and in the body of a
-- join point the variables it captures
type Owners = M.Map Path Mode

-- the parts of a trivial type, recorded where they are bound (a path denotes the same part in
-- the whole definition, see `Syntax.Path`)
type Trivial = S.Set Path

-- numbers of references to variables (`key`), without zeros; a reference to a variable is one
-- to each of its parts (`refine`)
type Counts = M.Map Path Int

-- How a term uses variables: the references it consumes (negative for those it creates with
-- `dup`), the references that must exist before it (a consumed or inspected variable needs
-- one), and the variables that it borrows and that it consumes as unique.
data Use = Use{ uNet :: Counts, uPeak :: Counts, uBorrowed :: S.Set Path, uUnique :: S.Set Path }

type L a = M Owners Trivial a

-- the modes of the parameters of the join points in scope, and the variables they capture
-- with their modes
type Joins = M.Map Name ([Mode],[(Path,Mode)])

checkLinear :: Program -> [String]
checkLinear prog
  = [show (defName d) ++ ": " ++ err | d <- progDefs prog, Left err <- [checkDef (envOf prog) d]]

checkDef :: Env -> Def -> Either String ()
checkDef env def
  = case def of
      DefFun _ _ args _ body
        -> run (M.fromList [(x,V t) | (x,_,t) <- args]) (params env args) body
      DefVal _ _ _ body -> run M.empty [] body
  where
    run g ps body = evalM (closed ps (checkE env g M.empty body)) M.empty S.empty

-- the parameters that are not of a trivial type
params :: Env -> [(Path,Mode,VType)] -> [(Path,Mode)]
params env ps = [(x,m) | (x,m,t) <- ps, not (trivialTy env (V t))]

-- The parts of a trivial type beside the way from a variable to its part `x`, from the type of
-- the variable: a projection leaves the products on its way unbound.
trivialSiblings :: Env -> Gamma -> Path -> Path -> [Path]
trivialSiblings env g z@(Path _ zs) (Path _ xs)
  = case M.lookup z g of
      Just (V t) -> [q | (pre,s) <- zip (inits steps) steps, Just s' <- [sibling s]
                       , Just u <- [partAt t (pre ++ [s'])], trivialTy env (V u)
                       , let q = foldl child z (pre ++ [s'])]
      _ -> []
  where
    steps = drop (length zs) xs

-- references

-- the other part of the parent of a variable, unless it is of a trivial type
siblingOf :: Trivial -> Path -> Maybe Path
siblingOf tr (Path x ss@(_:_))
  | Just t <- sibling (last ss), let q = Path x (init ss ++ [t]), S.notMember q tr = Just q
siblingOf _ _ = Nothing

-- A part without a sibling (that is not of a trivial type) is all of its parent, so a use of
-- it is a use of the parent: references are counted for the parent.
key :: Trivial -> Path -> Path
key tr p@(Path x ss)
  | not (null ss), Nothing <- siblingOf tr p = key tr (Path x (init ss))
  | otherwise = p

keyOf :: Path -> L Path
keyOf x = gets (\tr -> key tr x)

-- the parts of `p` on the way to a variable `q` below it, which together make up `p`
partsToward :: Trivial -> Path -> Path -> [Path]
partsToward tr p@(Path _ ss) (Path _ ts) = go p (drop (length ss) ts)
  where
    go v [] = [v]
    go v (s:rest) = [key tr q | Just q <- [siblingOf tr (child v s)]] ++ go (child v s) rest

-- Count the references to a variable with one of the `keys` (or another variable of the
-- counts) below it as references to its parts.
refine :: Trivial -> [Path] -> Counts -> Counts
refine tr keys m
  = case [(p,q) | p <- M.keys m, q <- keys ++ M.keys m, q /= p, q `within` p] of
      ((p,q):_) -> refine tr keys (M.filter (/= 0) (M.unionWith (+) (M.delete p m) (M.fromList [(r,m M.! p) | r <- partsToward tr p q])))
      [] -> m

-- Count the references to all parts of a variable as references to the variable, so that
-- alternatives that take a variable apart differently agree on it.
rollUp :: Trivial -> Counts -> Counts
rollUp tr m
  = case [(p,q,n) | (p,n) <- M.toList m, Just q <- [siblingOf tr p], M.lookup q m == Just n] of
      -- parts of different alternatives of a variable only meet in the maximum of `upper`
      ((p,q@(Path x ss),n):_) -> rollUp tr (M.filter (/= 0) (M.insertWith max (key tr (Path x (init ss))) n (M.delete p (M.delete q m))))
      [] -> m

plus :: Trivial -> Counts -> Counts -> Counts
plus tr a b = rollUp tr (refine tr [] (M.filter (/= 0) (M.unionWith (+) (refine tr (M.keys b) a) (refine tr (M.keys a) b))))

minus :: Trivial -> Counts -> Counts -> Counts
minus tr a b = plus tr a (M.map negate b)

-- the larger number of references to each part (a missing one is 0)
upper :: Trivial -> Counts -> Counts -> Counts
upper tr a b = M.filter (> 0) (M.unionWith max (refine tr ks a) (refine tr ks b))
  where
    ks = M.keys a ++ M.keys b

-- uses

noUse :: Use
noUse = Use M.empty M.empty S.empty S.empty

-- `u1` is evaluated before `u2`
andThen :: Use -> Use -> L Use
andThen u1 u2
  = do forM_ (S.toList (uUnique u2)) $ \p ->
         when (any (`S.member` uBorrowed u1) (p : prefixes p))
           (fail ("unique use of a variable after a borrowed use: " ++ show p))
       tr <- get
       return (Use (plus tr (uNet u1) (uNet u2)) (upper tr (uPeak u1) (plus tr (uNet u1) (uPeak u2)))
                   (S.union (uBorrowed u1) (uBorrowed u2)) (S.union (uUnique u1) (uUnique u2)))

-- the uses of terms that are evaluated in order
uses :: [L Use] -> L Use
uses = foldM (\u c -> c >>= andThen u) noUse

-- a term is evaluated before another
before :: L Use -> L Use -> L Use
before c1 c2 = uses [c1,c2]

-- every branch must consume the same references
branches :: [Use] -> L Use
branches us
  = case us of
      (u:rest) -> do tr <- get
                     forM_ rest $ \u' ->
                       unless (M.null (minus tr (uNet u) (uNet u')))
                         (fail ("branches consume different variables: " ++ show (M.toList (uNet u)) ++ " vs. " ++ show (M.toList (uNet u'))))
                     return (Use (uNet u) (foldr1 (upper tr) (map uPeak us)) (S.unions (map uBorrowed us)) (S.unions (map uUnique us)))
      [] -> return noUse

-- Leaving the scope of owners with their mode: an owned one must be consumed once (as unique
-- only if it is unique) and a borrowed one not at all, and neither may be needed when no
-- reference is left.
leave :: [(Path,Mode)] -> Use -> L Use
leave xs u
  = do tr <- get
       let zs = [(key tr x,m) | (x,m) <- xs]
           mine p = any ((p `within`) . fst) zs
           -- each owner holds a reference (a part may be an owner of its own as well)
           held = M.fromListWith (+) [(z,1) | (z,_) <- zs]
           left = refine tr (M.keys held) (minus tr (uNet u) (M.fromListWith (+) [(z,1) | (z,m) <- zs, owning m]))
           peak = refine tr (M.keys held) (uPeak u)
       forM_ (M.toList left) $ \(p,n) ->
         when (mine p) (fail ((if n < 0 then "owned variable is not consumed: " else "variable is consumed more often than it is owned: ") ++ show p))
       forM_ (M.toList peak) $ \(p,n) ->
         when (mine p && n > M.findWithDefault 0 p (refine tr [p] held)) (fail ("use of a consumed variable: " ++ show p))
       forM_ (S.toList (uUnique u)) $ \p -> forM_ zs $ \(z,m) ->
         when (p `within` z && (p /= z || m /= Unique))
           (fail ("unique use of a variable that is not unique: " ++ show p))
       return (Use (M.filterWithKey (\p _ -> not (mine p)) left) (M.filterWithKey (\p _ -> not (mine p)) peak)
                   (S.filter (not . mine) (uBorrowed u)) (S.filter (not . mine) (uUnique u)))

withOwners :: [(Path,Mode)] -> L a -> L a
withOwners xs = local (M.union (M.fromList xs))

-- the scope of binders that are new roots with a mode
roots :: Env -> Mode -> [(Path,Ty)] -> L Use -> L Use
roots env m bs check
  = do let xs = [(x,m) | (x,t) <- bs, not (trivialTy env t)]
       withOwners xs check >>= leave xs

-- a body (of a function or closure) whose only variables are its parameters
closed :: [(Path,Mode)] -> L Use -> L ()
closed ps check
  = do u <- local (const (M.fromList ps)) check
       _ <- leave ps u
       return ()

-- variables

-- the mode of a variable: that of the longest variable on its path that is an owner
ownerMode :: Path -> L Mode
ownerMode x
  = do os <- ask
       case [m | p <- x : reverse (prefixes x), Just m <- [M.lookup p os]] of
         (m:_) -> return m
         [] -> fail ("unbound variable " ++ show x)

trivialVar :: Env -> Gamma -> Path -> Bool
trivialVar env g x = maybe False (trivialTy env) (M.lookup x g)

-- A use of a variable that is not of a trivial type: it consumes `n` references (as unique
-- if the mode is) and borrows the variable if `b`.
useVar :: Env -> Gamma -> Mode -> Int -> Bool -> Path -> L Use
useVar env g m n b x
  | trivialVar env g x = return noUse
  | otherwise
  = do o <- ownerMode x
       when (m == Unique && o == Borrowed) (fail ("unique use of a variable that is not unique: " ++ show x))
       p <- keyOf x
       return (Use (M.filter (/= 0) (M.singleton p n)) (M.singleton p 1) (if b then S.singleton p else S.empty)
                   (if m == Unique then S.singleton p else S.empty))

-- consume a reference
consume, uniqueName :: Env -> Gamma -> Path -> L Use
consume env g = useVar env g Owned 1 False
uniqueName env g = useVar env g Unique 1 False

-- borrow a variable, or only read it
inspect, readVar :: Env -> Gamma -> Path -> L Use
inspect env g = useVar env g Borrowed 0 True
readVar env g = useVar env g Borrowed 0 False

-- `dup x` borrows `x` and gives it another reference
dupVar :: Env -> Gamma -> Path -> L Use
dupVar env g = useVar env g Borrowed (-1) True

-- values

ownedV :: Env -> Gamma -> VVal -> L Use
ownedV env g val
  = case val of
      Var x -> consume env g x
      DupV _ -> liftE (inferV env g val) >> return noUse   -- a global
      Glob _ _ -> do t <- V <$> liftE (inferV env g val)
                     unless (trivialTy env t) (fail ("owned use of global " ++ show val))
                     return noUse
      UnitV -> return noUse
      Lit _ -> return noUse
      NoReuse _ _ -> return noUse
      Inj _ _ _ -> children
      Pair _ _ -> children
      Ptr _ _ -> children
      Pack _ _ _ -> children
      TyApp _ _ -> children
      Hole -> return noUse
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
                  return noUse
      Lam ps _ e
        -> do unless (all (\(_,m,_) -> m == Owned) ps) (fail ("closure with parameters that are not owned: " ++ show val))
              let caps = S.toList (fvA val)
              closed ([(x,Owned) | x <- caps, not (trivialVar env g x)] ++ params env ps)
                     (checkE env (bindAll [(x,V t) | (x,_,t) <- ps] g) M.empty e)
              uses (map (consume env g) caps)
      UnitA -> return noUse
      InjA _ _ v -> ownedA env g v
      Roll _ v -> ownedA env g v
      Box v -> ownedV env g v
      Scalar v -> ownedV env g v
      OpenCon _ _ v -> ownedV env g v
      BoxAt r v -> uses [consume env g r, ownedV env g v]
      BoxIn x v -> uses [consume env g x, ownedV env g v]

-- a unique value is a unique variable, a fresh context, or a structural value of unique values
uniqueV :: Env -> Gamma -> VVal -> L Use
uniqueV env g val
  = case val of
      Var x -> uniqueName env g x
      UnitV -> return noUse
      Lit _ -> do t <- V <$> liftE (inferV env g val)
                  unless (trivialTy env t) (fail ("unique use of a shared literal: " ++ show val))
                  return noUse
      Inj _ _ w -> uniqueV env g w
      Pair v w -> uses [uniqueV env g v, uniqueV env g w]
      Pack _ _ w -> uniqueV env g w
      Context _ k -> ownedV env g k
      CtxCopy c -> ownedV env g c
      Append c d -> uses [uniqueV env g c, uniqueV env g d]
      _ -> fail ("unique use of a value that is not unique: " ++ show val)

borrowedV :: Env -> Gamma -> VVal -> L Use
borrowedV env g val
  = case val of
      Var x -> inspect env g x
      Glob _ _ -> return noUse
      Lit _ -> return noUse
      UnitV -> return noUse
      TyApp v _ -> borrowedV env g v
      Inj _ _ w -> borrowedV env g w
      Pair v w -> uses [borrowedV env g v, borrowedV env g w]
      Pack _ _ w -> borrowedV env g w
      _ -> fail ("borrowed use of a value that is not structural: " ++ show val)

-- closures only have owned parameters
ownedParams :: AType -> L ()
ownedParams a = unless (all (== Owned) (modes a)) (fail ("closure with parameters that are not owned: " ++ show a))
  where
    modes (AFun ps _) = map fst ps
    modes (AForall _ t) = modes t
    modes _ = []

-- expressions

checkE :: Env -> Gamma -> Joins -> VExpr -> L Use
checkE env g js (UnboxLazy v x e)
  = do t   <- liftE (inferVar g v)
       [[tx]] <- liftE (altTypes env t (UnboxLazy v x e))
       let bs = [(x,tx)]
       before (inspect env g v) (roots env Owned bs (checkE env (bindAll bs g) js e))
-- the binder is a copy of trivial contents, and an owned read consumes the scalar
checkE env g js expr@(Unscalar m z x e)
  = do t <- liftE (inferVar g z)
       [[tx]] <- liftE (altTypes env t expr)
       before ((if owning m then consume else readVar) env g z) (checkE env (bindAll [(x,tx)] g) js e)
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
           destruct env g js m v [(zip xs ts, e) | ((xs,e),ts) <- zip alts tss]
checkE env g js expr
  = case expr of
      Ret v -> ownedV env g v
      -- the binder is unique if it is used as unique (and the value is unique)
      Let x t e1 e2 -> do u2 <- withOwners [(x,Owned)] (checkE env (M.insert x (V t) g) js e2)
                          (m,u1) <- case e1 of
                                      Ret w | S.member x (uUnique u2) -> (,) Unique <$> uniqueV env g w
                                      _ -> (,) Owned <$> checkE env g M.empty e1
                          andThen u1 =<< leave [(x,m) | not (trivialTy env (V t))] u2
      -- the binder is not in scope where an effect yields
      LetYield x t e1 e2 e3
        -> do u2 <- withOwners [(x,Owned)] (checkE env (M.insert x (V t) g) js e2)
                    >>= leave [(x,Owned) | not (trivialTy env (V t))]
              u3 <- checkE env g js e3
              u1 <- checkE env g M.empty e1
              andThen u1 =<< branches [u2, u3]
      Yielded _ -> return noUse
      Call f _ vs -> args [] (paramModes env f (length vs)) vs
      Jump j vs -> case M.lookup j js of
                     Just (ms,caps) -> args caps ms vs
                     Nothing -> fail ("jump to unknown join point " ++ show j)
      -- the captured variables that are not parts of other captured variables
      Join j ps e1 e2 -> do let fvs = S.toList (fvE e1 `S.difference` S.fromList [x | (x,_,_) <- ps])
                            let xs = [x | x <- fvs, not (trivialVar env g x), not (any (\y -> y /= x && x `within` y) fvs)]
                            u <- local (const (M.fromList (params env ps ++ [(x,Unique) | x <- xs])))
                                       (checkE env (bindAll [(x,V t) | (x,_,t) <- ps] g) js e1)
                            caps <- concat <$> mapM (captured u) xs
                            _ <- leave (params env ps ++ caps) u
                            checkE env g (M.insert j ([m | (_,m,_) <- ps],caps) js) e2
      App f vs -> do ft <- liftE (inferVar g f)
                     case ft of
                       A a -> ownedParams a
                       _ -> fail "unboxed function operand"
                     uses (consume env g f : map (ownedV env g) vs)
      Gen _ e -> checkE env g M.empty e
      Drop x e -> before (consume env g x) (checkE env g js e)
      Free r e -> before (consume env g r) (checkE env g js e)
      Dup x e -> do t <- liftE (inferVar g x)
                    liftE (checkDupType t)
                    before (dupVar env g x) (checkE env g js e)
      -- the test reads the variable without borrowing it, which is unique in the first branch
      IsUnique x e1 e2 -> do m <- ownerMode x
                             when (m == Borrowed) (fail ("uniqueness test of a variable that is not owned: " ++ show x))
                             z <- keyOf x
                             u1 <- checkE env g js e1
                             u2 <- checkE env g js e2
                             before (readVar env g x) (branches [u1{ uUnique = S.delete z (uUnique u1) }, u2])
      -- the test reads the credit, which is empty in the second branch: the test consumes it there
      IfFull r e1 e2 -> do u1 <- checkE env g js e1
                           u2 <- before (consume env g r) (checkE env g js e2)
                           before (readVar env g r) (branches [u1, u2])
      -- a unique use of `z`, whose block becomes the credit, a part of `z`
      UnboxRu z r e
        -> do bs <- liftE (unboxRuBinds g z r)
              u <- uniqueName env g z
              before (return u{ uNet = M.empty }) (checkE env (bindAll bs g) js e)
      CaseLit v alts def -> before (borrowedV env g v) (branches =<< mapM (checkE env g js) (def : map snd alts))
      _ -> fail "unexpected destructuring form"
  where
    -- owned and unique arguments (and captured variables) first: a borrowed argument must not
    -- be derived from one of them
    args caps ms vs = uses ([ownedV env g v | (Owned,v) <- zip ms vs] ++
                            [consume env g x | (x,Owned) <- caps] ++
                            [uniqueV env g v | (Unique,v) <- zip ms vs] ++
                            [uniqueName env g x | (x,Unique) <- caps] ++
                            [borrowedV env g v | (Borrowed,v) <- zip ms vs] ++
                            [inspect env g x | (x,Borrowed) <- caps])
    -- A variable is captured unique if the body uses it as unique (the jump then uses it as
    -- unique), borrowed if its owner is borrowed and the body does not consume it, and owned
    -- otherwise, once for each reference that the body consumes.
    captured :: Use -> Path -> L [(Path,Mode)]
    captured u x
      = do o <- ownerMode x
           k <- keyOf x
           let consumed = [n | (p,n) <- M.toList (uNet u), n > 0, p `within` k || k `within` p]
           return (if S.member k (uUnique u) then [(x,Unique)]
                   else if o == Borrowed && null consumed then [(x,Borrowed)]
                   else replicate (maximum (1 : consumed)) (x,Owned))

-- The binders of a destructuring of a variable are its parts, and an owned or unique
-- destructuring consumes those of a trivial type. A unique destructuring consumes its
-- scrutinee as unique, so its alternatives must consume the scrutinee. The binders of a
-- destructuring of another value are new roots with the mode of the destructuring.
destruct :: Env -> Gamma -> Joins -> Mode -> VVal -> [([(Path,Ty)],VExpr)] -> L Use
destruct env g js m v alts
  = case v of
      Var z -> do zc <- keyOf z
                  rs <- sequence [alt zc bs e | (bs,e) <- alts]
                  tr <- get
                  -- where `z` is trivial, it has as many references as in the other alternatives
                  u <- case [u | (False,u) <- rs] of
                         (u0:_) -> let target = M.filterWithKey (\p _ -> p `within` zc) (refine tr [zc] (uNet u0))
                                       adopt u = u{ uNet = plus tr (M.filterWithKey (\p _ -> not (p `within` zc)) (refine tr [zc] (uNet u))) target
                                                  , uPeak = M.filterWithKey (\p _ -> not (p `within` zc)) (refine tr [zc] (uPeak u)) }
                                   in branches [if whole then adopt u else u | (whole,u) <- rs]
                         [] -> branches (map snd rs)
                  if m /= Unique || trivialVar env g z
                    then before (readVar env g z) (return u)
                    else do unless (not (any (`within` zc) (M.keys (refine tr [zc] (minus tr (uNet u) (M.singleton zc 1))))))
                              (fail ("unique destructuring does not consume its scrutinee: " ++ show z))
                            use <- uniqueName env g z
                            return u{ uPeak = upper tr (uPeak use) (uPeak u), uUnique = S.union (uUnique use) (uUnique u) }
                  where
                    -- The parts of a trivial type need no references. A binder of a trivial type
                    -- that is all of `z` (see `key`) makes `z` trivial in its alternative.
                    alt zc bs e
                      = do let ts = [x | (x,t) <- bs, trivialTy env t]
                           modify (S.union (S.fromList (ts ++ concatMap (trivialSiblings env g z . fst) bs)))
                           tr <- get
                           u <- checkE env (bindAll bs g) js e
                           return (not (trivialVar env g z) && any ((== zc) . key tr) ts, u)
      _ -> do let use = case m of
                          Owned -> ownedV env g v
                          Unique -> uniqueV env g v
                          Borrowed -> borrowedV env g v
              before use (branches =<< sequence [roots env m bs (checkE env (bindAll bs g) js e) | (bs,e) <- alts])
