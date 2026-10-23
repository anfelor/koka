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
  unrestricted, except that one in the contents of a box `z` (on a path with a `contents`
  step, `boxOf`) is read from the block of `z`: only `val y = dup x`, which loads it, and a
  case on it may read it, and they read the block `z.credit`, unless `UnboxRu` took the
  contents of `z` out of its block (`Taken`). A projection or unpack of it binds a part
  without reading it, and descriptions do not read it. Every other variable is a path (see
  `Syntax.Path`) and has the mode of its owner, the longest variable on its path that is a
  root (or, in the body of a join point, a variable it captures). An owned root holds one
  reference, which must be consumed exactly once on every path; a borrowed root (a borrowed
  parameter, or a binder of a borrowed destructuring of a value that is not a variable) holds
  a reference that may only be inspected.

  The variables at the steps from a variable are its parts: a reference to a variable is one
  reference to each of its parts (both components of a pair, the contents and the credit of a
  box, and the only part at any other step), so consuming a part takes it out of its parent,
  and a parent is consumed once all of its parts are. The binder of `[deref]`, `[unroll]`,
  `[case-a]` or `[split-a]` of a boxed value is the pointer of its scrutinee, and that of
  `[unpack]` is its scrutinee, so consuming or testing it consumes or tests the scrutinee (`key`). So does a part whose
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

  `val y = dup x` borrows `x` and binds its copy `y` as a new owned root, so a variable holds
  at most one reference. The consumed references are sets of variables (`Keys`), where a
  variable stands for all of its parts (`refine`): `z.fst` is left after a `let` that consumes
  the other parts of `z`, for example.

  A unique variable is owned and holds the only reference to its block, so `UnboxRu` may
  take its contents and keep its block as a credit, a new root that consumes the block
  `z.credit` of `z` (the part of `z` beside its contents). An owned variable is unique in the
  first branch of `IsUnique`; unique parameters and a `let` of a unique value (a unique
  variable, a fresh context, an append or `ctx-copy c`) are unique too, and so are the
  pointers of the scrutinee of a unique destructuring. A context is plugged or appended only
  through a unique value. Any borrowed use of a unique variable, or of a variable on its path,
  may duplicate the reference, after which it is only owned.

  The check is bottom-up: a term gives the references it consumes, the variables it needs
  (that it consumes or reads), and the variables it borrows and consumes as unique (`Use`).
  Sequencing (`andThen`) rejects a use of a consumed variable and a unique use after a
  borrowed one. Branches must consume the same references. A root must be consumed in its
  scope (a borrowed one not at all), and only a unique one may be consumed as unique
  (`leave`).

  The body of a join point is checked like the body of a function whose parameters include
  the variables it captures, including those of the join points it jumps to: unique if the
  body uses them as unique, borrowed if the body does not consume them (a join point is not
  recursive and runs in the scope of its definition), and owned otherwise. The jumps use them
  in the same way, so a `let` before the join point is unique if the body uses its variable as
  unique. A jump is checked like a call that also passes the captured variables.

  After `Loads` (`checkLinear True`), the contents of a box are a *place* in its block
  (`Layout.placeBinders`): a use of a place reads the block, so it needs the credit of the
  block (`Places`): the block `z.credit` of the box, which every consumption of `z` consumes,
  or after `[unbox-ru]` the credit that it binds. A field that a projection reads is
  copied out of the block. A join point whose body reads a place also captures its credit,
  borrowed, unless it captures the credit or the box anyway. A closure copies its
  captures when it is created, so its body has no places.

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
import Data.List( inits, partition )
import Data.Functor.Const( Const(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Layout( placeBinders )
import Backend.Typed.Query( Env(..), Gamma, envOf, bindAll, inferV, inferA, inferVar, inferAVar, altTypes, unboxRuBinds, paramModes, trivialTy )

-- the mode of the variables at and below each owner: the roots in scope, and in the body of a
-- join point the variables it captures
type Owners = M.Map Path Mode

-- the parts of a trivial type, recorded where a destructuring binds a part of their parent (a
-- path denotes the same part in the whole definition, see `Syntax.Path`)
type Trivial = S.Set Path

-- variables (`key`) that do not overlap; a variable stands for all of its parts (`refine`)
type Keys = S.Set Path

-- How a term uses variables: the references it consumes, the variables it needs (a consumed
-- or inspected variable needs a reference), and the variables that it borrows and that it
-- consumes as unique.
data Use = Use{ uConsumed :: Keys, uNeeded :: Keys, uBorrowed :: S.Set Path, uUnique :: S.Set Path }

-- the places in scope, with the credits of their blocks (if places are checked)
type Places = Maybe (M.Map Path Path)

-- the boxes whose contents `[unbox-ru]` took out of their blocks
type Taken = S.Set Path

type L a = M (Owners,Places,Taken) Trivial a

-- the modes of the parameters of the join points in scope, and the variables they capture
-- with their modes
type Joins = M.Map Name ([Mode],[(Path,Mode)])

-- whether places must be read while their blocks are live (after `Loads`)
checkLinear :: Bool -> Program -> [String]
checkLinear places prog
  = [show (defName d) ++ ": " ++ err | d <- progDefs prog, Left err <- [checkDef places (envOf prog) d]]

checkDef :: Bool -> Env -> Def -> Either String ()
checkDef places env def
  = case def of
      DefFun _ _ args _ body
        -> run (M.fromList [(x,V t) | (x,_,t) <- args]) (params env args) body
      DefVal _ _ _ body -> run M.empty [] body
  where
    run g ps body = evalM (closed ps (checkE env g M.empty body)) (M.empty,if places then Just M.empty else Nothing,S.empty) S.empty

-- the parameters that are not of a trivial type
params :: Env -> [(Path,Mode,VType)] -> [(Path,Mode)]
params env ps = [(x,m) | (x,m,t) <- ps, not (trivialTy env (V t))]

-- The parts of a trivial type beside the way from a product `p : t` to its part `x`: a
-- projection, and `[case-open]`, leave the products on the way unbound.
trivialSiblings :: Env -> Path -> VType -> Path -> [Path]
trivialSiblings env p@(Path _ ps) t (Path _ xs)
  = [foldl child p ss | (pre,s) <- zip (inits steps) steps, Just s' <- [sibling s]
                      , let ss = pre ++ [s'], Just u <- [partAt t ss], trivialTy env (V u)]
  where
    steps = drop (length ps) xs

-- The product that a destructuring of `z` with binders `bs` takes apart, with its type: `z`
-- for a projection, and `z.C`, the fields of the binders, for `[case-open]`.
destructed :: Gamma -> Path -> [(Path,Ty)] -> Maybe (Path,VType)
destructed g z@(Path _ zs) bs
  = case (M.lookup z g, bs) of
      (Just (V t), _) -> Just (z,t)
      (_, (Path _ ss,_):_:_) | (SOpen c : _) <- drop (length zs) ss
        -> Just (child z (SOpen c), foldr1 VProd [t | (_,V t) <- bs])
      _ -> Nothing

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

-- Split a variable with one of the `keys` (or another variable of the set) below it into its
-- parts.
refine :: Trivial -> [Path] -> Keys -> Keys
refine tr keys s
  = case [(p,q) | p <- S.toList s, q <- keys ++ S.toList s, q /= p, q `within` p] of
      ((p,q):_) -> refine tr keys (S.union (S.delete p s) (S.fromList (partsToward tr p q)))
      [] -> s

-- Replace all parts of a variable by the variable, so that alternatives that take a variable
-- apart differently agree on it.
rollUp :: Trivial -> Keys -> Keys
rollUp tr s
  = case [(p,q) | p <- S.toList s, Just q <- [siblingOf tr p], S.member q s] of
      ((p,q@(Path x ss)):_) -> rollUp tr (S.insert (key tr (Path x (init ss))) (S.delete p (S.delete q s)))
      [] -> s

-- the variables of `a` that share a part with a variable of `b`
overlapping :: Keys -> Keys -> [Path]
overlapping a b = [p | p <- S.toList a, any (\q -> p `within` q || q `within` p) (S.toList b)]

-- uses

noUse :: Use
noUse = Use S.empty S.empty S.empty S.empty

-- `u1` is evaluated before `u2`
andThen :: Use -> Use -> L Use
andThen u1 u2
  = do forM_ (S.toList (uUnique u2)) $ \p ->
         when (any (`S.member` uBorrowed u1) (p : prefixes p))
           (fail ("unique use of a variable after a borrowed use: " ++ show p))
       case overlapping (S.union (uConsumed u2) (uNeeded u2)) (uConsumed u1) of
         (p:_) -> fail ("use of a consumed variable: " ++ show p)
         [] -> return ()
       tr <- get
       return (Use (rollUp tr (S.union (uConsumed u1) (uConsumed u2))) (S.union (uNeeded u1) (uNeeded u2))
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
                       unless (rollUp tr (uConsumed u) == rollUp tr (uConsumed u'))
                         (fail ("branches consume different variables: " ++ show (S.toList (uConsumed u)) ++ " vs. " ++ show (S.toList (uConsumed u'))))
                     return (Use (uConsumed u) (S.unions (map uNeeded us)) (S.unions (map uBorrowed us)) (S.unions (map uUnique us)))
      [] -> return noUse

-- Leaving the scope of owners with their mode: an owned one must be consumed (as unique only
-- if it is unique) and a borrowed one not at all.
leave :: [(Path,Mode)] -> Use -> L Use
leave xs u
  = do tr <- get
       let zs = [(key tr x,m) | (x,m) <- xs]
           mine p = any ((p `within`) . fst) zs
           consumed = refine tr (map fst zs) (uConsumed u)
       forM_ zs $ \(z,m) ->
         case (owning m,filter (`within` z) (S.toList consumed)) of
           (True,ps) | ps /= [z] -> fail ("owned variable is not consumed: " ++ show z)
           (False,p:_) -> fail ("borrowed variable is consumed: " ++ show p)
           _ -> return ()
       forM_ (S.toList (uUnique u)) $ \p -> forM_ zs $ \(z,m) ->
         when (p `within` z && (p /= z || m /= Unique))
           (fail ("unique use of a variable that is not unique: " ++ show p))
       return (Use (S.filter (not . mine) consumed) (S.filter (not . mine) (refine tr (map fst zs) (uNeeded u)))
                   (S.filter (not . mine) (uBorrowed u)) (S.filter (not . mine) (uUnique u)))

withOwners :: [(Path,Mode)] -> L a -> L a
withOwners xs = local (\(os,pl,tk) -> (M.union (M.fromList xs) os,pl,tk))

-- the scope of binders that are places of the boxes (or places) given with them: a place of a
-- box `z` is read through its block `z.credit`
withPlaces :: [(Path,Path)] -> L a -> L a
withPlaces xs = local (\(os,pl,tk) -> (os,fmap (\m -> M.union (M.fromList [(x,M.findWithDefault (child z SCredit) z m) | (x,z) <- xs]) m) pl,tk))

-- the credit that a place is read through
creditOf :: Path -> L (Maybe Path)
creditOf x = asks (\(_,pl,_) -> pl >>= M.lookup x)

-- the scope of binders that are new roots with a mode
roots :: Env -> Mode -> [(Path,Ty)] -> L Use -> L Use
roots env m bs check
  = do let xs = [(x,m) | (x,t) <- bs, not (trivialTy env t)]
       withOwners xs check >>= leave xs

-- a body (of a function or closure) whose only variables are its parameters
closed :: [(Path,Mode)] -> L Use -> L ()
closed ps check
  = do u <- local (\(_,pl,_) -> (M.fromList ps,fmap (const M.empty) pl,S.empty)) check
       _ <- leave ps u
       return ()

-- variables

-- the mode of a variable: that of the longest variable on its path that is an owner
ownerMode :: Path -> L Mode
ownerMode x
  = do os <- asks (\(os,_,_) -> os)
       case [m | p <- x : reverse (prefixes x), Just m <- [M.lookup p os]] of
         (m:_) -> return m
         [] -> fail ("unbound variable " ++ show x)

trivialVar :: Env -> Gamma -> Path -> Bool
trivialVar env g x = maybe False (trivialTy env) (M.lookup x g)

-- A use of a variable: a use of a place first reads its block.
useVar :: Env -> Gamma -> Mode -> Bool -> Path -> L Use
useVar env g m b x
  = do mc <- creditOf x
       case mc of
         Just c -> uses [useRef env g Borrowed False c, useRef env g m b x]
         Nothing -> useRef env g m b x

-- A use of a reference that is not of a trivial type: it consumes the reference if the mode
-- is owned (as unique if the mode is) and borrows the variable if `b`.
useRef :: Env -> Gamma -> Mode -> Bool -> Path -> L Use
useRef env g m b x
  | trivialVar env g x = loaded x
  | otherwise
  = do o <- ownerMode x
       when (m == Unique && o == Borrowed) (fail ("unique use of a variable that is not unique: " ++ show x))
       p <- keyOf x
       return (Use (if owning m then S.singleton p else S.empty) (S.singleton p) (if b then S.singleton p else S.empty)
                   (if m == Unique then S.singleton p else S.empty))

-- A variable of a trivial type in the contents of a box is read from the block of the box, so
-- only a dup or a case may read it (`loadOf`), unless `[unbox-ru]` took the contents out of
-- the block.
loaded :: Path -> L Use
loaded x
  = do tk <- asks (\(_,_,tk) -> tk)
       case boxOf x of
         Just z | S.notMember z tk -> fail ("read of a trivial part of the contents of a box that is not loaded: " ++ show x)
         _ -> return noUse

-- A dup of a variable of a trivial type in the contents of a box `z` loads it: it reads the
-- block `z.credit`, unless `[unbox-ru]` took the contents out of the block.
loadOf :: Env -> Gamma -> Path -> L Use
loadOf env g x
  = do tk <- asks (\(_,_,tk) -> tk)
       case boxOf x of
         Just z | S.notMember z tk -> useRef env g Borrowed False (child z SCredit)
         _ -> return noUse

-- consume a reference
consume, uniqueName :: Env -> Gamma -> Path -> L Use
consume env g = useVar env g Owned False
uniqueName env g = useVar env g Unique False

-- borrow a variable, or only read it
inspect, readVar :: Env -> Gamma -> Path -> L Use
inspect env g = useVar env g Borrowed True
readVar env g = useVar env g Borrowed False

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
      OpenCon _ _ vs -> uses (map (ownedV env g) vs)
      -- the value is evaluated before the block is written
      BoxAt r v -> uses [ownedV env g v, consume env g r]
      BoxIn x v -> uses [ownedV env g v, consume env g x]

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
           pl <- asks (\(_,pl,_) -> pl)
           let isPlace p = maybe False (M.member p) pl
               places = concat [placeBinders isPlace expr xs ts | ((xs,_),ts) <- zip alts tss]
           withPlaces places (destruct env g js m (bindsPart expr) v [(zip xs ts, e) | ((xs,e),ts) <- zip alts tss])
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
      -- the captured variables that are not parts of other captured variables, including those
      -- of the join points that the body jumps to
      Join j ps e1 e2 -> do let fvs = S.toList (S.union (fvE e1 `S.difference` S.fromList [x | (x,_,_) <- ps])
                                                         (S.fromList [x | (k,(_,cs)) <- M.toList js, not (null (jumpArgs k e1)), (x,_) <- cs]))
                            let xs = [x | x <- fvs, not (trivialVar env g x), not (any (\y -> y /= x && x `within` y) fvs)]
                            cs <- mapM creditOf fvs
                            let blocks = S.toList (S.fromList [c | Just c <- cs, not (any (c `within`) xs)])
                            u <- local (\(_,pl,tk) -> (M.fromList (params env ps ++ [(x,Unique) | x <- xs] ++ [(c,Borrowed) | c <- blocks]),pl,tk))
                                       (checkE env (bindAll [(x,V t) | (x,_,t) <- ps] g) js e1)
                            -- a jump reads the captured places before it consumes their credits
                            let (inPlace,others) = partition (`elem` [y | (y,Just _) <- zip fvs cs]) xs
                            caps <- (++ [(c,Borrowed) | c <- blocks]) <$> mapM (captured u) (inPlace ++ others)
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
      -- the copy is a new root
      Dup x y e -> do t <- liftE (inferVar g x)
                      liftE (checkDupType t)
                      before ((if trivialVar env g x then loadOf else inspect) env g x) (roots env Owned [(y,t)] (checkE env (bindAll [(y,t)] g) js e))
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
      -- a unique use of `z` that consumes its block `z.credit` (leaving its contents) and binds
      -- the block as a new root, through which the places of `z` are read; the contents are
      -- taken out of the block, so their trivial parts are loaded
      UnboxRu z r e
        -> do bs <- liftE (unboxRuBinds g z r)
              u <- uniqueName env g z
              c <- keyOf (child z SCredit)
              let credit = local (\(os,pl,tk) -> (os,fmap (M.map (\p -> if p == child z SCredit then r else p)) pl,S.insert z tk))
              before (return u{ uConsumed = S.singleton c }) (credit (roots env Owned bs (checkE env (bindAll bs g) js e)))
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
    -- unique), borrowed if the body does not consume it, and owned otherwise. (An owned
    -- variable that is captured borrowed is not consumed by the jump, which its scope then
    -- rejects.)
    captured :: Use -> Path -> L (Path,Mode)
    captured u x
      = do k <- keyOf x
           return (if S.member k (uUnique u) then (x,Unique)
                   else if null (overlapping (uConsumed u) (S.singleton k)) then (x,Borrowed)
                   else (x,Owned))

-- a projection or an unpack binds a part of its scrutinee without reading it
bindsPart :: VExpr -> Bool
bindsPart expr
  = case expr of
      Proj{} -> True
      Unpack{} -> True
      _ -> False

-- The binders of a destructuring of a variable are its parts, and an owned or unique
-- destructuring consumes those of a trivial type. A unique destructuring consumes its
-- scrutinee as unique, so its alternatives must consume the scrutinee. The binders of a
-- destructuring of another value are new roots with the mode of the destructuring.
destruct :: Env -> Gamma -> Joins -> Mode -> Bool -> VVal -> [([(Path,Ty)],VExpr)] -> L Use
destruct env g js m part v alts
  = case v of
      Var z -> do zc <- keyOf z
                  rs <- sequence [alt zc bs e | (bs,e) <- alts]
                  tr <- get
                  -- where `z` is trivial, it has as many references as in the other alternatives
                  -- where `z` is trivial, it is consumed as in the other alternatives
                  u <- case [u | (False,u) <- rs] of
                         (u0:_) -> let inside = S.filter (`within` zc) . refine tr [zc]
                                       outside = S.filter (not . (`within` zc)) . refine tr [zc]
                                       adopt u = u{ uConsumed = rollUp tr (S.union (outside (uConsumed u)) (inside (uConsumed u0)))
                                                  , uNeeded = outside (uNeeded u) }
                                   in branches [if whole then adopt u else u | (whole,u) <- rs]
                         [] -> branches (map snd rs)
                  if m /= Unique || trivialVar env g z
                    then before scrutinee (return u)
                    else do unless (S.filter (`within` zc) (refine tr [zc] (uConsumed u)) == S.singleton zc)
                              (fail ("unique destructuring does not consume its scrutinee: " ++ show z))
                            use <- uniqueName env g z
                            return u{ uNeeded = S.union (uNeeded use) (uNeeded u), uUnique = S.union (uUnique use) (uUnique u) }
                  where
                    -- a case on a trivial part of the contents of a box reads its block, like a dup
                    scrutinee | not (trivialVar env g z) = readVar env g z
                              | part = return noUse
                              | otherwise = loadOf env g z
                    -- The parts of a trivial type need no references. A binder of a trivial type
                    -- that is all of `z` (see `key`) makes `z` trivial in its alternative.
                    alt zc bs e
                      = do let ts = [x | (x,t) <- bs, trivialTy env t]
                           modify (S.union (S.fromList (ts ++ [q | Just (p,t) <- [destructed g z bs], (x,_) <- bs, q <- trivialSiblings env p t x])))
                           tr <- get
                           u <- checkE env (bindAll bs g) js e
                           return (not (trivialVar env g z) && any ((== zc) . key tr) ts, u)
      _ -> do let use = case m of
                          Owned -> ownedV env g v
                          Unique -> uniqueV env g v
                          Borrowed -> borrowedV env g v
              before use (branches =<< sequence [roots env m bs (checkE env (bindAll bs g) js e) | (bs,e) <- alts])
