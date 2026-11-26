-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{- Perceus: insert dup and drop instructions.

  The pass works bottom-up: each expression is processed with the set of variables that are
  used after it (`Live`), and returns the variables that it uses besides those. Both sets are
  closed under `needs`: an alias of `z` (its pointer at a boxed type, from `[deref]`,
  `[unroll]`, `[case-a]` or `[split-a]`) is `z` at run time, so a use of it needs `z`.

  At each point, the topmost variables that are still used hold the references (`held`), and
  the variables below them (the paths that pass through them: see `Syntax.Path`) are borrowed
  from them. Borrowed parameters, the binders of destructurings of globals and variables of a
  trivial type hold no references. So a variable gives up its reference at one of three places:
  - where it is consumed and not used later, its last owned occurrence moves the reference
    (`consume`). The live descendants of a variable that moves are duplicated before, and any
    other owned occurrence is duplicated;
  - where it is used last, by a borrowed operand of a call, the reference ends after the call;
  - where it is not used at the start of a scope (`enter`): after a binding, at the start of a
    branch that does not use it, or of a function or join point body. A dead variable is
    dropped; one with live descendants hands its reference over to them (`settle`). A product
    hands it over to its fields, another non-pointer to its bound children (`z.fst` and `z.snd`
    once `z` is destructured), and a pointer duplicates its topmost live descendants and is
    dropped. Where these are in the contents of a box `y` on the way to them (an alias of `z`
    or `z` itself), `y` is dropped instead, which drop specialization turns into a move of the
    duplicated descendants (and `y` into a reuse credit) if `y` is unique.
  So a test such as `is-red(r)` does not duplicate `r`, and a nested pattern reuses the inner
  block where the outer value is dead.

  A destructuring of a variable `x` that only reads it (`Body`) takes over the references that
  end at its start, and ends them in its branches instead: those of the owners of `x`, so
  that a branch that does not use the descendants of `x` that another branch uses drops the
  owner instead of duplicating them, and all of them after a leading read such as `[proj]`.
  Reading the contents of a box or a scalar is always borrowed.

  Variables are duplicated in place (`[dup]`): a duplicated variable keeps its name and gains
  an owned reference, so the paths always show where a variable comes from. A variable at a
  boxed type is duplicated through its pointer, and a pointer is dropped through its longest
  bound alias.

  A variable of a trivial type needs no references, also in the contents of a box, which
  code generation copies out of the block at `[bunbox]`.

  `[lock]` consumes an owned box like any consumer: its contents `z.contents` become owned,
  and its cell is a new owned root. So `lazy-eval-locked` takes the fields of
  the lazy value under evaluation without duplicating them, as Koka's Parc does. A cell is linear: it is never copied, and a
  dead cell is an error (it must be filled by `memoize`, or freed in the unique branch of a
  test, where it is a credit). So is a token, which is never duplicated or dropped.
  `[if-yielding]` moves its token, and each branch owns its new token.

  A closure captures its free variables, and its body is closed: it holds references to its
  captures and owned parameters, and nothing is used after it. The body of a join point is
  closed as well; a jump is like a call, but nothing follows it. Nothing is dropped before
  `unreachable`, which consumes everything.
-}
module Lidar.Passes.Perceus( perceusProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad( foldM, unless )
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( runIdentity )
import Lidar.Name
import Lidar.Syntax
import Lidar.Build( K, compose )
import Lidar.Traversal( Destruct(..), child, descendA, descendE, descendV, destructAOf, destructVOf, dsAlts, dsBuild, dsScrut, fieldsAt, fvA, fvV, lamsV, scrutVar, stepsFrom, takesContents, usedIn, within )
import Lidar.Passes.Common( paramModes, prefixes, trivialTy, NameSupply, defGamma, descendTyped, dropValue, freshFor, perDef, freshPathFrom, lamsTyped, nameChildren, projectAll, renamePath, scopeOf )
import Lidar.Env( Env(..), envOf, M, evalM, get, lift, liftE, put, state, StateT, runStateT )
import Lidar.Query( Gamma, bindAll, inferV, altTypes, lamGamma, lockGamma, uniqueGamma )
import Lidar.Types( inst, isPtr )

type VarSet = S.Set Path

-- The variables used after a point of the program, closed under `needs`.
type Live = VarSet

-- `peJoins`: the parameter modes of the join points in scope; `peBorrowed`: the borrowed roots
-- (borrowed parameters, and the binders of destructurings of globals)
data PEnv = PEnv{ peEnv :: Env, peGamma :: Gamma, peJoins :: M.Map Name [Mode], peBorrowed :: S.Set Name }

type P a = M () NameSupply a

fresh :: String -> P Path
fresh s = state (freshPathFrom ("rc" ++ s))

-- programs

perceusProgram :: Program -> (Program,[String])
perceusProgram prog = perDef (\d -> evalM (perceusDef (envOf prog) d) () (freshFor d)) prog

perceusDef :: Env -> Def -> P Def
perceusDef env def
  = do body <- prepare env (defGamma def) (defBody def)
       case def of
         DefFun{ defArgs = args }
           -> (\b -> def{ defBody = b }) <$> closed (paramEnv env args M.empty) (ownedParams env args) body
         DefVal x tvs t _
           -> DefVal x tvs t <$> closed (PEnv env M.empty M.empty S.empty) [] body

-- Bind what the pass would otherwise rewrite and process again: a borrowed argument of a call
-- and the scrutinee of a literal test that are not `borrowable`, and the scrutinee of a value
-- destructuring that is not a variable or global; and name the binders of a value destructuring by their paths. A closure that captures
-- a variable and a path below it (`v` and `v.f`) captures a new variable bound to `v.f` instead,
-- so that the body holds a reference to each capture: otherwise `v.f` would be borrowed from `v`
-- there, and the body would drop the reference of `v.f` and duplicate it again where it is used.
prepare :: Env -> Gamma -> VExpr -> P VExpr
prepare env g expr
  = case expr of
      _ | (x:_) <- nestedCaptures env g expr
        -> do t <- maybe (fail ("unknown variable " ++ show x)) return (M.lookup x g)
              c <- fresh "c"
              let renamed = runIdentity (descendE pure (lamsV (\_ _ e -> pure (renamePath x c e))) (\_ e -> pure e) expr)
              case t of
                V vt -> prepare env g (Let c vt (Ret (Var x)) renamed)
                A _ -> fail ("captured boxed variable " ++ show x)
      Call f tys vs
        | ((i,v):_) <- [(i,v) | (i,(Borrowed,v)) <- zip [0..] (zip (paramModes env f (length vs)) vs), not (borrowable v)]
        -> bindVal "a" v (\s -> Call f tys (take i vs ++ [Var s] ++ drop (i+1) vs))
      CaseLit v alts def
        | not (borrowable v) -> bindVal "s" v (\s -> CaseLit (Var s) alts def)
      _ | Just ds <- destructVOf expr
        -> case dsScrut ds of
             Var _ -> next (nameChildren expr)
             Glob _ _ -> next (nameChildren expr)
             v -> bindVal "s" v (\s -> dsBuild ds (Var s) (map snd (dsAlts ds)))
      _ -> next expr
  where
    next = descendTyped env g (lamsTyped g (prepare env)) (prepare env)
    bindVal prefix v k = do t <- liftE (inferV env g v)
                            s <- fresh prefix
                            prepare env g (Let s t (Ret v) (k s))

-- the captures of the closures in the operands of an expression that are below another capture
-- of the same closure (and not of a trivial type), and the captures below those. Only those with
-- no capture below them are returned: renaming a capture renames the paths below it in the body,
-- so the captures below it become captures of the new variable first.
nestedCaptures :: Env -> Gamma -> VExpr -> [Path]
nestedCaptures env g expr
  = [x | caps <- capss
       , let nested = [x | x <- caps, any (`elem` caps) (prefixes x), maybe False (not . trivialTy env) (M.lookup x g)]
       , x <- caps, any (`elem` nested) (x : prefixes x), not (any ((x `elem`) . prefixes) caps)]
  where
    capss = getConst (descendE (const (Const [])) (lamsV (\ps r e -> Const [S.toList (fvA (Lam ps r e))])) (\_ _ -> Const []) expr)


-- the environment of the body of a function or join point
paramEnv :: Env -> [(Path,Mode,VType)] -> M.Map Name [Mode] -> PEnv
paramEnv env ps js = PEnv env (M.fromList [(x,V t) | (x,_,t) <- ps]) js (S.fromList [r | (Path r _,Borrowed,_) <- ps])

ownedParams :: Env -> [(Path,Mode,VType)] -> [Path]
ownedParams env ps = [x | (x,m,t) <- ps, owning m, not (trivialTy env (V t))]

typeOfV :: PEnv -> VVal -> P VType
typeOfV pe v = liftE (inferV (peEnv pe) (peGamma pe) v)

tyOfVar :: PEnv -> Path -> P Ty
tyOfVar pe x = maybe (fail ("unknown variable " ++ show x)) return (M.lookup x (peGamma pe))

-- ownership

-- A variable needs references unless its type is trivial, and it can hold one unless its root
-- is borrowed.
ownable :: PEnv -> Path -> Bool
ownable pe x@(Path r _) = S.notMember r (peBorrowed pe) && not (trivialVar pe x)

trivialVar :: PEnv -> Path -> Bool
trivialVar pe x = maybe False (trivialTy (peEnv pe)) (M.lookup x (peGamma pe))

-- Where the live set is `live`, the topmost ownable variables in it hold the references (see
-- the top), and the variables below them are borrowed from them.
held :: PEnv -> Live -> Path -> Bool
held pe live x = ownable pe x && not (any (`S.member` live) (prefixes x))

-- the variables that a use of `xs` needs (without those of a trivial type)
usesOf :: PEnv -> [Path] -> VarSet
usesOf pe xs = needs (S.fromList [x | x <- xs, not (trivialVar pe x)])

-- An alias is its pointer at run time (`keepsPtr`), so a use of it needs the variables that it
-- is an alias of.
needs :: VarSet -> VarSet
needs xs = S.union xs (S.fromList [Path r (take k ss) | Path r ss <- S.toList xs, k <- [0 .. length ss - 1], all keepsPtr (drop k ss)])

-- the topmost alias of a variable: the variable whose reference a use of it takes
aliased :: Path -> Path
aliased (Path r ss) = Path r (reverse (dropWhile keepsPtr (reverse ss)))

-- the steps that keep the pointer of a boxed value (the binder is an alias)
keepsPtr :: Step -> Bool
keepsPtr s
  = case s of
      SDeref -> True
      SRoll -> True
      SInjA _ _ -> True
      SRest -> True
      SLo -> True
      SHi -> True
      SWhnf -> True
      SDelay -> True
      _ -> False

-- a set without `x` and its descendants (which follow it in `Ord Path`)
removeWithin :: Path -> VarSet -> VarSet
removeWithin x s = s `S.difference` S.takeWhileAntitone (`within` x) (S.dropWhileAntitone (< x) s)

-- the topmost proper descendants of `z` in a set
topBelow :: Path -> VarSet -> [Path]
topBelow z s = tops (S.toAscList (S.takeWhileAntitone (`within` z) (S.dropWhileAntitone (<= z) s)))
  where
    tops (x:xs) = x : tops (dropWhile (`within` x) xs)
    tops [] = []

pointer :: Ty -> Bool
pointer t
  = case t of
      V v -> isPtr v
      A _ -> True

-- the children of a variable that are bound and not of a trivial type
childrenOf :: PEnv -> Path -> [Path]
childrenOf pe z
  = [x | (x,t) <- takeWhile ((`within` z) . fst) (M.toAscList (M.dropWhileAntitone (<= z) (peGamma pe)))
       , length (stepsFrom z x) == 1, not (trivialTy (peEnv pe) t)]

-- scope starts

-- A body that nothing follows, which holds the variables `es` at its start.
closed :: PEnv -> [Path] -> VExpr -> P VExpr
closed pe es e
  = do (u,b) <- percB pe S.empty e
       enter pe u es b

-- The start of a scope with the live set `live`, where the variables `es` hold references.
-- A live variable keeps its reference, one with live descendants hands it over to them
-- (`settle`), and the others are dropped. The drops come first: dropping one can make another
-- box unique when its fields are taken. Control never reaches `unreachable`, so nothing is
-- dropped before it (also where it is bound by a `let`).
--
-- A read defers these to its branches (see `Body`): a leading read all of them, so that they
-- come after the read; any other destructuring of a variable `x` the dead owners of `x`,
-- so that a branch that does not use the descendants of `x` that are live in another one drops
-- the owner instead of duplicating them first (in a nested match, for example).
enter :: PEnv -> Live -> [Path] -> Body -> P VExpr
enter pe live es body
  = do expr <- build body deferred
       if unreachable expr then return expr
         else do expr' <- foldM (\e z -> settle pe live z e) expr (reverse [z | z <- now, usedIn z live])
                 dropNames pe [z | z <- now, not (usedIn z live)] expr'
  where
    unreachable e = case e of
                      Unreachable{} -> True
                      Let _ _ e1 _ -> unreachable e1
                      _ -> False
    zs = [z | z <- S.toList (S.fromList es), S.notMember z live]
    deferred = case body of
                 Read x leading _ -> [z | z <- zs, leading || x `within` z]
                 Done _ -> []
    now = filter (`notElem` deferred) zs

-- The variable `z` is dead, but some of its descendants are live (an alias of `z` would make
-- `z` live, see `needs`). A product hands its reference over to its fields (projecting those
-- that are not bound), another non-pointer to its bound children. Otherwise its topmost live
-- descendants are duplicated and `z` is dropped; or, if they are in the contents of a box on
-- the way to them (an alias of `z` or `z` itself), the box is dropped instead, which drop
-- specialization turns into a move of the duplicated descendants if the box is unique.
settle :: PEnv -> Live -> Path -> VExpr -> P VExpr
settle pe live z body
  = do t <- tyOfVar pe z
       case t of
         V v@VProd{} -> do
           let fields = [f | f@(_,_,s) <- fieldsAt z v, not (trivialTy (peEnv pe) (V s))]
               missing = [f | f@(y,_,_) <- fields, M.notMember y (peGamma pe)]
           projectAll M.empty z missing <$> enter (bind pe [(y,V s) | (y,_,s) <- missing]) live [y | (y,_,_) <- fields] (Done body)
         _ | not (pointer t) -> enter pe live (childrenOf pe z) (Done body)
         _ -> do let xs = topBelow z live
                 ys <- dupsOf pe xs
                 body' <- case [p | x <- xs, Just p <- [contentsOn x]] of
                            (Path r ss:_) -> return (Drop (Path r (init ss)) body)
                            [] -> dropNames pe [z] body
                 return (compose (map Dup ys) body')
  where
    contentsOn x = case break (not . keepsPtr) (stepsFrom z x) of
                     (as,SContents:_) -> Just (foldl child z (as ++ [SContents]))
                     _ -> Nothing

-- Discard variables using their types, expanding unboxed aggregates into moves. An
-- aggregate whose children are bound is discarded by discarding its children. A product
-- may have only one projection in scope, so expand its drop to cover all fields. A pointer
-- is discarded through its longest bound alias that is not trivial, whose type shows the most
-- of it.
dropNames :: PEnv -> [Path] -> VExpr -> P VExpr
dropNames pe xs e = foldM (\body x -> step body (longestAlias x)) e (reverse xs)
  where
    longestAlias x = last (x : [y | (y,_) <- takeWhile ((`within` x) . fst) (M.toAscList (M.dropWhileAntitone (<= x) (peGamma pe)))
                                  , all keepsPtr (stepsFrom x y), not (trivialVar pe y)])
    step body x = do t <- tyOfVar pe x
                     case t of
                       V (VCell _ _) -> fail ("a cell that is not filled: " ++ show x)
                       _ -> return ()
                     let discard = dropValue (trivialTy (peEnv pe)) (fresh "d") (scopeOf (M.keys (peGamma pe))) x t body
                     case (t,childrenOf pe x) of
                       (V VProd{},_) -> discard
                       (_,ps@(_:_)) | not (pointer t) -> dropNames pe ps body
                       _ -> discard

-- expressions

-- An expression with duplications and drops, or a read: a destructuring of a variable, which
-- can still take owners whose references end at its start, to end them in its branches
-- instead (`enter`). `Read x leading build`: the scrutinee `x`, whether the read is a leading
-- one (it only binds part of `x` for its body), and the expression with the deferred owners.
data Body = Done VExpr | Read Path Bool ([Path] -> P VExpr)

build :: Body -> [Path] -> P VExpr
build (Done e) _ = return e
build (Read _ _ k) d = k d

-- `percB pe live e` inserts duplications and drops into `e`, after which the variables `live`
-- are used. It returns the variables that `e` uses besides those, closed under `needs`.
percB :: PEnv -> Live -> VExpr -> P (VarSet,Body)
percB pe live expr
  = case readOf expr of
      Just x -> percRead pe live x expr
      Nothing -> fmap Done <$> percExpr pe live expr

percE :: PEnv -> Live -> VExpr -> P (VarSet,VExpr)
percE pe live expr
  = do (u,b) <- percB pe live expr
       (,) u <$> build b []

-- the scrutinee of a destructuring of a variable that only reads it
readOf :: VExpr -> Maybe Path
readOf expr
  = case takesContents expr of
      Just _ -> Nothing
      Nothing -> scrutVar expr

-- reads of part of a variable for the body (`[proj]`, `[bunbox]`, `[unscalar]`, and `[deref]`
-- for an `[unscalar]`)
leadingRead :: VExpr -> Bool
leadingRead expr
  = case expr of
      Proj (Var _) _ _ _ -> True
      Unbox{} -> True
      Unscalar{} -> True
      Deref (Var _) x (Unscalar z _ _) -> x == z
      _ -> False

percExpr :: PEnv -> Live -> VExpr -> P (VarSet,VExpr)
percExpr pe live expr
  = case expr of
      Unreachable _ -> return (S.empty,expr)
      Ret v -> operation pe live [(Owned,v)] (\[v'] -> Ret v')
      -- the duplications at the start of `e1` come before the `let`, so that it binds a value
      -- where it can (such as a unique one)
      Let x t e1 e2
        -> do let pe2 = bind pe [(x,V t)]
              (u2,e2') <- percB pe2 live e2
              e2'' <- enter pe2 (S.union live u2) (ownedOf pe [(x,V t)]) e2'
              let u2' = removeWithin x u2
              (u1,e1') <- percE pe (S.union live u2') e1
              return (S.union u1 u2', hoistDups (\e1'' -> Let x t e1'' e2'') e1')
      Call f tys vs
        -> do (u,k,vs',ending) <- consume pe live (zip (paramModes (peEnv pe) f (length vs)) vs)
              let call = Call f tys vs'
              if null ending then return (u,k call)
                else do r <- fresh "r"
                        t <- resultOfCall pe f tys
                        (,) u . k . Let r t call <$> enter pe live ending (Done (Ret (Var r)))
      Jump j ts vs
        -> do ms <- maybe (fail ("unknown join point " ++ show j)) return (M.lookup j (peJoins pe))
              operation pe live (zip ms vs) (Jump j ts)
      App f vs -> operation pe live ((Owned,Var f) : [(Owned,v) | v <- vs]) (App f . drop 1)
      Append c d -> operation pe live [(Unique,c),(Unique,d)] (\[c',d'] -> Append c' d')
      Plug c v -> operation pe live [(Unique,c),(Owned,v)] (\[c',v'] -> Plug c' v')
      CtxCopy c -> operation pe live [(Owned,c)] (\[c'] -> CtxCopy c')
      Memoize c d i v -> operation pe live [(Owned,c),(Owned,v)] (\[c',v'] -> Memoize c' d i v')
      Join j tvs ps e1 e2
        -> do e1' <- closed (paramEnv (peEnv pe) ps (peJoins pe)) (ownedParams (peEnv pe) ps) e1
              fmap (Join j tvs ps e1') <$> percE pe{ peJoins = M.insert j [m | (_,m,_) <- ps] (peJoins pe) } live e2
      -- closed bodies, in which only the group is in scope
      JoinRec t ds e
        -> do let group = M.fromList [(j,[m | (_,m,_) <- ps]) | JoinDef j _ ps _ <- ds]
              ds' <- mapM (\d -> (\b -> d{ joinBody = b }) <$> closed (paramEnv (peEnv pe) (joinParams d) group) (ownedParams (peEnv pe) (joinParams d)) (joinBody d)) ds
              fmap (JoinRec t ds') <$> percE pe{ peJoins = M.union group (peJoins pe) } live e
      Gen tvs e -> fmap (Gen tvs) <$> percE pe live e
      CastEv u t e -> fmap (CastEv u t) <$> percE pe live e
      Total k e
        -> do let pe' = bind pe [(k,V VToken)]
              (u,e') <- percB pe' live e
              (,) (removeWithin k u) . Total k <$> enter pe' (S.union live u) [k] e'
      -- the token moves into the test, and each branch owns its new token
      IfYielding v (k3,e3) (k2,e2)
        -> do let token k e = Branch (bind pe [(k,V VToken)]) [k] [k] e
              (u,[e3',e2']) <- branches pe live (usesOf pe (S.toList (fvV v))) [token k3 e3, token k2 e2] []
              return (u,IfYielding v (k3,e3') (k2,e2'))
      CaseLit v alts def
        -> do (u,es) <- branches pe live (usesOf pe (S.toList (fvV v))) [Branch pe [] [] e | e <- map snd alts ++ [def]] []
              return (u,CaseLit v (zip (map fst alts) es) (last es))
      -- `Lazy` frees a unique cell: the cell becomes a credit, which `free` consumes
      IsUnique x e1 e2
        -> do (u,[e1',e2']) <- branches pe live (usesOf pe [x]) [Branch pe{ peGamma = uniqueGamma (peGamma pe) x } [] [] e1, Branch pe [] [] e2] []
              return (u,IsUnique x e1' e2')
      Free r e
        -> do (u,e') <- percE pe live e
              return (S.union u (usesOf pe [r] `S.difference` live), Free r e')
      -- the box splits into its contents and its cell, which hold references in its place
      Lock z e
        -> do g' <- liftE (lockGamma (peGamma pe) z)
              let pe' = pe{ peGamma = g' }
                  children = [x | x <- [child z SContents, child z SCredit], M.member x g']
              (u,e') <- percB pe' live e
              let uses = S.union (removeWithin z u) (usesOf pe [z] `S.difference` live)
              unless (held pe (S.union live uses) (aliased z) && not (usedIn (aliased z) live))
                (fail ("lock of a box that is not owned: " ++ show z))
              (,) uses . Lock z <$> enter pe' (S.union live u) (ownedOf pe' [(x,t) | x <- children, Just t <- [M.lookup x g']]) e'
      -- the binders of a destructuring of a global are roots that borrow it
      _ | Just ds <- destructVOf expr
        -> do let v = dsScrut ds
              t <- typeOfV pe v
              tss <- liftE (altTypes (peEnv pe) (V t) expr)
              let branch (xs,e) ts = Branch (bind pe{ peBorrowed = S.union (S.fromList [r | Path r _ <- xs]) (peBorrowed pe) } (zip xs ts)) xs [] e
              (u,es) <- branches pe live (usesOf pe (S.toList (fvV v))) (zipWith branch (dsAlts ds) tss) []
              return (u,dsBuild ds v es)
      -- only Perceus inserts these
      Dup{} -> unexpected
      Drop{} -> unexpected
      IfFull{} -> unexpected
      UnboxRu{} -> unexpected
      CopyRu{} -> unexpected
      _ -> fail "unexpected destructuring form"
  where
    unexpected = fail ("unexpected form before Perceus: " ++ show expr)

-- A read of `x`, whose branches end the owners deferred to it (`enter`); the descendants of
-- these do not hold references.
percRead :: PEnv -> Live -> Path -> VExpr -> P (VarSet,Body)
percRead pe live x expr
  = case expr of
      _ | Just ds <- destructAOf expr
        -> do t <- tyOfVar pe x
              tss <- liftE (altTypes (peEnv pe) t expr)
              (u,k) <- branchesB pe live (usesOf pe [x]) [Branch (bind pe (zip xs ts)) xs [] e | ((xs,e),ts) <- zip (dsAlts ds) tss]
              return (u,Read x (leadingRead expr) (fmap (dsBuild ds x) . k))
        | Just ds <- destructVOf expr
        -> do t <- typeOfV pe (Var x)
              tss <- liftE (altTypes (peEnv pe) (V t) expr)
              (u,k) <- branchesB pe live (usesOf pe [x]) [Branch (bind pe (zip xs ts)) xs [] e | ((xs,e),ts) <- zip (dsAlts ds) tss]
              return (u,Read x (leadingRead expr) (fmap (dsBuild ds (Var x)) . k))
      _ -> fail ("not a read: " ++ show expr)

-- the duplications at the start of an expression, before the rest of it
hoistDups :: (VExpr -> VExpr) -> VExpr -> VExpr
hoistDups k expr
  = case expr of
      Dup x e -> Dup x (hoistDups k e)
      _ -> k expr

-- branches

-- A branch of a node: its environment, its binders, those of them that enter it with a
-- reference (roots), and its body. The binders of a destructuring of a variable are below it.
data Branch = Branch PEnv [Path] [Path] VExpr

-- A node that inspects `scrut` and continues in one of its branches, after which the variables
-- `live` are used. The variables that hold references at the node and are used only in some
-- branches (or only by the node) end in the others, at their starts.
-- The owners deferred to the node (`deferred`) end in the branches as well.
branches :: PEnv -> Live -> VarSet -> [Branch] -> [Path] -> P (VarSet,[VExpr])
branches pe live scrut bs deferred
  = do (u,k) <- branchesB pe live scrut bs
       (,) u <$> k deferred

-- the uses of a branching node, and its branches given the owners deferred to it
branchesB :: PEnv -> Live -> VarSet -> [Branch] -> P (VarSet,[Path] -> P [VExpr])
branchesB pe live scrut bs
  = do rs <- mapM (\(Branch pe' _ _ e) -> percB pe' live e) bs
       let uses = S.unions ((scrut `S.difference` live) : [foldr removeWithin u xs | (Branch _ xs _ _,(u,_)) <- zip bs rs])
           enterAll d = sequence [enter pe' (S.union live u) (endingBelow pe live uses d ++ new) b | (Branch pe' _ new _,(u,b)) <- zip bs rs]
       return (uses,enterAll)

-- The variables that hold references before a node with the uses `uses`, but not after it,
-- with the owners `deferred` to the node, whose descendants do not hold references.
endingBelow :: PEnv -> Live -> VarSet -> [Path] -> [Path]
endingBelow pe live uses deferred
  = deferred ++ [x | x <- S.toList uses, held pe (S.union live uses) x, not (any (x `within`) deferred)]

-- duplications

-- the variables among `xs` that need a reference to be duplicated
dupsOf :: PEnv -> [Path] -> P [Path]
dupsOf pe xs = concat <$> mapM one xs
  where
    one x = do t <- tyOfVar pe x
               case t of
                 _ | trivialTy (peEnv pe) t -> return []
                 V (VCell _ _) -> fail ("duplication of a cell: " ++ show x)
                 _ -> return [x]

-- values

-- A node that consumes its owned operands, after which `live` is used.
operation :: PEnv -> Live -> [(Mode,VVal)] -> ([VVal] -> VExpr) -> P (VarSet,VExpr)
operation pe live mvs build
  = do (u,k,vs,ending') <- consume pe live mvs
       unless (null ending') (fail ("borrowed operands that are not used later: " ++ show ending'))
       return (u,k (build vs))

-- The owned operands of a node, after which `live` is used, and its borrowed operands, which
-- are used while it runs. Each variable that holds a reference before the node and is not used
-- during or after it moves at one of its owned occurrences (`movers`); the other occurrences
-- are duplicated. The live descendants of a variable that moves (those used during or after the
-- node) are duplicated before. Returns the uses, the duplications, the operands, and the
-- variables that hold references while the node runs but not after it.
consume :: PEnv -> Live -> [(Mode,VVal)] -> P (VarSet,K,[VVal],[Path])
consume pe live mvs
  = do let owned = concat [occurrences v | (m,v) <- mvs, owning m]
           borrowed = usesOf pe (concat [occurrences v | (Borrowed,v) <- mvs])
           uses = S.union (usesOf pe owned) borrowed `S.difference` live
           during = S.union live borrowed
           moving = movers pe (S.union live uses) during owned
       ys <- dupsOf pe (concat [topBelow (aliased x) during | x <- M.keys moving])
       (k,vs) <- useVals pe moving mvs
       return (uses, compose (map Dup ys) . k, vs, [x | x <- S.toList borrowed, S.notMember x live, held pe during x])

-- The owned occurrence (by its index) that moves the reference of each variable that holds one
-- before a node (live set `before`) and is not used during or after it (`during`). A use of an
-- alias takes the reference of the variable it is an alias of; the shortest alias moves, at
-- its last occurrence.
movers :: PEnv -> Live -> Live -> [Path] -> M.Map Path Int
movers pe before during owned
  = M.fromList [xi | (z,xi) <- M.toList candidates, held pe before z, S.notMember z during]
  where
    candidates = M.fromListWith later [(aliased x,(x,i)) | (i,x) <- zip [0::Int ..] owned]
    later new@(x,_) old@(y,_) = if depth y < depth x then old else new
    depth (Path _ ss) = length ss

useVals :: PEnv -> M.Map Path Int -> [(Mode,VVal)] -> P (K,[VVal])
useVals pe moving mvs
  = do (k,_,vs) <- foldM (\(k,i,acc) (m,v) -> do (k',i',v') <- useVal pe moving m i v
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
useVal pe moving Unique i v = useVal pe moving Owned i v
useVal pe moving Owned i val
  = case val of
      Var x | M.lookup x moving == Just i -> return (id,i+1,val)
            | otherwise -> do ys <- dupsOf pe [x]
                              return (compose (map Dup ys),i+1,val)
      Glob _ _ -> do t <- typeOfV pe val
                     return (id,i,if trivialTy (peEnv pe) (V t) then val else DupV val)
      DupV _ -> return (id,i,val)
      _ -> useChildren pe moving i (descendV (stepA pe moving) (stepV pe moving) val)

-- A closure captures its free variables, and its body holds references to them and to its
-- parameters (no capture is below another one, see `prepare`). Only the captures are in scope
-- in the body (`lamGamma`), so that its drops do not name aliases bound outside it.
useA :: PEnv -> M.Map Path Int -> Int -> AVal -> P (K,Int,AVal)
useA pe moving i val
  = case val of
      Lam ps r e
        -> do let caps = S.toList (fvA val)
                  inner = PEnv (peEnv pe) (lamGamma ps e (peGamma pe)) M.empty S.empty
                  own = [x | x <- caps, not (trivialVar pe x)]
              ys <- dupsOf pe [x | (x,j) <- zip caps [i..], M.lookup x moving /= Just j]
              e' <- closed inner (ownedParams (peEnv pe) ps ++ own) e
              return (compose (map Dup ys), i + length caps, Lam ps r e')
      _ -> useChildren pe moving i (descendA stepName (stepA pe moving) (stepV pe moving) val)
  where
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

-- a borrowed argument that needs no binding: an atom (but not a literal that allocates), or an
-- upcast of one (the same pointer, as an argument of type `any`), which stays borrowed: binding
-- it would own it, so a call of Lean's `isExclusiveUnsafe` would see the extra reference
borrowable :: VVal -> Bool
borrowable (Var _) = True
borrowable (Glob _ _) = True
borrowable (Lit l) = not (litAllocates l)
borrowable UnitV = True
borrowable (Up v) = borrowable v
borrowable _ = False

resultOfCall :: PEnv -> Name -> [AType] -> P VType
resultOfCall pe f tys
  = case M.lookup f (envSigs (peEnv pe)) of
      Just (SigFun tvs _ _ r) -> return (inst tvs tys r)
      _ -> fail ("unknown function " ++ show f)

-- environment

bind :: PEnv -> [(Path,Ty)] -> PEnv
bind pe bs = pe{ peGamma = bindAll bs (peGamma pe) }

ownedOf :: PEnv -> [(Path,Ty)] -> [Path]
ownedOf pe bs = [x | (x,t) <- bs, not (trivialTy (peEnv pe) t)]
