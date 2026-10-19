-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Expansion of reuse (after `JoinArgs`), as in Lean's `ExpandResetReuse`.

  The credits of `Reuse` come from uniqueness tests (`if-unique z`) and may be empty. Each
  allocation in a credit that may be empty is bound by its own join point (Lean's `reusejp`),
  and both branches of a test of the credit (`[if-full]`) jump to it:

    f(.., ptr box@r v, ..)   becomes   join j(x) = f(.., x, ..) in
                                       if-full r then jump j(ptr box@r v)
                                       else jump j(ptr box v)

  In the first branch the credit is full, so code generation writes its block in place
  without a test, and only stores the fields that its description does not already hold
  (Lean's fast path); in the second branch it is empty and the box is allocated freshly
  (the slow path). Only the allocation is copied: the rest of the statement (a `ret`, call,
  application or jump, or a `let` of a `ret`, call or application together with its body) is
  the body of the join point, which captures its variables. A `let` of the allocation itself
  binds its variable by the join point instead. Nested allocations in credits are bound
  innermost first, and the other allocations inside one (fresh boxes and closures) are bound
  by a `let` before the test, so that each branch only writes the credit's own block.

  The blocks on the path of a context `ctx K` to its hole cannot be bound by themselves, as the
  hole must stay in `K`. The whole context is bound instead, by a unique parameter: its other
  allocations are bound first, and the context is copied for each credit on its path that may
  be empty (in practice there is at most one).

  The alternatives of a case that differ only in an allocation in the same credit, such as
  `f(MkLo@r(x,k))` and `f(MkHi@r(x,k))`, share one join point, and the test of the credit is
  done before the case. Where their tags differ, the description of the credit forgets its
  tag, so that every alternative writes the tag and the C compiler can select it without a
  branch.

  The test that made the credit is Lean's `reset`, which `DropSpec` and `Reuse` already expand.
  A credit is full where it is bound at a full type (`◆n`), by `[unbox-ru]`, and in the first
  branch of a test.
-}
module Backend.Typed.Passes.ExpandReuse( expandReuseProgram ) where

import qualified Data.Set as S
import Data.List( nub )
import Data.Monoid( First(..), Any(..) )
import Data.Functor.Const( Const(..) )
import Control.Applicative( (<|>) )
import Control.Monad( when )
import Control.Monad.State
import Data.Functor.Identity( Identity(..) )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common

-- the credits in scope that are full
type Full = S.Set Path

-- a counter for fresh names, and the credits whose descriptions forget their tags
type X a = State (Int,S.Set Path) a

expandReuseProgram :: Program -> Program
expandReuseProgram prog
  = prog{ progDefs = [d{ defBody = evalState (exE (params d) (defBody d)) (0,S.empty) } | d <- progDefs prog] }
  where
    params d = case d of
                 DefFun{} -> fullOf [(x,t) | (x,_,t) <- defArgs d]
                 DefVal{} -> S.empty

fresh :: String -> X Name
fresh s = state (\(n,u) -> (newHiddenName (s ++ show n), (n+1,u)))

fullOf :: [(Path,VType)] -> Full
fullOf bs = S.fromList [x | (x,VReuse Full _ _) <- bs]

-- the type of a binder, without the tag of its description if a case forgot it
untagged :: Path -> VType -> X VType
untagged x t
  = do u <- gets snd
       return (case t of
                 VReuse f n (Just (Contents _ v s)) | S.member x u -> VReuse f n (Just (Contents Nothing v s))
                 _ -> t)

exE :: Full -> VExpr -> X VExpr
exE full expr
  = case expr of
      Ret _ -> statement expr >>= allocate full
      Call{} -> statement expr >>= allocate full
      App{} -> statement expr >>= allocate full
      Jump{} -> statement expr >>= allocate full
      Let x t e1 e2 | isStatement e1
        -> do e1' <- statement e1
              e2' <- exE (S.union full (fullOf [(x,t)])) e2
              allocate full (Let x t e1' e2')
      Let x t e1 e2 -> do e1' <- exE full e1
                          e2' <- exE (S.union full (fullOf [(x,t)])) e2
                          t' <- untagged x t
                          return (Let x t' e1' e2')
      Join j ps e1 e2 -> do e1' <- exE (S.union full (fullOf [(x,t) | (x,_,t) <- ps])) e1
                            ps' <- mapM (\(x,m,t) -> (,,) x m <$> untagged x t) ps
                            Join j ps' e1' <$> exE full e2
      UnboxRu z r e -> UnboxRu z r <$> exE (S.insert r full) e
      IfFull r e1 e2 -> IfFull r <$> exE (S.insert r full) e1 <*> exE full e2
      CaseV{} -> alternatives
      CaseA{} -> alternatives
      SplitA{} -> alternatives
      CaseLit{} -> alternatives
      _ -> descendE pure exV (\_ e -> exE full e) expr
  where
    alternatives = do alts <- mapM (\e -> if isStatement e then statement e else return e) (arms expr)
                      case shared full alts of
                        Just alloc -> merge full (withArms expr alts) alloc
                        Nothing -> descendE pure exV (\_ e -> exE full e) expr

-- a statement, whose closures are expanded
statement :: VExpr -> X VExpr
statement = descendE pure exV (\_ e -> return e)

isStatement :: VExpr -> Bool
isStatement e
  = case e of
      Ret _ -> True
      Call{} -> True
      App{} -> True
      Jump{} -> True
      _ -> False

-- closures get no credits
exV :: VVal -> X VVal
exV = descendV exA exV

exA :: AVal -> X AVal
exA val
  = case val of
      Lam ps r e -> Lam ps r <$> exE (fullOf [(x,t) | (x,_,t) <- ps]) e
      _ -> descendA pure exA exV val

-- Bind each allocation of a statement in a credit that may be empty by a join point.
allocate :: Full -> VExpr -> X VExpr
allocate full stmt
  = case pick full stmt of
      Nothing -> return stmt
      Just (u,_,_) | Let x t (Ret v) e <- stmt, v == u
        -> do j <- fresh "reusejp"
              (u',bs) <- hoist u
              return (lets bs (Join j [(x,modeOf u,t)] e (test full (Jump j [u']))))
      Just (u,m,t)
        -> do j <- fresh "reusejp"
              x <- root <$> fresh "alloc"
              e <- allocate full (replace u (Var x) stmt)
              (u',bs) <- hoist u
              return (lets bs (Join j [(x,m,t)] e (test full (Jump j [u']))))
  where
    modeOf u = case u of
                 Context{} -> Unique
                 _ -> Owned

-- Alternatives that are the same statement up to an allocation in the same credit `r` jump to
-- one join point, after one test of `r`.
merge :: Full -> VExpr -> (Path,Mode,VType,VVal -> VExpr,[VVal]) -> X VExpr
merge full expr (r,m,t,stmt,us)
  = do j <- fresh "reusejp"
       x <- root <$> fresh "alloc"
       e <- allocate full (stmt (Var x))
       hs <- mapM hoist us
       let jumps f = withArms expr [lets bs (f (Jump j [u'])) | (u',bs) <- hs]
       when (length (nub (map tagOf us)) > 1) (modify (\(n,u) -> (n,S.insert r u)))
       return (Join j [(x,m,t)] e (IfFull r (jumps id) (jumps (allocFresh r))))
  where
    tagOf v = case v of
                Context _ k -> tagOf k
                Ptr _ a -> tagA a
                _ -> Nothing
    tagA a = case a of
               Roll _ b -> tagA b
               InjA i _ b -> tagA b <|> Just i
               _ -> Nothing

-- The statements of all alternatives, if they are the same up to an allocation in the same
-- credit (the alternatives bind different paths, so the statement does not use them).
shared :: Full -> [VExpr] -> Maybe (Path,Mode,VType,VVal -> VExpr,[VVal])
shared full alts
  | length alts > 1 && all isStatement alts
  = do ps <- mapM (pick full) alts
       let us = [u | (u,_,_) <- ps]
       r <- case nub (map (tested full . pure) us) of
              [[r]] -> Just r
              _ -> Nothing
       case (nub [(m,t) | (_,m,t) <- ps], nub [replace u (Var hole) e | (u,e) <- zip us alts]) of
         ([(m,t)],[stmt]) -> Just (r,m,t,\v -> replace (Var hole) v stmt,us)
         _ -> Nothing
  | otherwise = Nothing
  where
    hole = root (newHiddenName "alloc")

-- the alternatives of a case
arms :: VExpr -> [VExpr]
arms = getConst . descendE (const (Const [])) (const (Const [])) (\_ e -> Const [e])

withArms :: VExpr -> [VExpr] -> VExpr
withArms expr es = evalState (descendE pure pure (\_ _ -> state next) expr) es
  where
    next (e:rest) = (e,rest)
    next [] = error "Backend.Typed.Passes.ExpandReuse.withArms: too few alternatives"

-- Bind the other allocations of an allocation (beside its path), so that only its own blocks
-- are copied.
hoist :: VVal -> X (VVal,[(Path,VType,VVal)])
hoist u = runStateT (descendV hoistA hoistV u) []
  where
    hoistV v = case v of
                 Ptr a c | holes v == 0 && allocates c
                   -> do y <- lift (root <$> fresh "alloc")
                         modify (++ [(y,VPtr a,v)])
                         return (Var y)
                 _ -> descendV hoistA hoistV v
    hoistA = descendA pure hoistA hoistV

lets :: [(Path,VType,VVal)] -> VExpr -> VExpr
lets bs e = foldr (\(y,t,v) -> Let y t (Ret v)) e bs

-- whether a boxed value allocates a block (closures included)
allocates :: AVal -> Bool
allocates val
  = case val of
      Box _ -> True
      BoxAt _ _ -> True
      OpenCon{} -> True
      Lam{} -> True
      _ -> getAny (getConst (descendA (const (Const (Any False))) (Const . Any . allocates) (Const . Any . allocatesV) val))
  where
    allocatesV = getAny . getConst . descendV (Const . Any . allocates) (Const . Any . allocatesV)

-- the values of a statement; those of a `let` are those of its bound expression
values :: VExpr -> [VVal]
values stmt
  = case stmt of
      Let _ _ e1 _ -> values e1
      _ -> getConst (descendE (const (Const [])) (Const . pure) (\_ _ -> Const []) stmt)

replace :: VVal -> VVal -> VExpr -> VExpr
replace u x stmt
  = case stmt of
      Let y t e1 e2 -> Let y t (replace u x e1) e2
      _ -> runIdentity (descendE pure (Identity . replaceV) (\_ e -> Identity e) stmt)
  where
    replaceV v | v == u = x
               | otherwise = mapV replaceA replaceV v
    replaceA = mapA id replaceA replaceV

-- The first allocation to bind, with the mode and type of its join parameter: a pointer to a
-- box in a credit that may be empty, or a context with such a box on its path, whose values
-- allocate in no other such credit.
pick :: Full -> VExpr -> Maybe (VVal,Mode,VType)
pick full stmt = getFirst (foldMap (First . pickV) (values stmt))
  where
    pickV v = case v of
                Context b k@(Ptr a _) -> pickV k <|> self Unique (VCtx Full a b)
                Ptr a c | holes v == 0, Just r <- boxCredit c, r `S.notMember` full
                  -> inner <|> self Owned (VPtr a)
                _ -> inner
      where
        self m t = if null (tested full [v]) then Nothing else Just (v,m,t)
        inner = getFirst (getConst (descendV (Const . First . pickA) (Const . First . pickV) v))
    pickA a = getFirst (getConst (descendA (const (Const (First Nothing))) (Const . First . pickA) (Const . First . pickV) a))
    boxCredit a = case a of
                    Roll _ b -> boxCredit b
                    InjA _ _ b -> boxCredit b
                    BoxAt r _ -> Just r
                    _ -> Nothing

-- the credits that may be empty and that values allocate in
tested :: Full -> [VVal] -> [Path]
tested full vs = filter (`S.notMember` full) (nub (concatMap credits vs))

-- Test each credit that may be empty and that a statement allocates in.
test :: Full -> VExpr -> VExpr
test full stmt
  = case tested full (values stmt) of
      (r:_) -> IfFull r (test (S.insert r full) stmt) (test full (allocFresh r stmt))
      [] -> stmt

-- the credits that a value allocates in
credits :: VVal -> [Path]
credits = getConst . descendV (Const . creditsA) (Const . credits)
  where
    creditsA val = case val of
                     BoxAt r v -> r : credits v
                     _ -> getConst (descendA (const (Const [])) (Const . creditsA) (Const . credits) val)

-- allocate freshly instead of in an empty credit
allocFresh :: Path -> VExpr -> VExpr
allocFresh r = runIdentity . descendE pure (Identity . freshV) (\_ e -> Identity e)
  where
    freshV = mapV freshA freshV
    freshA val = case val of
                   BoxAt r' v | r' == r -> Box (freshV v)
                   _ -> mapA id freshA freshV val
