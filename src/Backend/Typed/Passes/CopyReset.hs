-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Copying the continuation of a reset into both branches (after `JoinArgs`, before
  `ExpandReuse`), as in Lean's old `ExpandResetReuse` on its IR.

  The test that makes a credit (Lean's `reset`, from `DropSpec` and `Reuse`) is

    let r : ◇n[k; p : V] = if-unique z then (..; ret r') else (..; ret no-reuse n [k; p : V]) in e

  If `e` is small and consumes `r` directly (see below), it is copied into both branches:

    if-unique z then (..; let r : ◆n[k; p : V] = ret r' in e)
    else (..; e[r := empty])

  In the unique branch the credit is full, so `ExpandReuse` tests nothing and code generation
  writes its blocks in place. In the other branch it is empty: `box@r v` becomes `box v`,
  `free r` and `if-full r` disappear, and any other use of `r` becomes `no-reuse n [k; p : V]`.
  The copy gets fresh root names (`cloneE`).

  Lean copied whenever every path of `e` consumes the credit by a `reuse` or a `dec` of it
  (`consumed`), so that a credit that flows into a join point blocks the copy. Since
  `ExpandReuse` already tests the credit once per path, the copy saves about one test on the
  paths that allocate in the credit and nothing on those that free it, while it duplicates all
  of `e`. We therefore copy only if every path of `e` allocates in the credit, so that a path
  that only frees it does not grow (and, for example, lose the inlining of its calls), and only
  if `e` allocates no fresh blocks or closures (`allocatesFresh`), which `ExpandReuse` shares
  across its test but a copy would duplicate. We also copy only if the path to the allocation
  is straight-line (`straightReuse`): copying a test that precedes it, such as the key test of a
  tree descent, can cost more than the credit test it saves, while `ExpandReuse` shares such a
  test and splits only the allocation. As in `Fip`, the paths on which an effect yields
  (`yielding()`) are cold: they need only consume the credit, and may allocate fresh. The limit of `copyLimit`
  nodes only bounds the code size; Lean had none. As in Lean, the resets nested in `e` are
  copied only in the unique branch, so that the code grows at most linearly in their number.
-}
module Backend.Typed.Passes.CopyReset( copyResetProgram ) where

import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Data.Monoid( Sum(..), Any(..), All(..) )
import Control.Monad.State
import Backend.Typed.Syntax
import Common.NamePrim( nameYielding )
import Backend.Typed.Common

type C a = State NameSupply a

-- The largest continuation (in nodes, see `size`) that is copied; our own limit (Lean has none).
-- It only bounds the growth of the code, since `straightReuse` already excludes the descents.
copyLimit :: Int
copyLimit = 80

copyResetProgram :: Program -> Program
copyResetProgram prog
  = prog{ progDefs = [d{ defBody = evalState (crE (defBody d)) (freshFor d) } | d <- progDefs prog] }

crE :: VExpr -> C VExpr
crE expr
  = case expr of
      Let r (VReuse MaybeEmpty n p) (IsUnique z u s) e
        | [Var _] <- rets u, [NoReuse _ _] <- rets s
        , consumed False r e, straightReuse r e, not (allocatesFresh e), size e <= copyLimit, apart u e, apart s e
        -> do e1 <- crE e
              e2 <- cloneE (state (freshPathFrom "cr")) (emptied r (NoReuse n p) e)
              return (IsUnique z (atRet (\v -> Let r (VReuse Full n p) (Ret v) e1) u) (atRet (const e2) s))
      _ -> descendE pure crV (\_ -> crE) expr

-- Copy a straight-line reconstruction, not the control flow leading to it.
-- In particular, copying a tree descent's key test and context composition can
-- cost more than the credit test it saves. ExpandReuse shares that continuation
-- and splits only the allocation when we leave the reset in place.
straightReuse :: Path -> VExpr -> Bool
straightReuse r expr
  | Just (e,_) <- yieldingAlts expr = straightReuse r e
  | isStatement expr = True
  | otherwise = case expr of
      Let _ _ e1 e2 | isStatement e1
        -> any (boxesIn r) (statementValues e1) || straightReuse r e2
      -- `e1` does not mention the credit (`consumed`), so this only checks that it is straight-line
      Let _ _ e1 e2 -> straightReuse r e1 && straightReuse r e2
      _ | [e] <- body expr -> straightReuse r e
      _ -> False

crV :: VVal -> C VVal
crV = descendV crA crV

crA :: AVal -> C AVal
crA val
  = case val of
      Lam ps r e -> Lam ps r <$> crE e
      _ -> descendA pure crA crV val

-- The values returned by a branch of the test: the `ret`s at its end, through forms with one
-- subexpression (but not join points, whose bodies capture their variables).
rets :: VExpr -> [VVal]
rets expr
  = case (expr,body expr) of
      (Ret v,_) -> [v]
      (Let _ _ _ e,_) -> rets e
      (_,[e]) -> rets e
      _ -> []

-- replace the `ret` at the end of a branch
atRet :: (VVal -> VExpr) -> VExpr -> VExpr
atRet f expr
  = case expr of
      Ret v -> f v
      Let x t e1 e -> Let x t e1 (atRet f e)
      _ -> runIdentity (descendE Identity Identity (\_ e -> Identity (atRet f e)) expr)

-- whether the binders of a branch are not used or bound again in the continuation, which
-- moves into their scope
apart :: VExpr -> VExpr -> Bool
apart branch e = S.disjoint (S.fromList (bindersE branch)) (S.union (fvE e) (S.fromList (bindersE e)))

-- the subexpression of a form that only continues with it
body :: VExpr -> [VExpr]
body expr
  = case expr of
      Join{} -> []
      Gen{} -> []
      _ -> getConst (descendE (const (Const [])) (const (Const [])) (\_ e -> Const [e]) expr)

-- Lean's `consumed`: every path consumes the credit directly, by an allocation in it or (if
-- `freeing`) a `free`, and not by passing it on to a join point, function or result. The paths
-- on which an effect yields may always free it.
consumed :: Bool -> Path -> VExpr -> Bool
consumed freeing r expr
  = case expr of
      _ | Just (e,es) <- yieldingAlts expr -> consumed freeing r e && all (consumed True r) es
      Free r' e -> if r' == r then freeing else consumed freeing r e
      Let _ _ e1 e2 | isStatement e1 -> if mentions e1 then direct e1 else consumed freeing r e2
                    | otherwise -> not (mentions e1) && consumed freeing r e2
      Join _ _ e1 e2 -> not (mentions e1) && consumed freeing r e2
      IfFull r' _ _ | r' == r -> False
      _ | isStatement expr -> direct expr
      _ -> getAll (getConst (descendE (const (Const (All True))) (\v -> Const (All (not (S.member r (fvV v)))))
                                     (\_ e -> Const (All (consumed freeing r e))) expr))
  where
    mentions e = S.member r (fvE e)
    direct stmt = let vs = statementValues stmt
                  in any (boxesIn r) vs && not (any (varIn r) vs)

isStatement :: VExpr -> Bool
isStatement e
  = case e of
      Ret _ -> True
      Call{} -> True
      App{} -> True
      Jump{} -> True
      _ -> False

statementValues :: VExpr -> [VVal]
statementValues = getConst . descendE (const (Const [])) (Const . pure) (\_ _ -> Const [])

-- The alternatives of a test of `yielding()`: the first is taken if no effect yields, as in
-- `Fip`, and the others are cold.
yieldingAlts :: VExpr -> Maybe (VExpr,[VExpr])
yieldingAlts expr
  = case expr of
      Let x _ (Call f _ []) (CaseV _ (Var y) ((_,e):alts)) | f == nameYielding && y == x -> Just (e,map snd alts)
      _ -> Nothing

-- whether an expression allocates a fresh block or closure somewhere (and not in a credit),
-- except on the paths on which an effect yields
allocatesFresh :: VExpr -> Bool
allocatesFresh expr
  | Just (e,_) <- yieldingAlts expr = allocatesFresh e
  | otherwise = getAny (getConst (descendE (const (Const (Any False))) (Const . Any . freshV) (\_ e -> Const (Any (allocatesFresh e))) expr))
  where
    freshV = getAny . getConst . descendV (Const . Any . freshA) (Const . Any . freshV)
    freshA a = case a of
                 Box _ -> True
                 Lam{} -> True
                 _ -> getAny (getConst (descendA (const (Const (Any False))) (Const . Any . freshA) (Const . Any . freshV) a))

-- whether a value allocates in the credit
boxesIn :: Path -> VVal -> Bool
boxesIn r = getAny . getConst . descendV (Const . Any . boxesInA) (Const . Any . boxesIn r)
  where
    boxesInA a = case a of
                   BoxAt r' v -> r' == r || boxesIn r v
                   _ -> getAny (getConst (descendA (const (Const (Any False))) (Const . Any . boxesInA) (Const . Any . boxesIn r) a))

-- whether a value uses the credit as a value (and not by allocating in it)
varIn :: Path -> VVal -> Bool
varIn r v = case v of
              Var x -> x == r
              _ -> getAny (getConst (descendV (Const . Any . varInA) (Const . Any . varIn r) v))
  where
    varInA a = getAny (getConst (descendA (const (Const (Any False))) (Const . Any . varInA) (Const . Any . varIn r) a))

-- The continuation where the credit is empty: allocations in it are fresh, and the other uses
-- of it are `none`.
emptied :: Path -> VVal -> VExpr -> VExpr
emptied r none expr
  = case expr of
      Free r' e | r' == r -> emptied r none e
      IfFull r' _ e2 | r' == r -> emptied r none e2
      _ -> runIdentity (descendE Identity (Identity . emptyV) (\_ e -> Identity (emptied r none e)) expr)
  where
    emptyV v = case v of
                 Var x | x == r -> none
                 _ -> mapV emptyA emptyV v
    emptyA a = case a of
                 BoxAt r' v | r' == r -> Box (emptyV v)
                 Lam ps t e -> Lam ps t (emptied r none e)
                 _ -> mapA id emptyA emptyV a

-- the number of expressions and values
size :: VExpr -> Int
size expr = 1 + getSum (getConst (descendE (const (Const 0)) (Const . Sum . sizeV) (\_ e -> Const (Sum (size e))) expr))

sizeV :: VVal -> Int
sizeV v = 1 + getSum (getConst (descendV (Const . Sum . sizeA) (Const . Sum . sizeV) v))

sizeA :: AVal -> Int
sizeA a = case a of
            Lam _ _ e -> 1 + size e
            _ -> 1 + getSum (getConst (descendA (const (Const 0)) (Const . Sum . sizeA) (Const . Sum . sizeV) a))
