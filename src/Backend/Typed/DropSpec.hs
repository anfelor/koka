-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Drop specialization (after reuse).

  Perceus destructures a box that is still needed by borrowing its contents,
  duplicating them and then dropping the box:

    let^ box p = z in let y = dup p in drop z; e

  If the box is unique, the dup and the drop cancel out: its contents are taken
  without reference counting and its block is freed (or kept as a reuse credit):

    let y = if-unique z then let box p @ r = z in drop r; ret p
                         else let^ box p = z in let y' = dup p in drop z; ret y'
    in e

  The shared branch is the original code. With a drop-reuse both branches return
  the contents together with the credit (null in the shared branch).
  TODO: the shared branch could decrement the reference count without testing it,
  but only as long as no other reference to the block is dropped first.
-}
module Backend.Typed.DropSpec( dropSpecProgram ) where

import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Monad
import Backend.Typed.Check( reuseSize )

type D a = State Int a

fresh :: String -> D Name
fresh s = state (\n -> (newHiddenName ("ds" ++ s ++ show n), n+1))

dropSpecProgram :: Program -> Program
dropSpecProgram prog
  = prog{ progDefs = [d{ defBody = evalState (dsE (defBody d)) 0 } | d <- progDefs prog] }

dsE :: Expr -> D Expr
dsE (Unbox Borrowed (Var z) p (Let y t@(V s) (Ret (Dup (Var p'))) rest))
  | p == p', Right n <- reuseSize s, Just (mr,e) <- dropOf z rest
  = do y' <- fresh "y"
       r' <- fresh "r"
       e' <- dsE e
       let shared k = Unbox Borrowed (Var z) p (Let y' t (Ret (Dup (Var p))) k)
       case mr of
         Nothing -> return (Let y t (IsUnique z (UnboxRu (Var z) p r' (Drop r' (Ret (Var p))))
                                                (shared (Drop z (Ret (Var y')))))
                              e')
         Just r  -> do q <- fresh "q"
                       return (Let q (V (VProd s (VReuse n)))
                                 (IsUnique z (UnboxRu (Var z) p r' (Ret (Pair (Var p) (Var r'))))
                                             (shared (DropRu z r' (Ret (Pair (Var y') (Var r'))))))
                                 (Unpair Owned (Var q) y r e'))
dsE expr = descendE dsV (\_ e -> dsE e) expr

dropOf :: Name -> Expr -> Maybe (Maybe Name, Expr)
dropOf z expr
  = case expr of
      Drop x e     | x == z -> Just (Nothing, e)
      DropRu x r e | x == z -> Just (Just r, e)
      _ -> Nothing

dsV :: Val -> D Val
dsV (Lam ps r e) = Lam ps r <$> dsE e
dsV v = descendV dsV v
