-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Turn nonescaping local closures called only in tail position into closed
-- join points. Captured unboxed variables become explicit owned parameters.
module Backend.Typed.Passes.Contify( contifyProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Monoid( All(..) )
import Data.Functor.Identity( Identity(..) )
import Common.Name
import Common.NamePrim( nameOpenNone )
import Backend.Typed.Syntax
import Backend.Typed.Passes.Common( defGamma, descendTyped, lamsTyped, NameSupply, freshFor, freshNameFrom, perBody, renameE )
import Backend.Typed.Traversal( bindersE, descendE, fvA, fvE, fvV )
import Backend.Typed.Query( Env, Gamma, envOf, inferVar
                          , M, evalM, liftE, state )

type P a = M () NameSupply a

fresh :: String -> P Name
fresh s = state (freshNameFrom ("cont" ++ s))

contifyProgram :: Program -> (Program,[String])
contifyProgram prog = perBody (\d -> evalM (contifyE (envOf prog) (defGamma d) (defBody d)) () (freshFor d)) prog

contifyE :: Env -> Gamma -> VExpr -> P VExpr
contifyE env g expr
  = case expr of
      Let f _ (Ret (Ptr _ lam@(Lam ps _ body))) rest
        | tailOnly f rest
        , let captures = S.toList (fvA lam)
        , all (`notElem` bindersE rest) (f:captures)
        -> do ts <- mapM (liftE . inferVar g) captures
              case sequence [case t' of V v -> Just v; A _ -> Nothing | t' <- ts] of
                Just vs -> do j <- fresh "join"
                              qs <- mapM (const (root <$> fresh "capture")) captures
                              let sub = M.fromList (zip captures qs)
                                  params = ps ++ zipWith (\q v -> (q,Owned,v)) qs vs
                                  closed = renameE sub body
                              body' <- contifyE env (M.fromList [(x,V v) | (x,_,v) <- params]) closed
                              rest' <- contifyE env g (redirect f j (map Var captures) rest)
                              return (Join NonRec j [] params body' rest')
                Nothing -> descend
      _ -> descend
  where
    descend = descendTyped env g (lamsTyped g (contifyE env)) (contifyE env) expr

-- Elaboration applies a closure by dereferencing it into a boxed operand.
callOf :: Path -> VExpr -> Maybe [VVal]
callOf f (Deref _ (Var x) g (App h vs)) | x == f, g == h = Just vs
callOf f (Call o _ (Var x : vs)) | x == f, o == nameOpenNone (length vs) = Just vs
callOf _ _ = Nothing

-- Ordinary uses, including captures and non-tail calls, prevent contification.
tailOnly :: Path -> VExpr -> Bool
tailOnly f e = occurs e && tails e
  where
    occurs b = f `S.member` fvE b
    tails b
      | Just vs <- callOf f b = all (S.notMember f . fvV) vs
      | otherwise = case b of
          Let x _ e1 e2 -> not (occurs e1) && (x == f || tails e2)
          Gen{} -> not (occurs b)
          Join _ _ _ ps e1 e2 -> (f `elem` [x | (x,_,_) <- ps] || not (occurs e1)) && tails e2
          _ -> getAll (getConst (descendE (Const . All . (/= f)) (Const . All . S.notMember f . fvV)
                             (\xs body -> Const (All (f `elem` xs || tails body))) b))

redirect :: Path -> Name -> [VVal] -> VExpr -> VExpr
redirect f j captures expr
  | Just vs <- callOf f expr = Jump j [] (vs ++ captures)
  | otherwise = runIdentity (descendE Identity Identity
                   (\xs e -> Identity (if f `elem` xs then e else redirect f j captures e)) expr)
