-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

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
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env, Gamma, envOf, bindAll, inferVar, inferV, altTypes )

type P a = M () Int a

fresh :: String -> P Name
fresh s = state (\n -> (newHiddenName ("cont" ++ s ++ show n),n+1))

contifyProgram :: Program -> (Program,[String])
contifyProgram prog
  = let run d = case evalM (contifyE (envOf prog) (gamma d) (defBody d)) () 0 of
                  Right body -> (d{ defBody = body },[])
                  Left err -> (d,[show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs prog))
    in (prog{ progDefs = defs },concat errs)
  where
    gamma DefFun{ defArgs = ps } = M.fromList [(x,V t) | (x,_,t) <- ps]
    gamma DefVal{} = M.empty

contifyE :: Env -> Gamma -> VExpr -> P VExpr
contifyE env g expr
  = case expr of
      Let f t (Ret (Ptr a lam@(Lam ps _ body))) rest
        | tailOnly f rest
        , let captures = S.toList (fvA lam)
        , all (`notElem` bindersE rest) (f:captures)
        -> do ts <- mapM (liftE . inferVar g) captures
              case sequence [case t' of V v -> Just v; A _ -> Nothing | t' <- ts] of
                Just vs -> do j <- fresh "join"
                              qs <- mapM (const (fresh "capture")) captures
                              let sub = M.fromList (zip captures qs)
                                  params = ps ++ zipWith (\q v -> (q,Owned,v)) qs vs
                                  closed = renameE sub body
                              body' <- contifyE env (M.fromList [(x,V v) | (x,_,v) <- params]) closed
                              rest' <- contifyE env g (redirect f j (map Var captures) rest)
                              return (Join j params body' rest')
                Nothing -> Let f t <$> contifyE env g (Ret (Ptr a lam)) <*> contifyE env (M.insert f (V t) g) rest
      Let x t e1 e2 -> Let x t <$> contifyE env g e1 <*> contifyE env (M.insert x (V t) g) e2
      Join j ps e1 e2 -> Join j ps <$> contifyE env (M.fromList [(x,V t) | (x,_,t) <- ps]) e1 <*> contifyE env g e2
      _ | Just ds <- destructAOf expr
        -> do t <- liftE (inferVar g (dsScrut ds))
              destruct t (dsAlts ds) (dsBuild ds (dsMode ds) (dsScrut ds))
        | Just ds <- destructVOf expr
        -> do v <- contifyV env g (dsScrut ds)
              t <- liftE (inferV env g v)
              destruct (V t) (dsAlts ds) (dsBuild ds (dsMode ds) v)
      _ -> descend
  where
    descend = descendE pure (contifyV env g) (\_ -> contifyE env g) expr
    destruct t alts build
      = do tss <- liftE (altTypes env t expr)
           es <- sequence [contifyE env (bindAll (zip xs ts) g) e | ((xs,e),ts) <- zip alts tss]
           return (build es)

contifyV :: Env -> Gamma -> VVal -> P VVal
contifyV env g = descendV (contifyA env g) (contifyV env g)

contifyA :: Env -> Gamma -> AVal -> P AVal
contifyA env g (Lam ps r e) = Lam ps r <$> contifyE env (bindAll [(x,V t) | (x,_,t) <- ps] g) e
contifyA env g a = descendA pure (contifyA env g) (contifyV env g) a

-- Elaboration applies a closure by dereferencing it into a boxed operand.
callOf :: Name -> VExpr -> Maybe [VVal]
callOf f (Deref _ (Var x) g (App h vs)) | x == f, g == h = Just vs
callOf f (Call o _ (Var x : vs)) | x == f, o == nameOpenNone (length vs) = Just vs
callOf _ _ = Nothing

-- Ordinary uses, including captures and non-tail calls, prevent contification.
tailOnly :: Name -> VExpr -> Bool
tailOnly f e = occurs e && tails e
  where
    occurs b = f `S.member` fvE b
    tails b
      | Just vs <- callOf f b = all (S.notMember f . fvV) vs
      | otherwise = case b of
          Let x _ e1 e2 -> not (occurs e1) && (x == f || tails e2)
          Gen{} -> not (occurs b)
          Join _ ps e1 e2 -> (f `elem` [x | (x,_,_) <- ps] || not (occurs e1)) && tails e2
          _ -> getAll (getConst (descendE (Const . All . (/= f)) (Const . All . S.notMember f . fvV)
                             (\xs body -> Const (All (f `elem` xs || tails body))) b))

redirect :: Name -> Name -> [VVal] -> VExpr -> VExpr
redirect f j captures expr
  | Just vs <- callOf f expr = Jump j (vs ++ captures)
  | otherwise = runIdentity (descendE Identity Identity
                   (\xs e -> Identity (if f `elem` xs then e else redirect f j captures e)) expr)
