-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
-- Type matching for instantiation and coercion during elaboration.
module Backend.Typed.Elab.TypeMatch( TypeMatch(..) ) where

import qualified Data.Map as M
import Control.Monad( foldM )
import Backend.Typed.Syntax
import Backend.Typed.Types( Sub, Types(..), inst, applyA )

class TypeMatch t where
  match   :: [TVar] -> t -> t -> Maybe Sub
  match tvs = matchWith tvs M.empty
  matchWith :: [TVar] -> Sub -> t -> t -> Maybe Sub

instance TypeMatch VType where
  matchWith = matchVWith

instance TypeMatch AType where
  matchWith = matchAWith

instance TypeMatch Ty where
  matchWith tvs sub (A a) (A b) = matchAWith tvs sub a b
  matchWith tvs sub (V a) (V b) = matchVWith tvs sub a b
  matchWith _ _ _ _ = Nothing

matchVWith :: [TVar] -> Sub -> VType -> VType -> Maybe Sub
matchVWith tvs sub pat t
  = case (pat,t) of
      (VPtr p, VPtr s)       -> matchAWith tvs sub p s
      (VSum ps, VSum ts) | length ps == length ts
        -> foldM (\sb (p,s) -> matchVWith tvs sb p s) sub (zip (map snd ps) (map snd ts))
      (VProd ps, VProd ts) | length ps == length ts
        -> foldM (\sb (p,s) -> matchVWith tvs sb p s) sub (zip (map snd ps) (map snd ts))
      (VCtx f p q, VCtx g s u) | f == g -> matchAWith tvs sub p s >>= \sub' -> matchAWith tvs sub' q u
      (VCell n p, VCell m s) | n == m -> matchAWith tvs sub p s
      (VExists as p, VExists bs s) | length as == length bs
        -> matchVWith tvs sub p (inst bs (map AVar as) s)
      _ -> if pat == t then Just sub else Nothing

matchAWith :: [TVar] -> Sub -> AType -> AType -> Maybe Sub
matchAWith tvs sub pat t
  = case pat of
      AVar v | v `elem` tvs -> bind v t
      AApp v ps | v `elem` tvs, Just f <- M.lookup v sub ->
        if alphaEq (applyA f (map (subst sub) ps)) t then Just sub else Nothing
      AApp v ps | v `elem` tvs ->
        case t of
          ACon n ts | length ts >= length ps
            -> let (hs,rest) = splitAt (length ts - length ps) ts
               in bind v (ACon n hs) >>= \sub' -> matchAs sub' ps rest
          AApp w ts | length ts >= length ps
            -> let (hs,rest) = splitAt (length ts - length ps) ts
               in bind v (applyA (AVar w) hs) >>= \sub' -> matchAs sub' ps rest
          _ -> Nothing
      AApp v ps -> case t of
                     AApp w ts | v == w -> matchAs sub ps ts
                     _ -> Nothing
      ACon n ps -> case t of
                     ACon m ts | n == m -> matchAs sub ps ts
                     _ -> Nothing
      ABox p    -> case t of
                     ABox s -> matchVWith tvs sub p s
                     _ -> Nothing
      AScalar p -> case t of
                     AScalar s | p == s -> Just sub
                     _ -> Nothing
      ASum ps   -> case t of
                     ASum ts | map fst ps == map fst ts -> matchAs sub (map snd ps) (map snd ts)
                     _ -> Nothing
      AFun ps r -> case t of
                     AFun qs s | length ps == length qs
                       -> foldM (\sb (p,q) -> matchVWith tvs sb p q) sub (zip (map snd ps ++ [r]) (map snd qs ++ [s]))
                     _ -> Nothing
      AForall as p -> case t of
                        AForall bs s | length as == length bs
                          -> matchAWith tvs sub p (inst bs (map AVar as) s)
                        _ -> Nothing
      ALam as p -> case t of
                     ALam bs s | length as == length bs
                       -> matchAWith tvs sub p (inst bs (map AVar as) s)
                     _ -> Nothing
      ALazy l p -> case t of
                     ALazy k s -> matchAWith tvs sub l k >>= \sub' -> matchAWith tvs sub' p s
                     _ -> Nothing
      AMu x as p ps -> case t of
                         AMu y bs s ts | length as == length bs
                           -> matchAWith tvs sub p (inst (y:bs) (map AVar (x:as)) s) >>= \sub' -> matchAs sub' ps ts
                         _ -> Nothing
      AVar _    -> if pat == t then Just sub else Nothing
      AUnit     -> if pat == t then Just sub else Nothing
  where
    bind v s = case M.lookup v sub of
                 Nothing -> Just (M.insert v s sub)
                 Just s' -> if alphaEq s s' then Just sub else Nothing
    matchAs sb ps ts | length ps == length ts = foldM (\sb' (p,s) -> matchAWith tvs sb' p s) sb (zip ps ts)
                     | otherwise = Nothing
