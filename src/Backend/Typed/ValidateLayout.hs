-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
-- Licensed under the Apache License, Version 2.0.
-----------------------------------------------------------------------------

-- Validate the representation boundary independently of product normalization.
module Backend.Typed.ValidateLayout( checkLayoutProgram, programTypes ) where

import qualified Data.Map as M
import Data.Functor.Const( Const(..) )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Layout
import Backend.Typed.Product( productOrder )

checkLayoutProgram :: Program -> [String]
checkLayoutProgram p = concatMap check (programTypes p)
  where
    check t = normal t ++ checkLayout (layout t)
    normal t = case t of
      VProd a b -> ["product is not in layout normal form" | compound a || empty b || ordered /= [0..length fs-1]]
                   ++ normal a ++ normal b
        where fs = leaves t
              ordered = productOrder fs
      VExists _ b -> ["nested existential in layout normal form" | exists b] ++ normal b
      VPtr a -> atomic a
      VSum ts -> concatMap normal ts
      VCtx _ a b -> atomic a ++ atomic b
      VReuse _ _ d -> maybe [] (\(Contents _ _ s) -> normal s) d
      _ -> []
    compound VProd{} = True
    compound VExists{} = True
    compound VUnit = True
    compound _ = False
    empty VUnit = True
    empty VExists{} = True
    empty _ = False
    exists VExists{} = True
    exists _ = False
    atomic a = case a of
      ABox t -> check t
      AScalar t -> check t
      ASum ts -> concatMap (atomic . snd) ts
      AFun ps r -> concatMap check (r : map snd ps)
      AForall _ b -> atomic b
      ALam _ b -> atomic b
      ACon _ ts -> concatMap atomic ts
      AApp _ ts -> concatMap atomic ts
      _ -> []

programTypes :: Program -> [VType]
programTypes prog = concatMap sig (M.elems (progSigs prog)) ++ concatMap def (progDefs prog)
                    ++ concatMap (\d -> vars (tdefParams d) ++ maybe [] at (tdefBody d)) (M.elems (progTypes prog))
  where
    vars = map (VPtr . AVar)
    sig s = case s of
      SigFun vs ps r -> vars vs ++ (r : map snd ps)
      SigVal vs t -> vars vs ++ [t]
      SigCon vs ts _ -> vars vs ++ ts
    def d = case d of
      DefFun _ vs ps r e -> vars vs ++ (r : map (\(_,_,t) -> t) ps ++ et e)
      DefVal _ vs t e -> vars vs ++ (t : et e)
    at a = case a of
      ABox t -> [t]
      AScalar t -> [t]
      ASum ts -> concatMap (at . snd) ts
      AFun ps r -> r : map snd ps
      AForall _ b -> at b
      ALam _ b -> at b
      ACon _ ts -> concatMap at ts
      AApp _ ts -> concatMap at ts
      _ -> []
    et e = here ++ getConst (descendE (const (Const [])) (Const . vt) (\_ b -> Const (et b)) e)
      where here = case e of
                     Let _ t _ _ -> [t]
                     LetYield _ t _ _ _ -> [t]
                     Yielded t -> [t]
                     Join _ ps _ _ -> map (\(_,_,t) -> t) ps
                     Call _ ts _ -> concatMap at ts
                     Gen vs _ -> map (VPtr . AVar) vs
                     Unpack _ _ vs _ _ -> map (VPtr . AVar) vs
                     _ -> []
    vt v = here ++ getConst (descendV (Const . avTypes) (Const . vt) v)
      where here = case v of
                     Glob _ ts -> concatMap at ts
                     TyApp _ ts -> concatMap at ts
                     Context a _ -> at a
                     Ptr a _ -> at a
                     Inj _ t _ -> [t]
                     Pack t ts _ -> t : concatMap at ts
                     NoReuse _ p -> maybe [] (\(Contents _ _ t) -> [t]) p
                     _ -> []
    avTypes a = case a of
      Lam ps r e -> r : map (\(_,_,t) -> t) ps ++ et e
      Roll t w -> at t ++ avTypes w
      InjA _ t w -> at t ++ avTypes w
      OpenCon _ ts ws -> concatMap at ts ++ concatMap vt ws
      _ -> getConst (descendA (const (Const [])) (Const . avTypes) (Const . vt) a)
