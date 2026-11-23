------------------------------------------------------------------------------
-- Copyright 2026, Anton Lorenzen
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-|
The declarations of a dump in lidar's terms: the IR type of each mono type, the datatypes of the
inductive types, and the signatures of the module's declarations and of the constants they use.

Mono types become IR types as follows.

* @lcAny@, @lcErased@, type variables and function types are @any*@. Mono types give no reliable
  arity for closures, so a closure is an @any*@ that is cast to a function type where it is
  applied (as @lean_apply_n@ checks the arity at run time).
* @lcVoid@, the state of @IO@, is @𝟙@.
* @Nat@ and @String@ are the builtin types @int*@ and @string*@ of literals. The unsigned
  scalars, @USize@ and the floats are raw types; until lidar has unsigned raw types, they are
  the signed raw types of the same size. The other types that Lean's runtime implements itself
  (@Int@, @Array@, ...) are abstract.
* A trivial structure is its relevant field, as in Lean's IR. As the C code follows Lean's impure
  types, these are the trivial structures of the impure level, where @lcVoid@ fields are
  irrelevant too (so @ST.Out@, a value and the state, is its value).
* An enumeration (an inductive type whose values are scalars and whose constructors have no
  fields) is a value sum of units, @uint8@ to @uint32@ as in Lean.
* Any other inductive type @T@ is a reference datatype @T*@, without parameters: mono types
  replace the parameters of fields by @lcAny@, so the arguments of @T@ never matter. Its body
  is the sum of its constructors by index (Lean's @cidx@), each a box of its fields without the
  erased ones (or @1@ without fields).
-}
module Lidar.Lean.Decls
  ( Decls(..), Kind(..), CtorInfo(..)
  , declsOf, leanName, irType, typeKind, anyT, resultType, rawOfNat, isBuiltinType
  ) where

import qualified Data.Map as M
import Data.List( sortOn )
import Data.Maybe( mapMaybe )
import Lidar
import Lidar.Types( prodFields, vtInt, vtString )
import Lidar.Elab.Representation( sumOf )
import qualified Lidar.Lean.Dump as D

data Decls = Decls
  { dTypes      :: TypeDefs
  , dSigs       :: Sigs
  , dInductives :: M.Map D.Name D.Inductive
  , dCtors      :: M.Map D.Name CtorInfo
  }

-- | A constructor: its type, its index, its number of parameters, and for each of its fields
-- the IR type, if the field is stored.
data CtorInfo = CtorInfo
  { ciType      :: D.Name
  , ciIndex     :: Int
  , ciNumParams :: Int
  , ciFields    :: [Maybe VType]
  }

-- | What a named mono type is in the IR.
data Kind = KRaw Raw              -- ^ a scalar
          | KPrim VType           -- ^ @int*@ or @string*@
          | KAbstract             -- ^ a type without constructors that the IR knows
          | KTrivial D.Type       -- ^ a trivial structure: the type of its relevant field
          | KEnum [D.Name]        -- ^ an enumeration, by its constructors
          | KRef                  -- ^ a reference datatype

-- | Lean's names are lidar names with the whole Lean name as stem, so that they keep their
-- (case-sensitive) spelling; C names come from the dump.
leanName :: D.Name -> Name
leanName = newName

anyT :: VType
anyT = VPtr AAny

-- the scalars of Lean's runtime, by the name of their type
rawTypes :: [(D.Name,Raw)]
rawTypes = [ ("UInt8",RUInt8), ("UInt16",RInt16), ("UInt32",RInt32), ("UInt64",RInt64)
           , ("USize",RSSize), ("Float",RFloat64), ("Float32",RFloat32) ]

-- the types that Lean's runtime implements itself (`isRuntimeBultinType`), apart from scalars
builtinTypes :: [(D.Name,Kind)]
builtinTypes = [ ("Nat",KPrim vtInt), ("String",KPrim vtString) ]
               ++ [ (n,KAbstract) | n <- ["Int","Array","ByteArray","FloatArray","Thunk","Task"] ]

-- | Whether the runtime implements the type itself: its constructors (such as @Int.ofNat@) are
-- functions of the runtime, not constructor values.
isBuiltinType :: D.Name -> Bool
isBuiltinType n = n `elem` map fst rawTypes || n `elem` map fst builtinTypes

-- the constructors of builtin types that mono code applies, as functions of the runtime
-- (@lean_nat_to_int@ and @lean_int_neg_succ_of_nat@ consume their argument)
builtinCtorSigs :: [(D.Name,Sig)]
builtinCtorSigs = [ (c, SigFun [] [(Owned,vtInt)] Owned (VPtr (ACon (leanName "Int") [])))
                  | c <- ["Int.ofNat","Int.negSucc"] ]

-- the unsigned integer types, whose literals are converted from Nat
uintTypes :: [(D.Name,Raw)]
uintTypes = take 5 rawTypes

-- | The function that converts a Nat to an unsigned integer (an extern of Lean's runtime,
-- such as @UInt32.ofNat@), for the literals of that type, as the IR has no literals of raw
-- integer types.
rawOfNat :: Raw -> Maybe D.Name
rawOfNat r = case [n | (n,r') <- uintTypes, r' == r] of
               n:_ -> Just (n ++ ".ofNat")
               [] -> Nothing

typeKind :: M.Map D.Name D.Inductive -> D.Name -> Kind
typeKind inds n
  | Just r <- lookup n rawTypes = KRaw r
  | Just k <- lookup n builtinTypes = k
  | otherwise
  = case M.lookup n inds of
      Nothing -> KAbstract
      Just ind
        | Just (c,_,f) <- D.indTrivial ind, Just ctor <- lookupCtor c ind
          -> KTrivial (maybe (D.TConst "lcAny") id (ctorFieldType ctor (fromInteger f)))
        | Just (D.TConst s) <- D.indImpure ind, Just r <- lookup s rawTypes
          -> if s `elem` ["UInt8","UInt16","UInt32"] && not (null (D.indCtors ind)) && all ((== 0) . D.ctorNumFields) (D.indCtors ind)
               then KEnum (map D.ctorName (sortOn D.ctorIndex (D.indCtors ind)))
               else KRaw r
        | null (D.indCtors ind) -> KAbstract
        | otherwise -> KRef
  where
    lookupCtor c ind = case [ct | ct <- D.indCtors ind, D.ctorName ct == c] of
                         ct:_ -> Just ct
                         [] -> Nothing

-- | The IR type of a mono type.
irType :: M.Map D.Name D.Inductive -> D.Type -> VType
irType inds t
  = case t of
      D.TConst "lcVoid" -> VUnit
      D.TConst n | n `elem` ["lcAny","lcErased"] -> anyT
      D.TConst n -> named n
      D.TApp (D.TConst n) _ -> named n
      _ -> anyT
  where
    named n = case typeKind inds n of
                KRaw r -> VRaw r
                KPrim v -> v
                KAbstract -> VPtr (ACon (leanName n) [])
                KTrivial f -> irType inds f
                KEnum cs -> VSum [(Con (leanName c), VUnit) | c <- cs]
                KRef -> VPtr (ACon (leanName n) [])

-- | The type of field i of a constructor, from its mono type.
ctorFieldType :: D.Ctor -> Int -> Maybe D.Type
ctorFieldType c i
  = case D.ctorType c of
      Just t | (_:_) <- drop (fromInteger (D.ctorNumParams c) + i) (args t) -> Just (args t !! (fromInteger (D.ctorNumParams c) + i))
      _ -> Nothing
  where
    args (D.TArrow a b) = a : args b
    args _ = []

-- | The result type of a function with n parameters of mono type t.
resultType :: Int -> D.Type -> D.Type
resultType 0 t = t
resultType n (D.TArrow _ b) = resultType (n-1) b
resultType _ _ = D.TConst "lcAny"

ctorInfo :: M.Map D.Name D.Inductive -> D.Inductive -> D.Ctor -> CtorInfo
ctorInfo inds ind c
  = CtorInfo (D.indName ind) (fromInteger (D.ctorIndex c)) (fromInteger (D.ctorNumParams c))
             [field i | i <- [0 .. fromInteger (D.ctorNumFields c) - 1]]
  where
    layout = maybe [] D.layoutFields (D.ctorLayout c)
    field i = case (drop i layout, ctorFieldType c i) of
                (D.FErased : _, _) -> Nothing
                (D.FVoid : _, _) -> Nothing
                (_, Just ft) | erased ft -> Nothing
                (_, ft) -> Just (maybe anyT (irType inds) ft)
    erased ft = case ft of
                  D.TConst n -> n `elem` ["lcErased","lcVoid"]
                  D.TSort -> True
                  _ -> False

-- | The datatype of a reference type.
typeDef :: M.Map D.Name CtorInfo -> D.Inductive -> TypeDef
typeDef ctors ind
  = TypeDef (leanName (D.indName ind)) [] (BodyRef (sumOf (map shape cs))) (map label cs)
  where
    cs = [(D.ctorName c, stored (ctors M.! D.ctorName c)) | c <- sortOn D.ctorIndex (D.indCtors ind)]
    stored ci = zip (map posField [0..]) (mapMaybe id (ciFields ci))
    shape (_,[]) = AUnit
    shape (_,fs) = ABox (prodFields fs)
    label (c,fs) = ConLabel (leanName c) (map fst fs) (map (const Nothing) fs)

-- | The datatype of an enumeration.
enumDef :: D.Name -> [D.Name] -> TypeDef
enumDef n cs
  = TypeDef (leanName n) [] (BodyValue (VSum [(Con (leanName c), VUnit) | c <- cs])) [ConLabel (leanName c) [] [] | c <- cs]

-- | The signature of a function or value with the given parameters and mono type. The modes
-- are the borrow flags of its impure signature, which Lean's callers rely on, if it has one.
signature :: M.Map D.Name D.Inductive -> D.Link -> [D.Param] -> D.Type -> Sig
signature inds link ps t
  | null ps = SigVal [] (irType inds t)
  | otherwise = SigFun [] [(mode b, irType inds (D.paramType p)) | (p,b) <- zip ps borrows] Owned
                       (irType inds (resultType (length ps) t))
  where
    borrows = case D.linkImpure link of
                Just (ips,_) | length ips == length ps -> map D.paramBorrow ips
                _ -> map D.paramBorrow ps
    mode b = if b then Borrowed else Owned

declsOf :: D.Dump -> Decls
declsOf d
  = Decls types sigs inds ctors
  where
    inds = M.fromList [(D.indName i, i) | i <- D.dumpInductives d]
    ctors = M.fromList [(D.ctorName c, ctorInfo inds i c) | i <- D.dumpInductives d, c <- D.indCtors i]
    types = M.fromList [(tdefName td, td) | i <- D.dumpInductives d, Just td <- [def i]]
    def i = case typeKind inds (D.indName i) of
              KRef -> Just (typeDef ctors i)
              KEnum cs -> Just (enumDef (D.indName i) cs)
              _ -> Nothing
    sigs = M.fromList ([(leanName (D.declName x), signature inds (D.declLink x) (D.declParams x) (D.declType x)) | x <- D.dumpDecls d]
                       ++ [(leanName (D.constName c), signature inds (D.constLink c) ps t) | c <- D.dumpConsts d, Just (D.MonoSig ps t) <- [D.constMono c]])
           `M.union` M.fromList [(leanName (n ++ ".ofNat"), SigFun [] [(Borrowed,vtInt)] Owned (VRaw r)) | (n,r) <- uintTypes]
           `M.union` M.fromList [(leanName c, sig) | (c,sig) <- builtinCtorSigs]
