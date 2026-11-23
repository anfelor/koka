------------------------------------------------------------------------------
-- Copyright 2026, Anton Lorenzen
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-|
The representation of lidar's types in Lean's runtime (@lean.h@).

Every pointer @A*@ is a @lean_object*@: a constructor object, a unit alternative or a scalar
boxed by @lean_box@, a closure, or one of the runtime's own objects (@Nat@, @String@, arrays).
An unboxed value is a list of /leaves/ (@Lidar.Layout.leaves@), each held in a C local: a
product has one per leaf, @𝟙@ and the effect token have none. A credit is the block it holds,
or @NULL@ if it is empty.

Lean's scalars are unsigned. Until lidar has unsigned raw types, its signed raw types stand for
the unsigned types of the same size (see "Lidar.Lean.Decls"), so @int32@ is @uint32_t@. An
enumeration is a scalar of the size Lean gives it.

A box @Box V@ with tag i is a constructor object with tag i (Lean's @cidx@), whose fields are the
leaves of V in Lean's order (@getCtorLayout@ in Lean's @ToImpureType.lean@): the objects, then
the @usize@ fields, then the other scalars by decreasing size, each group in the order of V.
-}
module Lidar.Lean.CGen.Layout
  ( Leaf(..), leafOf, cType
  , Slot, Payload(..), payload, allocCtor, readSlot, writeSlot
  , boxScalar, unboxScalar
  ) where

import qualified Data.Map as M
import Lidar.Syntax
import Lidar.Layout( isEnum )

-- | The representation of a leaf.
data Leaf = LObj          -- ^ a @lean_object*@
          | LCredit       -- ^ a block, or @NULL@
          | LScalar Raw   -- ^ an unsigned scalar or a float
          deriving (Eq, Show)

-- | The representation of a leaf type (an element of @Lidar.Layout.leaves@).
leafOf :: VType -> Either String Leaf
leafOf t
  = case t of
      VPtr _ -> Right LObj
      VCell _ _ -> Right LObj
      VRaw r -> Right (LScalar r)
      VReuse{} -> Right LCredit
      VSum ts | isEnum t -> Right (LScalar (enumRaw (length ts)))
      _ -> Left ("no representation in Lean's runtime for a leaf of type " ++ show t)

-- the scalar of an enumeration with n constructors, as Lean's `toImpureType`
enumRaw :: Int -> Raw
enumRaw n
  | n < 256   = RUInt8
  | n < 65536 = RInt16
  | otherwise = RInt32

cType :: Leaf -> String
cType l
  = case l of
      LObj -> "lean_object*"
      LCredit -> "lean_object*"
      LScalar r -> case r of
                     RUInt8   -> "uint8_t"
                     RInt8    -> "uint8_t"
                     RInt16   -> "uint16_t"
                     RInt32   -> "uint32_t"
                     RChar    -> "uint32_t"
                     RInt64   -> "uint64_t"
                     RSSize   -> "size_t"
                     RIntPtr  -> "size_t"
                     RFloat64 -> "double"
                     RFloat32 -> "float"

-- the size of a scalar field of a constructor, or Nothing for a `usize` field
scalarSize :: Raw -> Maybe Int
scalarSize r
  = case r of
      RUInt8   -> Just 1
      RInt8    -> Just 1
      RInt16   -> Just 2
      RInt32   -> Just 4
      RChar    -> Just 4
      RFloat32 -> Just 4
      RInt64   -> Just 8
      RFloat64 -> Just 8
      RSSize   -> Nothing
      RIntPtr  -> Nothing

-- the suffix of the accessors of a scalar field (`lean_ctor_get_uint32`)
accessor :: Raw -> String
accessor r
  = case r of
      RUInt8   -> "uint8"
      RInt8    -> "uint8"
      RInt16   -> "uint16"
      RInt32   -> "uint32"
      RChar    -> "uint32"
      RInt64   -> "uint64"
      RFloat64 -> "float"
      RFloat32 -> "float32"
      RSSize   -> "usize"
      RIntPtr  -> "usize"

-- | Where a leaf of a payload is: an object field, a @usize@ field (by index among them), or a
-- scalar field at a byte offset after the objects and @usize@ fields.
data Slot = SObj Int | SUSize Int | SScalar Raw Int

-- | The layout of the payload of a constructor object: the numbers of object and @usize@
-- fields, the size of the other scalars, and the slot of each leaf.
data Payload = Payload{ plObjs :: Int, plUSize :: Int, plScalars :: Int, plSlots :: [Slot] }

payload :: [Leaf] -> Either String Payload
payload ls
  | LCredit `elem` ls = Left "a credit in a constructor object"
  | otherwise = Right (Payload (length objs) (length usizes) (sum (map snd scalars)) (map (slots M.!) (map fst indexed)))
  where
    indexed = zip [0 :: Int ..] ls
    objs = [i | (i,LObj) <- indexed]
    usizes = [i | (i,LScalar r) <- indexed, scalarSize r == Nothing]
    -- by decreasing size, each size in leaf order
    scalars = [(i,n) | n <- [8,4,2,1], (i,LScalar r) <- indexed, scalarSize r == Just n]
    scalarRaw i = case ls !! i of { LScalar r -> r; _ -> RUInt8 }
    slots = M.fromList (zip objs (map SObj [0..]) ++ zip usizes (map SUSize [0..])
                        ++ [(i,SScalar (scalarRaw i) off) | ((i,_),off) <- zip scalars (scanl (+) 0 (map snd scalars))])

-- | A fresh constructor object with the given tag for the payload.
allocCtor :: Int -> Payload -> String
allocCtor tag pl = "lean_alloc_ctor(" ++ show tag ++ ", " ++ show (plObjs pl) ++ ", " ++ scalarArea pl ++ ")"
  where scalarArea p = "sizeof(size_t)*" ++ show (plUSize p) ++ " + " ++ show (plScalars p)

-- the byte offset of a scalar field, as Lean's `lean_ctor_get_uint8` takes it
scalarOffset :: Payload -> Int -> String
scalarOffset pl off = "sizeof(void*)*" ++ show (plObjs pl + plUSize pl) ++ " + " ++ show off

-- | The value of a slot of the constructor object @o@.
readSlot :: Payload -> String -> Slot -> String
readSlot pl o s
  = case s of
      SObj i -> "lean_ctor_get(" ++ o ++ ", " ++ show i ++ ")"
      SUSize i -> "lean_ctor_get_usize(" ++ o ++ ", " ++ show (plObjs pl + i) ++ ")"
      SScalar r off -> "lean_ctor_get_" ++ accessor r ++ "(" ++ o ++ ", " ++ scalarOffset pl off ++ ")"

-- | The statement that writes @v@ into a slot of the constructor object @o@.
writeSlot :: Payload -> String -> Slot -> String -> String
writeSlot pl o s v
  = case s of
      SObj i -> "lean_ctor_set(" ++ o ++ ", " ++ show i ++ ", " ++ v ++ ");"
      SUSize i -> "lean_ctor_set_usize(" ++ o ++ ", " ++ show (plObjs pl + i) ++ ", " ++ v ++ ");"
      SScalar r off -> "lean_ctor_set_" ++ accessor r ++ "(" ++ o ++ ", " ++ scalarOffset pl off ++ ", " ++ v ++ ");"

-- | Lean's box of a scalar (@Scalar raw@): immediate for small integers, an object otherwise.
boxScalar :: Raw -> String -> String
boxScalar r e = "lean_box" ++ boxSuffix r ++ "(" ++ e ++ ")"

-- | The scalar in a box; the box is not consumed.
unboxScalar :: Raw -> String -> String
unboxScalar r e = "lean_unbox" ++ boxSuffix r ++ "(" ++ e ++ ")"

boxSuffix :: Raw -> String
boxSuffix r
  = case scalarSize r of
      Just n | n <= 2 -> ""
      _ -> "_" ++ accessor r
