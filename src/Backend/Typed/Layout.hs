-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- The C representation of unboxed types.

  - pointer-sized types are `kk_box_t`; raw types are their C type; unit is `kk_unit_t`;
  - an unboxed product is a struct whose leaves are ordered as in Koka: fields with
    pointers first, then raw fields by decreasing alignment;
  - an unboxed sum is a struct with a `kk_value_tag_t` and a union of its alternatives
    (or the smallest unsigned integer that holds its tag if all alternatives are unit);
  - a box is a heap block with the payload after the header.
  Structs are named by a hash of their layout so modules agree on them.
-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Layout( CT(..), PrimType(..), EnumSize(..), layout, leaves, leafSlots, isEnum, orderFields, shapeIsHeap
                           , ctName, scanOf, rawOf, needsRC
                           , structDefs, blockName, blockDef, blockSize, isBlock, isScalar
                           , dupExpr, dropStmt, dupFun, dropFun, rawCType, primBox, scalarHeapSize, fnv
                           ) where

import Data.Char( ord )
import Data.Bits( xor )
import Data.Word( Word64 )
import Data.List( intercalate, foldl', sortOn )
import Data.Maybe( isJust )
import Data.Ord( Down(..) )
import qualified Numeric
import Common.Name
import Common.NamePrim
import Backend.Typed.Syntax

data CT = CBox
        | CPrim PrimType
        | CUnit
        | CEnum EnumSize              -- the width of the tag
        | CProd String [(Int,CT)]     -- leaves in memory order, with their position in the product
        | CSum String [Maybe CT]      -- the payload of each alternative (if not unit)
        | CReuse                      -- a reuse credit
        deriving (Eq,Show)

data PrimType = PrimChar | PrimSSize | PrimIntPtr | PrimDouble | PrimInt64
              | PrimUInt8 | PrimInt8 | PrimInt16 | PrimInt32 | PrimFloat
              | PrimFieldAddr | PrimBox
              deriving (Eq,Show)

data EnumSize = Enum8 | Enum16 | Enum32
              deriving (Eq,Show)

enumBytes :: EnumSize -> Int
enumBytes size
  = case size of
      Enum8  -> 1
      Enum16 -> 2
      Enum32 -> 4

-- A uniform boxed shape can be distinguished by the pointer bit. Nothing means
-- either a mixture of heap blocks and immediates or an opaque representation.
shapeIsHeap :: AType -> Maybe Bool
shapeIsHeap AUnit = Just False
shapeIsHeap (ABox t) = Just (case layout t of { CUnit -> False; _ -> True })
shapeIsHeap (ASum ((_,t):ts))
  = do b <- shapeIsHeap t
       bs <- mapM (shapeIsHeap . snd) ts
       if all (== b) bs then Just b else Nothing
shapeIsHeap _ = Nothing

layout :: VType -> CT
layout t
  = case t of
      VRaw n      -> CPrim (rawCType n)
      VExists _ b -> layout b
      VReuse _ _ _  -> CReuse
      VSum ts | isEnum t -> CEnum (enumSize (length ts))
      VSum ts     -> let alts = map altLayout ts
                     in CSum (structName ("S[" ++ intercalate "|" (map (maybe "U" canonCT) alts) ++ "]")) alts
      VProd _ _   -> case map layout (leaves t) of
                       [ct] -> ct
                       cts  -> CProd (structName ("P(" ++ intercalate "," [show i ++ ":" ++ canonCT ct | (i,ct) <- zip [0::Int ..] cts] ++ ")"))
                                     (orderFields (zip [0..] cts))
      VUnit       -> CUnit
      VPtr _      -> CBox
      -- Koka's `cctx`: `res` and the address of the hole, which is boxed as a value
      -- (`kk_field_addr_t`), so duplicating and dropping it does nothing
      VCtx _ a b  -> layout (VProd (VPtr a) (VPtr b))
  where
    altLayout s = case layout s of
                    CUnit -> Nothing
                    ct    -> Just ct

-- leaves of a product
leaves :: VType -> [VType]
leaves t
  = case t of
      VProd a b -> leaves a ++ leaves b
      VExists _ b -> leaves b
      VUnit -> []
      VPtr _ -> [t]
      VSum _ -> [t]
      VRaw _ -> [t]
      VReuse _ _ _ -> [t]
      VCtx _ a b -> [VPtr a, VPtr b]

enumSize :: Int -> EnumSize
enumSize n
  | n <= 256   = Enum8
  | n <= 65536 = Enum16
  | otherwise  = Enum32

isEnum :: VType -> Bool
isEnum t
  = case t of
      VSum ts -> length ts > 1 && all isUnitT ts
      _ -> False
  where
    isUnitT VUnit = True
    isUnitT (VExists _ b) = isUnitT b
    isUnitT _ = False

-- scanned fields first (pointers before mixed ones), then raw fields by decreasing alignment
-- (so that small fields share a word, as in Koka); units take no space
orderFields :: [(Int,CT)] -> [(Int,CT)]
orderFields fs
  = [f | f@(_,ct) <- fs, scanOf ct > 0, not (rawOf ct)] ++
    [f | f@(_,ct) <- fs, scanOf ct > 0, rawOf ct] ++
    sortOn (Down . snd . sizeAlign . snd) [f | f@(_,ct) <- fs, scanOf ct == 0, notUnit ct]
  where
    notUnit CUnit = False
    notUnit _ = True

ctName :: CT -> String
ctName ct
  = case ct of
      CBox -> "kk_box_t"
      CPrim p -> primName p
      CUnit -> "kk_unit_t"
      CEnum Enum8  -> "uint8_t"
      CEnum Enum16 -> "uint16_t"
      CEnum Enum32 -> "uint32_t"
      CProd n _ -> n
      CSum n _ -> n
      CReuse -> "kk_reuse_t"

canonCT :: CT -> String
canonCT ct
  = case ct of
      CBox -> "B"
      CUnit -> "U"
      CEnum size -> "E" ++ show (enumBytes size)
      CPrim _ -> ctName ct
      CProd _ _ -> ctName ct
      CSum _ _ -> ctName ct
      CReuse -> ctName ct

scanOf :: CT -> Int
scanOf ct
  = case ct of
      CBox -> 1
      CProd _ fs -> sum (map (scanOf . snd) fs)
      CSum _ alts -> 1 + maximum (0 : map (maybe 0 scanOf) alts)
      CPrim _ -> 0
      CUnit -> 0
      CEnum _ -> 0
      CReuse -> 0

rawOf :: CT -> Bool
rawOf ct
  = case ct of
      CBox -> False
      CUnit -> False
      CProd _ fs -> any (rawOf . snd) fs
      CSum _ alts -> any (maybe False rawOf) alts
      CPrim _ -> True
      CEnum _ -> True
      CReuse -> True

needsRC :: CT -> Bool
needsRC ct = scanOf ct > 0

structName :: String -> String
structName canon = "kt_s" ++ Numeric.showHex (fnv canon) ""

fnv :: String -> Word64
fnv = foldl' (\h c -> (h `xor` fromIntegral (ord c)) * 1099511628211) 14695981039346656037

-- struct definitions

-- the definitions of the structs used by a type, nested ones first
structDefs :: CT -> [(String,String)]
structDefs ct
  = case ct of
      CProd name fs -> concatMap (structDefs . snd) fs ++ [(name, prodDef name [("f" ++ show i, f) | (i,f) <- fs])]
      CSum name alts -> concatMap structDefs [a | Just a <- alts] ++ [(name, sumDef name alts (scanOf ct - 1))]
      CBox -> []
      CPrim _ -> []
      CUnit -> []
      CEnum _ -> []
      CReuse -> []

guarded :: String -> String -> String
guarded name body = "#ifndef " ++ name ++ "_DEF\n#define " ++ name ++ "_DEF\n" ++ body ++ "#endif\n"

prodDef :: String -> [(String,CT)] -> String
prodDef name fs
  = guarded name ("typedef struct " ++ name ++ " {\n" ++ concat ["  " ++ ctName ct ++ " " ++ f ++ ";\n" | (f,ct) <- fs] ++ "} " ++ name ++ ";\n"
                  ++ dupDropDefs name [("x." ++ f, ct) | (f,ct) <- fs, needsRC ct])

sumDef :: String -> [Maybe CT] -> Int -> String
sumDef name alts scan
  = guarded name ("typedef struct " ++ name ++ " {\n  kk_value_tag_t _tag;\n  union {\n"
                  ++ concat ["    " ++ ctName ct ++ " c" ++ show i ++ ";\n" | (i,Just ct) <- zip [0::Int ..] alts]
                  ++ (if scan > 0 then "    kk_box_t _fields[" ++ show scan ++ "];\n" else "    int32_t _unused;\n")
                  ++ "  } _cons;\n} " ++ name ++ ";\n"
                  ++ dupDropDefs name [("x._cons._fields[" ++ show i ++ "]", CBox) | i <- [0..scan-1]])

-- `_dup` is always inlined, as in Koka's C backend, which dups the fields one by one:
-- on a cold path (the shared branch of `IsUnique`) clang would otherwise call it out
-- of line, which passes the struct through the stack and enlarges the caller's frame.
dupDropDefs :: String -> [(String,CT)] -> String
dupDropDefs name fs
  = "static inline __attribute__((always_inline)) " ++ name ++ " " ++ name ++ "_dup(" ++ name ++ " x, kk_context_t* _ctx) {\n"
    ++ concat ["  " ++ dupExpr ct f ++ ";\n" | (f,ct) <- fs]
    ++ "  return x;\n}\n"
    ++ "static inline void " ++ name ++ "_drop(" ++ name ++ " x, kk_context_t* _ctx) {\n"
    ++ concat ["  " ++ dropStmt ct f ++ "\n" | (f,ct) <- fs]
    ++ "}\n"

-- the functions that duplicate and drop a value of a C type, where it needs one
dupFun :: CT -> Maybe String
dupFun ct
  = case ct of
      CBox -> Just "kk_box_dup"
      CProd _ _ | needsRC ct -> Just (ctName ct ++ "_dup")
      CSum _ _  | needsRC ct -> Just (ctName ct ++ "_dup")
      _ -> Nothing   -- raw values need none; credits are linear and never duplicated

dropFun :: CT -> Maybe String
dropFun ct
  = case ct of
      CBox -> Just "kk_box_drop"
      CReuse -> Just "kt_reuse_drop"
      CProd _ _ | needsRC ct -> Just (ctName ct ++ "_drop")
      CSum _ _  | needsRC ct -> Just (ctName ct ++ "_drop")
      _ -> Nothing

dupExpr :: CT -> String -> String
dupExpr ct e = maybe e (\f -> f ++ "(" ++ e ++ ",_ctx)") (dupFun ct)

dropStmt :: CT -> String -> String
dropStmt ct e = maybe "" (\f -> f ++ "(" ++ e ++ ",_ctx);") (dropFun ct)

-- heap blocks of boxes

blockName :: CT -> String
blockName ct = "kt_b" ++ Numeric.showHex (fnv ("B:" ++ canonCT ct)) ""

blockDef :: CT -> (String,String)
blockDef ct
  = let name = blockName ct
    in (name, guarded name ("struct " ++ name ++ " { kk_block_t _block; " ++ ctName ct ++ " p; };\n"))

-- the size in bytes of the block of a box (checked by the C compiler where it is reused)
blockSize :: CT -> Int
blockSize ct = fst (structSize [(8,4), sizeAlign ct])

-- the offset and layout of each leaf of a payload, in the order of `leaves`
leafSlots :: CT -> [(Int,CT)]
leafSlots ct
  = case ct of
      CProd _ fs -> map snd (sortOn fst (zip (map fst fs) (zip (fieldOffsets (map (sizeAlign . snd) fs)) (map snd fs))))
      CUnit -> []
      _ -> [(0,ct)]

-- a box of this payload is a heap block (a box of unit is its tag)
isBlock :: CT -> Bool
isBlock ct
  = case ct of
      CProd _ _ -> True
      CSum _ _  -> True
      CBox      -> True
      CPrim _   -> True
      CEnum _   -> True
      CUnit     -> False
      CReuse    -> False

-- Koka boxes a raw value, or a struct of one, by itself (`Scalar V`). An enumeration is a
-- sum and boxed by its tag.
isScalar :: VType -> Bool
isScalar t
  = case (t,layout t) of
      (VSum _, _)  -> False
      (_, CPrim p) -> isJust (primBox p)
      (_, CEnum _) -> True
      _            -> False

sizeAlign :: CT -> (Int,Int)
sizeAlign ct
  = case ct of
      CBox -> (8,8)
      CReuse -> (8,8)
      CUnit -> (4,4)
      CEnum size -> let n = enumBytes size in (n,n)
      CPrim p -> let n = primSize p in (n,n)
      CProd _ fs -> structSize (map (sizeAlign . snd) fs)
      CSum _ alts -> let scan = scanOf ct - 1
                         members = [sizeAlign a | Just a <- alts] ++ [if scan > 0 then (8*scan,8) else (4,4)]
                         union = (alignUp (maximum (map fst members)) (maximum (map snd members)), maximum (map snd members))
                     in structSize [(8,8), union]

structSize :: [(Int,Int)] -> (Int,Int)
structSize fields
  = let align = maximum (1 : map snd fields)
        end   = foldl' (\off (size,al) -> alignUp off al + size) 0 fields
    in (alignUp end align, align)

fieldOffsets :: [(Int,Int)] -> [Int]
fieldOffsets = go 0
  where
    go _ [] = []
    go off ((size,al):fields) = let start = alignUp off al in start : go (start + size) fields

alignUp :: Int -> Int -> Int
alignUp n a = ((n + a - 1) `div` a) * a

primName :: PrimType -> String
primName p
  = case p of
      PrimChar      -> "kk_char_t"
      PrimSSize     -> "kk_ssize_t"
      PrimIntPtr    -> "intptr_t"
      PrimDouble    -> "double"
      PrimInt64     -> "int64_t"
      PrimUInt8     -> "uint8_t"
      PrimInt8      -> "int8_t"
      PrimInt16     -> "int16_t"
      PrimInt32     -> "int32_t"
      PrimFloat     -> "float"
      PrimFieldAddr -> "kk_field_addr_t"
      PrimBox       -> "kk_box_t"

primSize :: PrimType -> Int
primSize p
  = case p of
      PrimUInt8     -> 1
      PrimInt8      -> 1
      PrimInt16     -> 2
      PrimInt32     -> 4
      PrimChar      -> 4
      PrimFloat     -> 4
      PrimSSize     -> 8
      PrimIntPtr    -> 8
      PrimDouble    -> 8
      PrimInt64     -> 8
      PrimFieldAddr -> 8
      PrimBox       -> 8

rawCType :: Name -> PrimType
rawCType n
  | n == nameTpChar    = PrimChar
  | n == nameTpSSizeT  = PrimSSize
  | n == nameTpIntPtrT = PrimIntPtr
  | n == nameTpFloat   = PrimDouble
  | n == nameTpInt64   = PrimInt64
  | n == nameTpByte    = PrimUInt8
  | n == nameTpInt8    = PrimInt8
  | n == nameTpInt16   = PrimInt16
  | n == nameTpInt32 || n == nameTpMarker = PrimInt32
  | n == nameTpFloat32 = PrimFloat
  | n == nameTpFloat16 = PrimFloat
  | n == nameTpFieldAddr = PrimFieldAddr
  | n == nameTpAny     = PrimBox
  | otherwise          = PrimIntPtr

-- immediate boxing of raw values (as in Koka)
-- the largest `KK_INTF_SIZE` at which Koka's box of a scalar may be a heap block (kklib's
-- `box.h`), or `Nothing` if it may be one on every target
scalarHeapSize :: CT -> Maybe Int
scalarHeapSize ct
  = case ct of
      CEnum _ -> Just 4   -- boxed as an `int32`
      CPrim p -> case p of
                   PrimInt8      -> Just 0
                   PrimUInt8     -> Just 0
                   PrimInt16     -> Just 2
                   PrimInt32     -> Just 4
                   PrimFloat     -> Just 4
                   PrimChar      -> Just 4
                   PrimInt64     -> Just 8
                   PrimDouble    -> Just 8
                   PrimSSize     -> Nothing
                   PrimIntPtr    -> Nothing
                   PrimFieldAddr -> Nothing
                   PrimBox       -> Nothing
      _ -> Nothing

primBox :: PrimType -> Maybe (String,String)
primBox p
  = fmap (\base -> (base ++ "_box", base ++ "_unbox")) $
    case p of
      PrimChar      -> Just "kk_char"
      PrimSSize     -> Just "kk_ssize"
      PrimIntPtr    -> Just "kk_intptr"
      PrimDouble    -> Just "kk_double"
      PrimInt64     -> Just "kk_int64"
      PrimUInt8     -> Just "kk_uint8"
      PrimInt8      -> Just "kk_int8"
      PrimInt16     -> Just "kk_int16"
      PrimInt32     -> Just "kk_int32"
      PrimFloat     -> Just "kk_float"
      PrimFieldAddr -> Nothing
      PrimBox       -> Nothing
