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
module Backend.Typed.Layout( CT(..), layout, leaves, leafSlots, isEnum, orderFields, shapeIsHeap
                           , ctName, scanOf, rawOf, needsRC
                           , structDefs, blockName, blockDef, blockSize, isBlock
                           , dupExpr, dropStmt, rawCType, primBox, fnv
                           ) where

import Data.Char( ord )
import Data.Bits( xor )
import Data.Word( Word64 )
import Data.List( intercalate, foldl', sortOn )
import Data.Ord( Down(..) )
import qualified Numeric
import Common.Name
import Common.NamePrim
import Backend.Typed.Syntax

data CT = CBox
        | CPrim String
        | CUnit
        | CEnum Int                   -- the size in bytes of the tag (1, 2 or 4)
        | CProd String [(Int,CT)]     -- leaves in memory order, with their position in the product
        | CSum String [Maybe CT]      -- the payload of each alternative (if not unit)
        | CReuse                      -- a reuse credit
        deriving (Eq,Show)

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
      VReuse _ _    -> CReuse
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
      VCtx a b    -> layout (VProd (VPtr a) (VPtr b))
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
      VReuse _ _ -> [t]
      VCtx a b -> [VPtr a, VPtr b]

enumSize :: Int -> Int
enumSize n
  | n <= 256   = 1
  | n <= 65536 = 2
  | otherwise  = 4

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
      CPrim p -> p
      CUnit -> "kk_unit_t"
      CEnum 1 -> "uint8_t"
      CEnum 2 -> "uint16_t"
      CEnum _ -> "uint32_t"
      CProd n _ -> n
      CSum n _ -> n
      CReuse -> "kk_reuse_t"

canonCT :: CT -> String
canonCT ct
  = case ct of
      CBox -> "B"
      CUnit -> "U"
      CEnum n -> "E" ++ show n
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

dupDropDefs :: String -> [(String,CT)] -> String
dupDropDefs name fs
  = "static inline " ++ name ++ " " ++ name ++ "_dup(" ++ name ++ " x, kk_context_t* _ctx) {\n"
    ++ concat ["  " ++ dupExpr ct f ++ ";\n" | (f,ct) <- fs]
    ++ "  return x;\n}\n"
    ++ "static inline void " ++ name ++ "_drop(" ++ name ++ " x, kk_context_t* _ctx) {\n"
    ++ concat ["  " ++ dropStmt ct f ++ "\n" | (f,ct) <- fs]
    ++ "}\n"

dupExpr :: CT -> String -> String
dupExpr ct e
  = case ct of
      CBox -> "kk_box_dup(" ++ e ++ ",_ctx)"
      CProd _ _ | needsRC ct -> ctName ct ++ "_dup(" ++ e ++ ",_ctx)"
      CSum _ _  | needsRC ct -> ctName ct ++ "_dup(" ++ e ++ ",_ctx)"
      CProd _ _ -> e
      CSum _ _  -> e
      CPrim _ -> e
      CUnit -> e
      CEnum _ -> e
      CReuse -> e   -- credits are linear and never duplicated

dropStmt :: CT -> String -> String
dropStmt ct e
  = case ct of
      CBox -> "kk_box_drop(" ++ e ++ ",_ctx);"
      CReuse -> "kt_reuse_drop(" ++ e ++ ",_ctx);"
      CProd _ _ | needsRC ct -> ctName ct ++ "_drop(" ++ e ++ ",_ctx);"
      CSum _ _  | needsRC ct -> ctName ct ++ "_drop(" ++ e ++ ",_ctx);"
      CProd _ _ -> ""
      CSum _ _  -> ""
      CPrim _ -> ""
      CUnit -> ""
      CEnum _ -> ""

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

-- a box of this payload is always a heap block (raw values may be boxed in place)
isBlock :: CT -> Bool
isBlock ct
  = case ct of
      CProd _ _ -> True
      CSum _ _  -> True
      CBox      -> True
      CPrim _   -> False
      CUnit     -> False
      CEnum _   -> False
      CReuse    -> False

sizeAlign :: CT -> (Int,Int)
sizeAlign ct
  = case ct of
      CBox -> (8,8)
      CReuse -> (8,8)
      CUnit -> (4,4)
      CEnum n -> (n,n)
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

primSize :: String -> Int
primSize p
  = case p of
      "uint8_t" -> 1
      "int8_t"  -> 1
      "int16_t" -> 2
      "uint16_t" -> 2
      "uint32_t" -> 4
      "int32_t" -> 4
      "kk_char_t" -> 4
      "float"   -> 4
      _         -> 8

rawCType :: Name -> String
rawCType n
  | n == nameTpChar    = "kk_char_t"
  | n == nameTpSSizeT  = "kk_ssize_t"
  | n == nameTpIntPtrT = "intptr_t"
  | n == nameTpFloat   = "double"
  | n == nameTpInt64   = "int64_t"
  | n == nameTpByte    = "uint8_t"
  | n == nameTpInt8    = "int8_t"
  | n == nameTpInt16   = "int16_t"
  | n == nameTpInt32 || n == nameTpMarker = "int32_t"
  | n == nameTpFloat32 = "float"
  | n == nameTpFloat16 = "float"
  | n == nameTpFieldAddr = "kk_field_addr_t"
  | n == nameTpAny     = "kk_box_t"
  | otherwise          = "intptr_t"

-- immediate boxing of raw values (as in Koka)
primBox :: String -> Maybe (String,String)
primBox p
  | p `elem` ["kk_char_t","int64_t","int32_t","int16_t","int8_t","uint8_t","double","float","intptr_t","kk_ssize_t"]
  = let base = case p of
                 "kk_char_t"  -> "kk_char"
                 "double"     -> "kk_double"
                 "float"      -> "kk_float"
                 "kk_ssize_t" -> "kk_ssize"
                 _            -> "kk_" ++ takeWhile (/= '_') p
    in Just (base ++ "_box", base ++ "_unbox")
  | otherwise = Nothing
