-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-- C names, declarations and runtime operations for the shared memory layouts.
-- Struct names are hashes of their canonical layouts so modules agree on them.
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.CGen.Layout( ctName, structDefs, blockName, blockDef, leafSlots
                            , needsRC, dupExpr, dropStmt, dupFun, dropFun
                            , primBox, scalarHeapSize, shapeIsSmall, fnv
                            ) where

import Data.Char( ord )
import Data.Bits( xor )
import Data.Word( Word64 )
import Data.List( intercalate, foldl', sortOn )
import qualified Numeric
import Backend.Typed.Syntax
import Backend.Typed.Layout

ctName :: CT -> String
ctName ct
  = case ct of
      CBox -> "kk_box_t"
      CPrim p -> primName p
      CUnit -> "kk_unit_t"
      CEnum Enum8  -> "uint8_t"
      CEnum Enum16 -> "uint16_t"
      CEnum Enum32 -> "uint32_t"
      CProd fs -> structName ("P(" ++ intercalate "," [show i ++ ":" ++ canonCT f | (i,f) <- fs] ++ ")")
      CSum alts -> structName ("S[" ++ intercalate "|" (map (maybe "U" canonCT) alts) ++ "]")
      CReuse -> "kk_reuse_t"

canonCT :: CT -> String
canonCT ct
  = case ct of
      CBox -> "B"
      CUnit -> "U"
      CEnum size -> "E" ++ show (enumBytes size)
      CPrim _ -> ctName ct
      CProd _ -> ctName ct
      CSum _ -> ctName ct
      CReuse -> ctName ct

structName :: String -> String
structName canon = "kt_s" ++ Numeric.showHex (fnv canon) ""

fnv :: String -> Word64
fnv = foldl' (\h c -> (h `xor` fromIntegral (ord c)) * 1099511628211) 14695981039346656037

needsRC :: CT -> Bool
needsRC ct = scanOf ct > 0

-- struct definitions

-- the definitions of the structs used by a type, nested ones first
structDefs :: CT -> [(String,String)]
structDefs ct
  = case ct of
      CProd fs -> concatMap (structDefs . snd) fs ++ [(name, prodDef name [("f" ++ show i, f) | (i,f) <- fs])]
      CSum alts -> concatMap structDefs [a | Just a <- alts] ++ [(name, sumDef name alts (scanOf ct - 1))]
      CBox -> []
      CPrim _ -> []
      CUnit -> []
      CEnum _ -> []
      CReuse -> []
  where name = ctName ct

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
      CProd _ | needsRC ct -> Just (ctName ct ++ "_dup")
      CSum _  | needsRC ct -> Just (ctName ct ++ "_dup")
      _ -> Nothing   -- raw values need none; credits are linear and never duplicated

dropFun :: CT -> Maybe String
dropFun ct
  = case ct of
      CBox -> Just "kk_box_drop"
      CReuse -> Just "kt_reuse_drop"
      CProd _ | needsRC ct -> Just (ctName ct ++ "_drop")
      CSum _  | needsRC ct -> Just (ctName ct ++ "_drop")
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
    in (name, guarded name ("struct " ++ name ++ " { kk_block_t _block;" ++ payload ++ " };\n"))
  where
    payload = case ct of
                CUnit -> ""
                _ -> " " ++ ctName ct ++ " p;"

-- the offset and layout of each leaf of a payload, in the order of `leaves`
leafSlots :: CT -> [(Int,CT)]
leafSlots ct
  = case ct of
      CProd fs -> map snd (sortOn fst (zip (map fst fs) (zip (fieldOffsets (map (sizeAlign . snd) fs)) (map snd fs))))
      CUnit -> []
      _ -> [(0,ct)]

primName :: Raw -> String
primName r
  = case r of
      RChar    -> "kk_char_t"
      RSSize   -> "kk_ssize_t"
      RIntPtr  -> "intptr_t"
      RFloat64 -> "double"
      RFloat32 -> "float"
      RInt64   -> "int64_t"
      RInt32   -> "int32_t"
      RInt16   -> "int16_t"
      RInt8    -> "int8_t"
      RUInt8   -> "uint8_t"

-- immediate boxing of raw values (as in Koka)
-- the largest `KK_INTF_SIZE` at which Koka's box of a scalar may be a heap block (kklib's
-- `box.h`), or `Nothing` if it may be one on every target
scalarHeapSize :: Raw -> Maybe Int
scalarHeapSize r
  = case r of
      RInt8    -> Just 0
      RUInt8   -> Just 0
      RInt16   -> Just 2
      RInt32   -> Just 4
      RFloat32 -> Just 4
      RChar    -> Just 4
      RInt64   -> Just 8
      RFloat64 -> Just 8
      RSSize   -> Nothing
      RIntPtr  -> Nothing

primBox :: Raw -> (String,String)
primBox r
  = (\base -> (base ++ "_box", base ++ "_unbox")) $
    case r of
      RChar    -> "kk_char"
      RSSize   -> "kk_ssize"
      RIntPtr  -> "kk_intptr"
      RFloat64 -> "kk_double"
      RFloat32 -> "kk_float"
      RInt64   -> "kk_int64"
      RInt32   -> "kk_int32"
      RInt16   -> "kk_int16"
      RInt8    -> "kk_int8"
      RUInt8   -> "kk_uint8"

-- The small free path requires a fixed allocation of at most 128 words,
-- excluding runtime objects such as strings, vectors and arbitrary opaque boxes.
-- Like the rest of the layout calculations, sizes here use 64-bit words.
shapeIsSmall :: AType -> Bool
shapeIsSmall a = case a of
  AUnit -> True
  ABox v -> blockSize (layout v) <= 128 * 8
  ASum ts -> not (null ts) && all (\(i,b) -> i > 0 && i <= 0xFFC0 && shapeIsSmall b) ts
  _ -> False
