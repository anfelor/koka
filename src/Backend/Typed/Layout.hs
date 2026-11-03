-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-- Memory representations shared by typed IR queries, validation and code generation.
-- Products are flattened and ordered with scanned words first, then raw fields by
-- decreasing alignment. Sums have a tag and storage for their largest alternative.
-- Sizes and alignment currently assume 64-bit words.
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Layout( leaves, isEnum, CT(..), EnumSize(..), enumBytes, layout, orderFields, shapeIsHeap
                           , checkLayout, scanOf, blockSize, sizeAlign, fieldOffsets
                           ) where

import Data.List( foldl', sortOn )
import Data.Ord( Down(..) )
import Backend.Typed.Syntax

-- leaves of a product
leaves :: VType -> [VType]
leaves t
  = case t of
      VProd fs -> concatMap (leaves . snd) fs
      VExists _ b -> leaves b
      VUnit -> []
      VPtr _ -> [t]
      VSum _ -> [t]
      VRaw _ -> [t]
      VReuse _ _ _ -> [t]
      VCtx _ a b -> [VPtr a, VPtr b]
      VCell _ _ -> [t]

isEnum :: VType -> Bool
isEnum t
  = case t of
      VSum ts -> length ts > 1 && all (isUnitT . snd) ts
      _ -> False
  where
    isUnitT VUnit = True
    isUnitT (VProd fs) = all (isUnitT . snd) fs
    isUnitT (VExists _ b) = isUnitT b
    isUnitT _ = False

data CT = CBox
        | CPrim Raw
        | CUnit
        | CEnum EnumSize              -- the width of the tag
        | CProd [(Int,CT)]            -- leaves in memory order, with their position in the product
        | CSum [Maybe CT]             -- the payload of each alternative (if not unit)
        | CReuse                      -- a reuse credit
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
shapeIsHeap (ABox _) = Just True
shapeIsHeap (ASum ((_,t):ts))
  = do b <- shapeIsHeap t
       bs <- mapM (shapeIsHeap . snd) ts
       if all (== b) bs then Just b else Nothing
shapeIsHeap _ = Nothing

-- The layout of a type, with the leaves of a product in memory order.
layout :: VType -> CT
layout t
  = case t of
      VRaw r      -> CPrim r
      VExists _ b -> layout b
      VReuse _ _ _  -> CReuse
      VSum ts | isEnum t -> CEnum (enumSize (length ts))
      VSum ts     -> CSum (map (altLayout . snd) ts)
      VProd _     -> case map layout (leaves t) of
                       [] -> CUnit
                       [ct] -> ct
                       cts  -> CProd (orderFields (zip [0..] cts))
      VUnit       -> CUnit
      VPtr _      -> CBox
      -- Koka's `cctx`: `res` and the address of the hole, which is boxed as a value
      -- (`kk_field_addr_t`), so duplicating and dropping it does nothing
      VCtx _ a b  -> layout (VProd [(posField 0,VPtr a),(posField 1,VPtr b)])
      -- a cell is the pointer to its block
      VCell _ _   -> CBox
  where
    altLayout s = case layout s of
                    CUnit -> Nothing
                    ct    -> Just ct

enumSize :: Int -> EnumSize
enumSize n
  | n <= 256   = Enum8
  | n <= 65536 = Enum16
  | otherwise  = Enum32

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

scanOf :: CT -> Int
scanOf ct
  = case ct of
      CBox -> 1
      CProd fs -> sum (map (scanOf . snd) fs)
      CSum alts -> 1 + maximum (0 : map (maybe 0 scanOf) alts)
      CPrim _ -> 0
      CUnit -> 0
      CEnum _ -> 0
      CReuse -> 0

rawOf :: CT -> Bool
rawOf ct
  = case ct of
      CBox -> False
      CUnit -> False
      CProd fs -> any (rawOf . snd) fs
      CSum alts -> any (maybe False rawOf) alts
      CPrim _ -> True
      CEnum _ -> True
      CReuse -> True

-- The size in bytes of the block of a box (checked by the C compiler where it is reused).
blockSize :: CT -> Int
blockSize CUnit = 8
blockSize ct = fst (structSize [(8,4), sizeAlign ct])

sizeAlign :: CT -> (Int,Int)
sizeAlign ct
  = case ct of
      CBox -> (8,8)
      CReuse -> (8,8)
      CUnit -> (4,4)
      CEnum size -> let n = enumBytes size in (n,n)
      CPrim p -> let n = primSize p in (n,n)
      CProd fs -> structSize (map (sizeAlign . snd) fs)
      CSum alts -> let scan = scanOf ct - 1
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

primSize :: Raw -> Int
primSize r
  = case r of
      RUInt8   -> 1
      RInt8    -> 1
      RInt16   -> 2
      RInt32   -> 4
      RChar    -> 4
      RFloat32 -> 4
      RSSize   -> 8
      RIntPtr  -> 8
      RFloat64 -> 8
      RInt64   -> 8

-- Every advertised scanned word must be a boxed word, at the start of the
-- object. Counts alone are insufficient for products of mixed aggregates.
checkLayout :: CT -> [String]
checkLayout ct = prefix ++ nested
  where
    prefix = ["invalid scanned prefix in " ++ show ct
             | scanned ct /= [0,8 .. 8 * scanOf ct - 1]
               || any (\(off,n) -> off < 8 * scanOf ct && off+n > 0) (rawRanges ct)]
    nested = case ct of
      CProd fs -> concatMap (checkLayout . snd) fs
      CSum as -> concatMap checkLayout [a | Just a <- as]
      _ -> []
    fields fs = zip (fieldOffsets (map (sizeAlign . snd) fs)) (map snd fs)
    scanned c = case c of
      CBox -> [0]
      CProd fs -> [off+i | (off,f) <- fields fs, i <- scanned f]
      CSum{} -> [0,8 .. 8 * scanOf c - 1]
      _ -> []
    rawRanges c = case c of
      CProd fs -> [(off+i,n) | (off,f) <- fields fs, (i,n) <- rawRanges f]
      CSum as -> [(8+i,n) | Just a <- as, (i,n) <- rawRanges a]
      CBox -> []
      CUnit -> []
      _ -> [(0,fst (sizeAlign c))]
