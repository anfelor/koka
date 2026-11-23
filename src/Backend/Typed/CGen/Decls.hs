-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- The C declarations of the datatypes of a module in Koka's conventions (see `Backend.C.FromCore`),
  for the C code of `lib/`: Koka's type names, structs with Koka's field names, and the helpers
  `new_C`, `is_C`, `as_C`, `T_dup`, `T_drop`, `T_box` and `T_unbox`. They are built from our layout,
  so they agree with the generated code, which itself only uses the type names (at extern calls).

  A struct with Koka's field names needs each field to be contiguous in memory, and our layout
  flattens products. A constructor with a field of several leaves therefore gets no struct (and no
  `new_C` or `as_C`), and a value type with one is declared as its structural type. A value type
  gets a `T_box` where its box is a block or a scalar (one constructor, or an enumeration), and no
  `T_unbox`. Static assertions check that the named structs agree with our layouts.
-}
module Backend.Typed.CGen.Decls( typeDecls, openPayload, openTagName ) where

import qualified Data.Map as M
import Data.Graph( stronglyConnComp, flattenSCCs )
import Data.List( intercalate )
import Data.Maybe( catMaybes, isNothing )
import Lib.PPrint( text )
import Lidar.Name
import Lidar.Prim( nameTpString )
import Backend.Typed.Syntax
import Backend.Typed.Layout
import Backend.Typed.CGen.Layout( cName, ctName, structDefs, blockName, blockDef, dupFun, dropFun, primBox )
import Backend.Typed.CGen.Koka( kokaName, kokaTypeName, kokaLocal, kokaKType, kokaPrimTypes, fromKoka )

-- The payload of the block of an open constructor: the tag string of the constructor (the `_tag`
-- of Koka's base struct), followed by the fields.
openPayload :: [VType] -> VType
openPayload fs = VProd ((posField 0, VPtr (ACon nameTpString [])) : [(posField i, f) | (i,f) <- zip [1..] fs])

-- the top-level string that tags the blocks of an open constructor
openTagName :: Name -> Name
openTagName c = makeHiddenName "tag" c

-- The declarations of the datatypes and open constructors of a module. Value types are declared in dependency order, after the reference types.
typeDecls :: Name -> Program -> [String]
typeDecls modName prog
  = concatMap baseDecls refs ++ concatMap valueDecls (dependencyOrder values)
    ++ concatMap refConDecls refs ++ concatMap openConDecls opens
  where
    owned n = isQualified n && qualifier n == modName
    own     = [d | d <- M.elems (progTypes prog), owned (tdefName d), isNothing (lookup (tdefName d) kokaPrimTypes)]
    values  = [(d,v) | d@TypeDef{ tdefBody = BodyValue v } <- own]
    refs    = [d | d <- own, not (isValueBody (tdefBody d))]
    opens   = [(c,fs,n) | (c,SigCon _ fs n) <- M.toList (progSigs prog), owned c]
    isValueBody (BodyValue _) = True
    isValueBody _ = False

dependencyOrder :: [(TypeDef,VType)] -> [(TypeDef,VType)]
dependencyOrder vs
  = flattenSCCs (stronglyConnComp [(x, tdefName d, concatMap (catMaybes . lblDecls) (tdefLabels d)) | x@(d,_) <- vs])

-- reference, abstract and open types

baseDecls :: TypeDef -> [String]
baseDecls d
  = [ "struct " ++ tn ++ "_s { kk_block_t _block;" ++ (if isOpen then " kk_string_t _tag;" else "") ++ " };"
    , "typedef kk_datatype_t " ++ tn ++ ";"
    , fun tn (tn ++ "_dup") [tn ++ " _x"] ["return kk_datatype_dup(_x,_ctx);"]
    , fun "void" (tn ++ "_drop") [tn ++ " _x"] ["kk_datatype_drop(_x,_ctx);"]
    , fun "kk_box_t" (tn ++ "_box") [tn ++ " _x"] ["return kk_datatype_box(_x);"]
    , fun tn (tn ++ "_unbox") ["kk_box_t _x", "kk_borrow_t _borrow"] ["return kk_datatype_unbox(_x);"] ]
  where
    tn = kokaTypeName (tdefName d)
    isOpen = case tdefBody d of { BodyOpen -> True; _ -> False }

-- the constructors of a reference type, which are our alternatives in order (not those of a lazy type)
refConDecls :: TypeDef -> [String]
refConDecls d
  = case tdefBody d of
      BodyRef a | Just alts <- refAlts a, length alts == length (tdefLabels d)
        -> concat (zipWith (refCon tn (length alts == 1) (all (isBox . snd) alts)) alts (tdefLabels d))
      _ -> []
  where
    tn = kokaTypeName (tdefName d)
    refAlts a = case a of
                  ASum ts -> Just ts
                  ALazy _ _ -> Nothing
                  _ -> Just [(1,a)]
    isBox (ABox _) = True
    isBox _ = False

refCon :: String -> Bool -> Bool -> (Int,AType) -> ConLabel -> [String]
refCon tn single allHeap (tag,shape) lbl
  = case shape of
      AUnit -> [ fun tn (conNew c) [] ["return kk_datatype_from_tag(" ++ ktag ++ ");"]
               , fun "bool" (conIs c) [tn ++ " x"] ["return kk_datatype_has_singleton_tag(x," ++ ktag ++ ");"] ]
      ABox v -> fun "bool" (conIs c) [tn ++ " x"] ["return " ++ test ++ ";"]
                : maybe [] (heapCon v) (namedFields lbl v)
      _ -> []
  where
    c = lblCon lbl
    ktag = "(kk_tag_t)" ++ show tag
    sname = "struct " ++ kokaName c
    test | single    = "true"
         | allHeap   = "kk_datatype_ptr_has_tag(x," ++ ktag ++ ",_ctx)"
         | otherwise = "kk_datatype_has_ptr_tag(x," ++ ktag ++ ",_ctx)"
    heapCon v fields
      = let ct = layout v
        in blockDefs ct ++
           [ sname ++ " {\n  struct " ++ tn ++ "_s _base;" ++ concat ["\n  " ++ ty ++ " " ++ f ++ ";" | (ty,f,_) <- fields] ++ "\n};"
           , fun tn (conNew c) (["kk_reuse_t _at", "int32_t _cpath"] ++ params lbl v)
               ([sname ++ "* _con = kk_block_alloc_at_as(" ++ sname ++ ", _at, " ++ show (scanOf ct) ++ ", _cpath, " ++ ktag ++ ", _ctx);"]
                ++ ["_con->" ++ f ++ " = " ++ f ++ ";" | (_,f,_) <- fields]
                ++ ["return kk_datatype_from_base(&_con->_base, _ctx);"])
           , fun (sname ++ "*") (conAs c) [tn ++ " x"] ["return kk_datatype_as(" ++ sname ++ "*, x, _ctx);"] ]
           ++ [assertEq ("offsetof(" ++ sname ++ "," ++ f ++ ")") (blockLeafOffset ct j) | (_,f,j) <- fields]

-- value types

valueDecls :: (TypeDef,VType) -> [String]
valueDecls (d,v)
  = case v of
      -- (a single constructor whose only field is a sum is that sum, see `conFields`)
      VSum ts | length ts == length labels, isEnum v -> enumDecls ts ++ dupDrop ++ [enumBox]
      VSum ts | length ts == length labels, Just alts <- mapM altFields (zip ts labels) -> sumDecls ts alts ++ dupDrop
      VSum _ | length labels > 1 -> structural ++ dupDrop
      _ | [lbl] <- labels, not (null (leaves v)), Just fields <- namedFields lbl v
        -> singleDecls lbl fields ++ dupDrop ++ box
      _ -> structural ++ dupDrop ++ box
  where
    tn = kokaTypeName (tdefName d)
    ct = layout v
    labels = tdefLabels d
    structural = structDefsOf ct ++ ["typedef " ++ ctName ct ++ " " ++ tn ++ ";"]
    pun e = "kt_pun(" ++ ctName ct ++ "," ++ e ++ ")"
    dupDrop = [ fun tn (tn ++ "_dup") [tn ++ " _x"] ["return " ++ maybe "_x" (\f -> "kt_pun(" ++ tn ++ "," ++ f ++ "(" ++ pun "_x" ++ ",_ctx))") (dupFun ct) ++ ";"]
              , fun "void" (tn ++ "_drop") [tn ++ " _x"] [maybe "" (\f -> f ++ "(" ++ pun "_x" ++ ",_ctx);") (dropFun ct)] ]

    -- an enumeration is boxed as the singleton of its tag (`Elab.Representation.boxA`)
    enumDecls ts
      = [ "enum " ++ tn ++ "_e { " ++ intercalate ", " [kokaName c | (Con c,_) <- ts] ++ " };"
        , "typedef " ++ ctName ct ++ " " ++ tn ++ ";" ]
        ++ concat [ [ fun tn (conNew c) [] ["return " ++ kokaName c ++ ";"]
                    , fun "bool" (conIs c) [tn ++ " x"] ["return (x == " ++ kokaName c ++ ");"] ] | (Con c,_) <- ts]
    enumBox = fun "kk_box_t" (tn ++ "_box") [tn ++ " _x"] ["return kk_datatype_box(kk_datatype_from_tag((kk_tag_t)_x + 1));"]

    -- the named fields of each alternative with leaves
    altFields ((_,s),lbl)
      | null (leaves s) = Just Nothing
      | otherwise = Just <$> namedFields lbl s

    sumDecls ts alts
      = let scan = scanOf ct - 1
            sname = kokaName (tdefName d) ++ "_s"
            cons = zip3 [1 :: Int ..] (zip ts labels) alts
        in structDefsOf ct
           ++ [conStruct c fs | (_,((Con c,_),_),Just fs) <- cons]
           ++ [ "struct " ++ sname ++ " {\n  kk_value_tag_t _tag;\n  union {"
                ++ concat ["\n    struct " ++ kokaName c ++ " " ++ member c ++ ";" | (_,((Con c,_),_),Just _) <- cons]
                ++ (if scan > 0 then "\n    kk_box_t _fields[" ++ show scan ++ "];" else "\n    int32_t _unused;")
                ++ "\n  } _cons;\n};"
              , "typedef struct " ++ sname ++ " " ++ tn ++ ";"
              , assertEq ("sizeof(" ++ tn ++ ")") ("sizeof(" ++ ctName ct ++ ")") ]
           ++ concat [ [ fun tn (conNew c) (params lbl s)
                           ([tn ++ " _con;", "_con._tag = kk_value_tag(" ++ show i ++ ");"]
                            ++ ["_con._cons._fields[" ++ show j ++ "] = kk_box_null();" | j <- [0..scan-1]]
                            ++ ["_con._cons." ++ member c ++ "." ++ f ++ " = " ++ f ++ ";" | Just fs <- [alt], (_,f,_) <- fs]
                            ++ ["return _con;"])
                       , fun "bool" (conIs c) [tn ++ " x"] ["return kk_value_tag_eq(x._tag, kk_value_tag(" ++ show i ++ "));"] ]
                       ++ [assertEq ("offsetof(struct " ++ kokaName c ++ "," ++ f ++ ")") (leafOffset (layout s) j) | Just fs <- [alt], (_,f,j) <- fs]
                     | (i,((Con c,s),lbl),alt) <- cons ]

    singleDecls lbl fields
      = let c = lblCon lbl
        in structDefsOf ct
           ++ [ conStruct c fields
              , "typedef struct " ++ kokaName c ++ " " ++ tn ++ ";"
              , assertEq ("sizeof(" ++ tn ++ ")") ("sizeof(" ++ ctName ct ++ ")") ]
           ++ [assertEq ("offsetof(" ++ tn ++ "," ++ f ++ ")") (leafOffset ct j) | (_,f,j) <- fields]
           ++ [ fun tn (conNew c) (params lbl v) ([tn ++ " _con;"] ++ ["_con." ++ f ++ " = " ++ f ++ ";" | (_,f,_) <- fields] ++ ["return _con;"])
              , fun "bool" (conIs c) [tn ++ " x"] ["return true;"] ]

    -- as `Elab.Representation.boxA`: a raw value as a scalar, other values in a block with tag 1
    box = case leaves v of
            [] -> []
            [VRaw r] -> [fun "kk_box_t" (tn ++ "_box") [tn ++ " _x"] ["return " ++ fst (primBox r) ++ "(" ++ pun "_x" ++ ",_ctx);"]]
            [s] | isEnum s -> []
            _ -> let bt = "struct " ++ blockName ct
                 in blockDefs ct ++
                    [fun "kk_box_t" (tn ++ "_box") [tn ++ " _x"]
                       [bt ++ "* _b = kk_block_alloc_as(" ++ bt ++ ", " ++ show (scanOf ct) ++ ", (kk_tag_t)1, _ctx);"
                       ,"_b->p = " ++ pun "_x" ++ ";"
                       ,"return kt_box_from_block(&_b->_block,_ctx);"]]

conStruct :: Name -> [(String,String,Int)] -> String
conStruct c fields = "struct " ++ kokaName c ++ " {" ++ concat ["\n  " ++ ty ++ " " ++ f ++ ";" | (ty,f,_) <- fields] ++ "\n};"

member :: Name -> String
member c = kokaLocal (unqualify c)

-- open constructors

-- `new_C` of an open constructor (its fields have positional names)
openConDecls :: (Name,[VType],Name) -> [String]
openConDecls (c,fs,n)
  | any ((> 1) . length . leaves) fs = []
  | otherwise
  = blockDefs ct ++
    [ "extern kk_box_t " ++ tag ++ ";"
    , fun (kokaTypeName n) (conNew c) (reuseParams ++ [kokaFieldType Nothing t ++ " " ++ x | (x,t) <- xs])
        ([bt ++ "* _b = kk_block_alloc_at_as(" ++ bt ++ ", " ++ at ++ ", " ++ show (scanOf ct) ++ ", " ++ cpath ++ ", KK_TAG_OPEN, _ctx);"
         ,"_b->" ++ leaf 0 ++ " = kk_box_dup(" ++ tag ++ ",_ctx);"]
         ++ ["_b->" ++ leaf j ++ " = " ++ show (fromKoka (kokaFieldType Nothing t) (layout t) (text x)) ++ ";"
            | (j,(x,t)) <- zip [1..] [xt | xt@(_,t) <- xs, not (null (leaves t))]]
         ++ ["return kk_datatype_from_ptr(&_b->_block,_ctx);"]) ]
  where
    ct  = layout (openPayload fs)
    bt  = "struct " ++ blockName ct
    tag = cName (openTagName c)
    xs  = [("x" ++ show i, t) | (i,t) <- zip [0 :: Int ..] fs]
    (reuseParams,at,cpath) | null fs   = ([], "kk_reuse_null", "0")
                           | otherwise = (["kk_reuse_t _at", "int32_t _cpath"], "_at", "_cpath")
    leaf j = case ct of
               CProd _ -> "p.f" ++ show (j :: Int)
               _ -> "p"

-- fields

-- The fields of a constructor with the payload `v`, with their declared types: a constructor has
-- no payload, that of its only field, or the product of its fields (`Types.prodFields`).
conFields :: ConLabel -> VType -> [(Field,VType,Maybe Name)]
conFields lbl v = zip3 (lblFields lbl) types (lblDecls lbl ++ repeat Nothing)
  where
    types = case (lblFields lbl, unpacked v) of
              ([],_) -> []
              ([_],t) -> [t]
              (_,VProd fs) -> map snd fs
              (_,t) -> [t]
    unpacked (VExists _ b) = unpacked b
    unpacked t = t

-- The fields with leaves of a constructor in memory order, with their Koka C type, C name and leaf
-- index, if each field has at most one leaf.
namedFields :: ConLabel -> VType -> Maybe [(String,String,Int)]
namedFields lbl v
  | any ((> 1) . length . leaves . snd3) fs = Nothing
  | otherwise = Just [byLeaf !! j | j <- memoryOrder]
  where
    fs = conFields lbl v
    snd3 (_,t,_) = t
    byLeaf = [(kokaFieldType d t, fieldName f, j) | (j,(f,t,d)) <- zip [0..] [x | x@(_,t,_) <- fs, not (null (leaves t))]]
    memoryOrder = case layout v of
                    CProd lfs -> map fst lfs
                    _ -> [0 .. length byLeaf - 1]

-- the parameters of `new_C`: all fields in source order
params :: ConLabel -> VType -> [String]
params lbl v = [kokaFieldType d t ++ " " ++ fieldName f | (f,t,d) <- conFields lbl v]

fieldName :: Field -> String
fieldName (Field n) = kokaLocal (unqualify n)

-- Koka's C type of a field: that of its declared value type, or of its type
kokaFieldType :: Maybe Name -> VType -> String
kokaFieldType decl t
  = case (decl,t) of
      (Just n,_) -> kokaKType (KCon n)
      (_,VPtr a) -> ptrType a
      (_,VExists _ b) -> kokaFieldType Nothing b
      _ -> ctName (layout t)
  where
    ptrType a = case a of
                  ACon n _ -> kokaKType (KCon n)
                  AFun _ _ -> kokaKType KFun
                  AForall _ b -> ptrType b
                  _ -> kokaKType KBox

-- C syntax

conNew, conIs, conAs :: Name -> String
conNew c = kokaName (makeHiddenName "new" c)
conIs c = kokaName (makeHiddenName "is" c)
conAs c = kokaName (makeHiddenName "as" c)

-- a static inline function with a context parameter
fun :: String -> String -> [String] -> [String] -> String
fun res name ps body
  = "static inline " ++ res ++ " " ++ name ++ "(" ++ intercalate ", " (ps ++ ["kk_context_t* _ctx"]) ++ ") {"
    ++ concat ["\n  " ++ s | s <- body, not (null s)] ++ "\n}"

assertEq :: String -> String -> String
assertEq a b = "_Static_assert(" ++ a ++ " == " ++ b ++ ", \"kt_decl\");"

-- the offset of leaf `j` in a value of layout `ct`, and in the block of a box of it
leafOffset :: CT -> Int -> String
leafOffset ct j
  = case ct of
      CProd _ -> "offsetof(" ++ ctName ct ++ ",f" ++ show j ++ ")"
      _ -> "0"

blockLeafOffset :: CT -> Int -> String
blockLeafOffset ct j = "offsetof(struct " ++ blockName ct ++ ",p) + " ++ leafOffset ct j

-- the layout structs (defined by `CGen.Layout`, guarded against repetition)
structDefsOf :: CT -> [String]
structDefsOf ct = [init s | (_,s) <- structDefs ct]

blockDefs :: CT -> [String]
blockDefs ct = structDefsOf ct ++ [init (snd (blockDef ct))]
