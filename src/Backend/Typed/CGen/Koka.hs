-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- Koka's C conventions: names, and the C types of extern calls.
module Backend.Typed.CGen.Koka( kokaName, kokaTypeName, kokaLocal
                              , kokaKType, kokaPrimTypes
                              , toKoka, fromKoka, cIdents, isComment, substFormat
                              , externCType
                              ) where

import Data.Char( isAlphaNum, isDigit )
import Lib.PPrint( Doc, text, empty, (<.>) )
import qualified Common.Name as K
import Common.NamePrim
import Lidar.Name
import Backend.Typed.LidarName( toLidar, fromLidar )
import Backend.Typed.Syntax
import Backend.Typed.Layout( CT(..) )
import Backend.Typed.CGen.Layout( ctName )

-- Koka's C names (see Backend.C.FromCore)
kokaName :: Name -> String
kokaName = kName . fromLidar

kName :: K.Name -> String
kName name
  | K.isQualified name = "kk_" ++ kokaEncode True (show (K.qualifier name)) ++ "_" ++ K.asciiEncode False (show (K.unqualify name))
  | otherwise          = kokaEncode False (show name)
  where
    kokaEncode isModule s = K.asciiEncode isModule s

kokaTypeName :: Name -> String
kokaTypeName name = kName (K.prependRaw "@" (fromLidar name))

kokaLocal :: Name -> String
kokaLocal n
  = let s = K.asciiEncode False (show n)
    in if take 3 s == "kk_" || null s || isDigit (head s) || s `elem` cReserved then "kkloc_" ++ s else s

cReserved :: [String]
cReserved = ["bool","toString","arguments","eval","char","int","intptr_t","long","short","signed","size_t","ssize_t","intptr_t","uintptr_t","unsigned","uint8_t","double","auto","extern","float","goto","inline","restrict","sizeof","static","volatile","async","await","break","case","catch","class","continue","const","debugger","default","delete","do","else","finally","for","function","if","in","instanceof","new","return","register","switch","struct","this","throw","try","typeof","typedef","union","var","void","while","with","yield","class","enum","export","extends","import","super","errno","exception_info","or","timezone"]

-- conversions between our C types and Koka's C types

kokaPrimTypes :: [(Name,String)]
kokaPrimTypes
  = [(toLidar n,t) | (n,t) <- prims]
  where
    prims
      = [(nameTpInt,"kk_integer_t"),(nameTpString,"kk_string_t"),(nameTpBytes,"kk_bytes_t"),(nameTpVector,"kk_vector_t")
      ,(nameTpEvv,"kk_evv_t"),(nameTpChar,"kk_char_t"),(nameTpSSizeT,"kk_ssize_t"),(nameTpIntPtrT,"intptr_t")
      ,(nameTpFloat,"double"),(nameTpBool,"bool"),(nameTpUnit,"kk_unit_t"),(nameTpInt64,"int64_t"),(nameTpByte,"uint8_t")
      ,(nameTpInt8,"int8_t"),(nameTpInt16,"int16_t"),(nameTpInt32,"int32_t"),(nameTpMarker,"int32_t")
      ,(nameTpFloat32,"float"),(nameTpFloat16,"float"),(nameTpRef,"kk_ref_t"),(nameTpLocalVar,"kk_ref_t")
      ,(nameTpBox,"kk_box_t"),(nameTpAny,"kk_box_t"),(nameTpReuse,"kk_reuse_t"),(nameTpFieldAddr,"kk_field_addr_t")]

toKoka :: CT -> String -> Doc -> Doc
toKoka ct kt e
  | ctName ct == kt = e
  | otherwise
  = case ct of
      CEnum _ -> "((" <.> text kt <.> ")(" <.> e <.> "))"
      CPrim _ -> "((" <.> text kt <.> ")(" <.> e <.> "))"
      _ -> "kt_pun(" <.> text kt <.> "," <.> e <.> ")"

fromKoka :: String -> CT -> Doc -> Doc
fromKoka kt ct e
  | ctName ct == kt = e
  | otherwise
  = case ct of
      CEnum _ -> "((" <.> text (ctName ct) <.> ")(" <.> e <.> "))"
      CPrim _ -> "((" <.> text (ctName ct) <.> ")(" <.> e <.> "))"
      _ -> "kt_pun(" <.> text (ctName ct) <.> "," <.> e <.> ")"

-- Koka passes type variables of its lazy internals at their instance (see `Backend.C.Box`)
externCType :: Name -> KType -> VType -> String
externCType f kt t
  = case (kt,t) of
      (KBox, VPtr (ACon n _)) | f `elem` unboxedInternals -> kokaKType (KCon n)
      _ -> kokaKType kt

kokaKType :: KType -> String
kokaKType kt
  = case kt of
      KCon n -> maybe (kokaTypeName n) id (lookup n kokaPrimTypes)
      KBox   -> "kk_box_t"
      KFun   -> "kk_function_t"

unboxedInternals :: [Name]
unboxedInternals
  = map toLidar
    [nameLazyEnter, nameLazyLeave, nameLazyIsWhnf, nameLazyPtrIsWhnf
    ,nameDataTypePtrIsThreadShared, nameDataTypePtrIsUnique, nameLazyIndirectCompress]

-- the identifiers in a piece of C code
cIdents :: String -> [String]
cIdents s = case dropWhile (not . isIdent) s of
              "" -> []
              s' -> let (w,rest) = span isIdent s' in w : cIdents rest
  where isIdent c = isAlphaNum c || c == '_'

isComment :: String -> Bool
isComment fmt = case dropWhile (== ' ') fmt of
                  ('/':'*':_) -> True
                  ""          -> True
                  _           -> False

substFormat :: String -> [Doc] -> Doc
substFormat fmt args = go fmt
  where
    go [] = empty
    go ('\\':'#':xs) = "#" <.> go xs
    go ('#':d:xs) | isDigit d && d /= '0' = let i = fromEnum d - fromEnum '1'
                                            in (if i < length args then "(" <.> args !! i <.> ")" else "/*missing*/") <.> go xs
    -- Raw C newlines must not add indentation inside backslash-continued strings.
    go (x:xs) = text [x] <.> go xs
