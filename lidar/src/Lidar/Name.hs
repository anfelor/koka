-----------------------------------------------------------------------------
-- Copyright 2012-2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -funbox-strict-fields #-}
{- Names of the typed IR.

  A copy of the part of Koka's `Common.Name` that the IR needs. The record, the hash and
  the `Show` instance are identical to Koka's. Koka's `Eq` and `Ord` ignore case; here,
  names that differ only in case are distinct (Lean has such names), ordered by their exact
  spelling. Koka never has two such names, so converting a name field by field preserves
  equality and the iteration order of `Map Name`.
-}
module Lidar.Name
  ( Name(..)
  , newName, newModuleName, newQualified, newLocallyQualified
  , readQualifiedName
  , qualify, unqualify, unqualifyFull, qualifier, isQualified, nameLocal
  , newHiddenName, makeHiddenName
  ) where

import Data.Char( toLower, isAlpha, isAlphaNum, isDigit )
import Prettyprinter( Pretty(pretty) )

-- | A name, as in Koka. The hashes of the three parts speed up comparisons:
-- `h1 > h2` implies `name1 > name2`. Hashes are case-insensitive; comparisons ignore case
-- unless two names differ only in case.
data Name = Name
  { nameModule    :: !String   -- module name (`std/core`)
  , hashModule    :: !Int
  , nameLocalQual :: !String   -- local qualifier (`int`)
  , hashLocalQual :: !Int
  , nameStem      :: !String   -- the stem (`show`)
  , hashStem      :: !Int
  }

instance Eq Name where
  nm1@(Name _ hm1 _ hl1 _ hn1) == nm2@(Name _ hm2 _ hl2 _ hn2)
    = hn1 == hn2 && hl1 == hl2 && hm1 == hm2 && sameSpelling nm1 nm2

-- compare module, stem name, and then local name for dependencies
instance Ord Name where
  compare nm1@(Name _ hm1 _ hl1 _ hn1) nm2@(Name _ hm2 _ hl2 _ hn2)
    = case compare hm1 hm2 of
        EQ -> case compare hn1 hn2 of
                EQ -> case compare hl1 hl2 of
                        EQ -> lowerCompare nm1 nm2 <> exactCompare nm1 nm2
                        lg -> lg
                lg -> lg
        lg -> lg

instance Show Name where
  show (Name m _ l _ n _)
    = let ln = join l (wrapId n)
      in if null m then ln
                   else if null ln then m
                                   else m ++ (if null l then "/" else "/#") ++ ln

instance Pretty Name where
  pretty name = pretty (show name)

lowerCompare :: Name -> Name -> Ordering
lowerCompare (Name m1 _ l1 _ n1 _) (Name m2 _ l2 _ n2 _)
  = case lowerCompareS m1 m2 of
      EQ -> case lowerCompareS l1 l2 of
              EQ -> lowerCompareS n1 n2
              lg -> lg
      lg -> lg

-- names that differ only in case, by their exact spelling
exactCompare :: Name -> Name -> Ordering
exactCompare (Name m1 _ l1 _ n1 _) (Name m2 _ l2 _ n2 _) = compare (m1,l1,n1) (m2,l2,n2)

sameSpelling :: Name -> Name -> Bool
sameSpelling (Name m1 _ l1 _ n1 _) (Name m2 _ l2 _ n2 _) = n1 == n2 && l1 == l2 && m1 == m2

lowerCompareS :: String -> String -> Ordering
lowerCompareS (c:cs) (d:ds)
  | c == d    = lowerCompareS cs ds
  | otherwise = case compare (toLower c) (toLower d) of
                  EQ -> lowerCompareS cs ds
                  lg -> lg
lowerCompareS (_:_) [] = GT
lowerCompareS [] (_:_) = LT
lowerCompareS [] []    = EQ

-- The hash takes the first 4 characters, assumes 32 bit integers and
-- no characters >= \x128, and is case-insensitive.
hash :: String -> Int
hash s = foldl (\h c -> h*256 + fromEnum c) 0 (map toLower (take 4 (s ++ "\0\0\0\0")))

join :: String -> String -> String
join m n = if null m then n else if null n then m else m ++ "/" ++ n

isIdChar, isIdStartChar, isIdEndChar :: Char -> Bool
isIdChar c      = isAlphaNum c || c == '_' || c == '@' || c == '-'
isIdStartChar c = isAlpha c || c == '_' || c == '@'
isIdEndChar c   = c /= '-' && (isIdChar c || c == '\'')

isSymbolId :: String -> Bool
isSymbolId ""      = False
isSymbolId s@(c:_) = not (isIdStartChar c) || not (isIdEndChar (last s))

wrapId :: String -> String
wrapId s = if isSymbolId s then "(" ++ s ++ ")" else s

----------------------------------------------------------------
-- Construction
----------------------------------------------------------------

newName :: String -> Name
newName s = newQualified "" s

newModuleName :: String -> Name
newModuleName s = newQualified s ""

newQualified :: String -> String -> Name
newQualified m n = newLocallyQualified m "" n

newLocallyQualified :: String -> String -> String -> Name
newLocallyQualified m l n = Name m (hash m) l (hash l) n (hash n)

nameMapStem :: Name -> (String -> String) -> Name
nameMapStem (Name m hm l hl n _) f
  = let fn = f n in Name m hm l hl fn (hash fn)

-- | Read a name as `show` prints it.
readQualifiedName :: String -> Name
readQualifiedName ('?':s)
  = toImplicitParamName (requalifyLocally (readQualifiedName s))
readQualifiedName s
  = let (qual,lqual,ident) = splitName
    in newLocallyQualified qual lqual ident
  where
    splitName :: (String,String,String)
    splitName
      = case reverse s of
          (')':rs1) -> -- operator
                      let (rop,rest) = span (/='(') rs1
                      in case rest of
                           ('(':rs2) -> let (qual,lqual,ident) = splitIdNameRev rs2
                                        in (qual,lqual,ident ++ reverse rop)
                           _ -> error ("Lidar.Name.readQualifiedName: unmatched parenthesis in name: " ++ s)
          rs -> splitIdNameRev rs

    splitIdNameRev :: String -> (String,String,String)
    splitIdNameRev rs
      = let (rid,rest) = span (/='#') rs
        in case rest of
             ('#':'/':rs2) -> -- local qualifier
                              let (lqual,ident) = splitQualIdRev rid
                              in (reverse rs2, lqual, ident)
             [] -> let (qual,ident) = splitQualIdRev rid
                   in (qual,"",ident)
             _  -> error ("Lidar.Name.readQualifiedName: illegal locally qualified name: " ++ s)

    splitQualIdRev :: String -> (String,String)
    splitQualIdRev rs
      = let (rid,rqual) = span (/='/') rs
        in case rqual of
             ('/':rs1) -> (reverse rs1, reverse rid)
             _         -> ("",reverse rid)

toImplicitParamName :: Name -> Name
toImplicitParamName name = qualifyLocally (newModuleName "@implicit") name

----------------------------------------------------------------
-- Qualification
----------------------------------------------------------------

qualify :: Name -> Name -> Name
qualify (Name m hm _ 0 _ 0) (Name _ 0 l hl n hn) = Name m hm l hl n hn
qualify (Name m1 _ _ 0 _ 0) name@(Name m2 _ _ _ _ _) | m1 == m2 = name
qualify n1 n2
  = error ("Lidar.Name.qualify: illegal qualification: " ++ show (n1,n2))

unqualify :: Name -> Name
unqualify (Name _ _ l hl n hn) = Name "" 0 l hl n hn

-- | Only keep the stem.
unqualifyFull :: Name -> Name
unqualifyFull (Name _ _ _ _ n hn) = Name "" 0 "" 0 n hn

qualifier :: Name -> Name
qualifier (Name m hm _ _ _ _) = Name m hm "" 0 "" 0

isQualified :: Name -> Bool
isQualified name = not (null (nameModule name))

qualifyLocally :: Name -> Name -> Name
qualifyLocally (Name loc _ _ 0 _ 0) (Name m _ l _ n _)
  = newLocallyQualified m (join loc l) n
qualifyLocally name1 name2
  = error ("Lidar.Name.qualifyLocally: illegal qualification: " ++ show (name1,name2))

-- | Move the module qualifier to the local qualifier.
requalifyLocally :: Name -> Name
requalifyLocally name@(Name m _ l _ n _)
  = if null m then name else newLocallyQualified "" (join m l) n

-- | The local qualifier and the stem (`int/show`).
nameLocal :: Name -> String
nameLocal (Name _ _ l _ n _) = join l n

----------------------------------------------------------------
-- Hidden names
----------------------------------------------------------------

newHiddenName :: String -> Name
newHiddenName base = prepend "@" (newName base)

makeHiddenName :: String -> Name -> Name
makeHiddenName s name = prepend ("@" ++ s ++ "-") name

-- prepend a string to the stem of a name
prepend :: String -> Name -> Name
prepend "" name = name
prepend pre name
  = nameMapStem name $ \stem ->
    let unhide s = case s of
                     '@':t -> t
                     _     -> s
    in case pre of
         '@':c:cs | isDigit c -> dashAppend ("@x" ++ (c:cs)) (unhide stem)  -- make sure it stays lowercase
         '@':_    -> dashAppend pre (unhide stem)                           -- no need for duplicate '@'s
         _        -> case stem of
                       '@':_ -> '@' : dashAppend pre (unhide stem)          -- keep hidden
                       _     -> dashAppend pre stem

-- append two identifier strings making sure dashes are correct.
dashAppend :: String -> String -> String
dashAppend s1 s2
  = let pre = case s1 of
                ('-':_) -> "x" ++ s1
                _       -> s1
    in case (reverse pre, s2) of
         ('-':_, c:_) | not (isAlpha c || c=='@') -> pre ++ "x" ++ s2
         _                                        -> pre ++ s2
