------------------------------------------------------------------------------
-- Copyright 2026, Anton Lorenzen
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-|
The dumps that Lean's @leanir@ writes for a module selected by @LEAN_TYPED_MODULES@
(@TypedDump@ in @src/LeanIR.lean@ of the lean4 branch @lidar@): the module's mono declarations
as @saveMono@ left them, the inductive types they mention with their constructor layouts, and
the C names, signatures and @\@[extern]@ entries of the constants they use.

A dump is a sequence of s-expressions. 'readDump' parses it into the AST below and 'showDump'
prints it back in the same format.
-}
module Lidar.Lean.Dump
  ( Dump(..), Name, Var
  , Type(..), Param(..), Lit(..), Arg(..), LetValue(..), Code(..), FunDecl(..), Alt(..)
  , ModInit(..), Link(..), Init(..), ExternEntry(..), Decl(..), DeclValue(..)
  , CtorRef(..), Const(..), ConstMono(..), Inductive(..), Ctor(..), Layout(..), Field(..), Main(..)
  , readDump, showDump
  , SExp(..), parseSExps, showSExp
  ) where

import Data.Char( isDigit, isHexDigit, isSpace, chr, ord )
import Numeric( readHex, showHex )
import Text.Parsec hiding ( label )
import Text.Parsec.String( Parser )

------------------------------------------------------------------------------
-- AST
------------------------------------------------------------------------------

-- | A Lean name as Lean prints it (with @«»@ escapes).
type Name = String

-- | A local variable (an @FVarId@).
type Var = String

data Dump = Dump
  { dumpModule     :: Name
  , dumpIsModule   :: Bool
  , dumpImports    :: [Name]
  , dumpInits      :: [ModInit]     -- ^ the module's initializers
  , dumpDecls      :: [Decl]        -- ^ the module's mono declarations, in the order of declaration
  , dumpCtors      :: [CtorRef]     -- ^ constructors used by the declarations
  , dumpConsts     :: [Const]       -- ^ other constants used by the declarations
  , dumpInductives :: [Inductive]   -- ^ inductive types mentioned, closed under constructor fields
  , dumpMain       :: Maybe Main
  } deriving (Eq, Show)

-- | Mono types: constants (@lcAny@, @lcErased@, type names), applications and arrows.
data Type
  = TConst Name
  | TApp Type [Type]
  | TArrow Type Type
  | TBVar Integer
  | TFVar Var
  | TSort
  | TOther String
  deriving (Eq, Show)

data Param = Param { paramVar :: Var, paramName :: Name, paramType :: Type, paramBorrow :: Bool }
  deriving (Eq, Show)

data Lit = LNat Integer | LStr String | LU8 Integer | LU16 Integer | LU32 Integer | LU64 Integer
         | LUSize Integer
  deriving (Eq, Show)

data Arg = AErased | AVar Var | AType Type
  deriving (Eq, Show)

data LetValue
  = VLit Lit
  | VErased
  | VProj Name Integer Var      -- ^ type, field index, structure
  | VConst Name [Arg]
  | VFVar Var [Arg]
  | VUnsupported
  deriving (Eq, Show)

data Code
  = Let Var Name Type LetValue Code
  | Fun FunDecl Code
  | Jp FunDecl Code
  | Jmp Var [Arg]
  | Cases Name Type Var [Alt]     -- ^ type, result type, discriminant, alternatives
  | Return Var
  | Unreach Type
  | Unsupported
  deriving (Eq, Show)

data FunDecl = FunDecl { funVar :: Var, funName :: Name, funParams :: [Param], funType :: Type, funBody :: Code }
  deriving (Eq, Show)

data Alt = Alt Name [Param] Code | Default Code | AltUnsupported
  deriving (Eq, Show)

-- | A module initializer as Lean's @emitInitFn@ writes it: its phase (@runtime@, @comptime@,
-- @all@, or @legacy@ for the initializer of all phases of a module of the module system), its C
-- name, the runtime initializer it calls first (or @""@) and the initializers of the imports.
data ModInit = ModInit { initPhase :: String, initName :: String, initLean :: String, initImports :: [String] }
  deriving (Eq, Show)

-- | How a constant is linked: its C name, @\@[export]@ name, the C name of its @_boxed@ version (for
-- the module's declarations), impure signature (parameters with impure types and borrow flags,
-- and the impure result type) and @\@[extern]@ entries.
data Link = Link
  { linkCName  :: String
  , linkExport :: Maybe String
  , linkBoxed  :: Maybe String
  , linkImpure :: Maybe ([Param], Type)
  , linkExtern :: Maybe [ExternEntry]
  } deriving (Eq, Show)

data Init = InitFn Name | BuiltinInitFn Name | IOUnitInit | IOUnitBuiltinInit
  deriving (Eq, Show)

data ExternEntry = Adhoc Name | Inline Name String | Standard Name String | Opaque
  deriving (Eq, Show)

data Decl = Decl
  { declName      :: Name
  , declLink      :: Link
  , declInit      :: [Init]
  , declSafe      :: Bool
  , declRecursive :: Bool
  , declParams    :: [Param]
  , declType      :: Type
  , declValue     :: DeclValue
  } deriving (Eq, Show)

data DeclValue = Body Code | Extern [ExternEntry]
  deriving (Eq, Show)

-- | A constructor: name, inductive type, constructor index.
data CtorRef = CtorRef Name Name Integer
  deriving (Eq, Show)

data Const = Const { constName :: Name, constLink :: Link, constMono :: Maybe ConstMono }
  deriving (Eq, Show)

-- | A constant's mono signature, if it has a mono declaration, or else its mono type.
data ConstMono = MonoSig [Param] Type | MonoType Type
  deriving (Eq, Show)

data Inductive = Inductive
  { indName    :: Name
  , indImpure  :: Maybe Type                    -- ^ impure type of its values
  , indTrivial :: Maybe (Name, Integer, Integer, Maybe Integer)
    -- ^ trivial structure: constructor, parameters, field, and the parameter that is the
    -- field's type, if it is one
  , indCtors   :: [Ctor]
  } deriving (Eq, Show)

data Ctor = Ctor
  { ctorName      :: Name
  , ctorIndex     :: Integer
  , ctorNumParams :: Integer
  , ctorNumFields :: Integer
  , ctorType      :: Maybe Type
  , ctorLayout    :: Maybe Layout
  } deriving (Eq, Show)

-- | Lean's @CtorLayout@: object fields, @usize@ fields and scalar bytes, and each field's place.
data Layout = Layout { layoutSize :: Integer, layoutUSize :: Integer, layoutSSize :: Integer, layoutFields :: [Field] }
  deriving (Eq, Show)

data Field
  = FErased
  | FVoid
  | FObject Integer Type
  | FUSize Integer
  | FScalar Integer Integer Type      -- ^ size, offset, type
  | FSpilled Integer Integer Type     -- ^ depth, index, type
  deriving (Eq, Show)

-- | @main@: its number of parameters, and whether it returns an exit code.
data Main = Main Integer Bool
  deriving (Eq, Show)

------------------------------------------------------------------------------
-- S-expressions
------------------------------------------------------------------------------

data SExp = SInt Integer | SStr String | SSym String | SList [SExp]
  deriving (Eq, Show)

parseSExps :: FilePath -> String -> Either String [SExp]
parseSExps file src = either (Left . show) Right (parse (ws *> many (sexp <* ws) <* eof) file src)
  where
    ws = skipMany (satisfy isSpace)
    sexp :: Parser SExp
    sexp = (SList <$> between (char '(' *> ws) (char ')') (many (sexp <* ws)))
       <|> (SStr <$> str)
       <|> atom
    atom = do
      s <- many1 (satisfy (\c -> not (isSpace c) && c `notElem` "()\""))
      pure $ case s of
        '-':ds | not (null ds), all isDigit ds -> SInt (negate (read ds))
        _ | all isDigit s -> SInt (read s)
          | otherwise     -> SSym s
    str = between (char '"') (char '"') (many (noneOf "\"\\" <|> (char '\\' *> escape)))
    escape = char '"' <|> char '\\'
         <|> (char 'u' *> between (char '{') (char '}') (hex <$> many1 (satisfy isHexDigit)))
    hex ds = chr (fst (head (readHex ds)))

showSExp :: SExp -> String
showSExp e = go e ""
  where
    go (SInt n) = shows n
    go (SStr s) = showChar '"' . foldr (\c k -> esc c . k) id s . showChar '"'
    go (SSym s) = showString s
    go (SList xs) = showChar '(' . foldr (.) id (sep (map go xs)) . showChar ')'
    sep (x:xs) = x : map (showChar ' ' .) xs
    sep []     = []
    esc '"'  = showString "\\\""
    esc '\\' = showString "\\\\"
    esc c | ord c < 32 || ord c > 126 = showString "\\u{" . showHex (ord c) . showChar '}'
          | otherwise = showChar c

------------------------------------------------------------------------------
-- Reading
------------------------------------------------------------------------------

type R a = Either String a

bad :: String -> SExp -> R a
bad what e = Left ("expected " ++ what ++ ", got: " ++ take 200 (showSExp e))

readDump :: FilePath -> String -> R Dump
readDump file src = do
  es <- parseSExps file src
  foldl (\d e -> d >>= item e) (Right (Dump "" False [] [] [] [] [] [] Nothing)) es
    >>= \d -> pure d { dumpDecls = reverse (dumpDecls d), dumpCtors = reverse (dumpCtors d)
                     , dumpConsts = reverse (dumpConsts d), dumpInductives = reverse (dumpInductives d)
                     , dumpInits = reverse (dumpInits d) }
  where
    item e d = case e of
      SList [SSym "module", SStr m, SList [SSym "is-module", b]] -> do
        b' <- rBool b; pure d { dumpModule = m, dumpIsModule = b' }
      SList (SSym "imports" : ms) -> do ms' <- mapM rStr ms; pure d { dumpImports = ms' }
      SList [SSym "mod-init", SSym p, SStr n, SStr l, SList (SSym "imports" : is)] -> do
        is' <- mapM rStr is; pure d { dumpInits = ModInit p n l is' : dumpInits d }
      SList (SSym "decl" : _) -> do x <- rDecl e; pure d { dumpDecls = x : dumpDecls d }
      SList [SSym "ctor", SStr c, SStr t, SInt i] -> pure d { dumpCtors = CtorRef c t i : dumpCtors d }
      SList (SSym "const" : _) -> do x <- rConst e; pure d { dumpConsts = x : dumpConsts d }
      SList (SSym "inductive" : _) -> do x <- rInductive e; pure d { dumpInductives = x : dumpInductives d }
      SList [SSym "main", SInt n, b] -> do b' <- rBool b; pure d { dumpMain = Just (Main n b') }
      _ -> bad "a dump item" e

rBool :: SExp -> R Bool
rBool (SSym "true")  = pure True
rBool (SSym "false") = pure False
rBool e = bad "a boolean" e

rStr :: SExp -> R String
rStr (SStr s) = pure s
rStr e = bad "a string" e

rVar :: SExp -> R Var
rVar (SSym s) = pure s
rVar e = bad "a variable" e

rType :: SExp -> R Type
rType e = case e of
  SStr n -> pure (TConst n)
  SList (SSym "app" : f : as) -> TApp <$> rType f <*> mapM rType as
  SList [SSym "->", a, b] -> TArrow <$> rType a <*> rType b
  SList [SSym "bvar", SInt i] -> pure (TBVar i)
  SList [SSym "fvar", SSym x] -> pure (TFVar x)
  SSym "sort" -> pure TSort
  SList [SSym "other", SStr s] -> pure (TOther s)
  _ -> bad "a type" e

rParams :: SExp -> R [Param]
rParams (SList (SSym "params" : ps)) = mapM rParam ps
  where rParam (SList [SSym "param", SSym x, SStr n, t, b]) = Param x n <$> rType t <*> rBool b
        rParam e = bad "a parameter" e
rParams e = bad "parameters" e

rLit :: SExp -> R Lit
rLit e = case e of
  SList [SSym "nat", SInt n] -> pure (LNat n)
  SList [SSym "str", SStr s] -> pure (LStr s)
  SList [SSym "u8", SInt n] -> pure (LU8 n)
  SList [SSym "u16", SInt n] -> pure (LU16 n)
  SList [SSym "u32", SInt n] -> pure (LU32 n)
  SList [SSym "u64", SInt n] -> pure (LU64 n)
  SList [SSym "usize", SInt n] -> pure (LUSize n)
  _ -> bad "a literal" e

rArg :: SExp -> R Arg
rArg (SSym "erased") = pure AErased
rArg (SSym x) = pure (AVar x)
rArg (SList [SSym "type", t]) = AType <$> rType t
rArg e = bad "an argument" e

rLetValue :: SExp -> R LetValue
rLetValue e = case e of
  SList [SSym "lit", l] -> VLit <$> rLit l
  SSym "erased" -> pure VErased
  SList [SSym "proj", SStr t, SInt i, SSym x] -> pure (VProj t i x)
  SList (SSym "const" : SStr n : as) -> VConst n <$> mapM rArg as
  SList (SSym "fvar" : SSym x : as) -> VFVar x <$> mapM rArg as
  SList [SSym "unsupported"] -> pure VUnsupported
  _ -> bad "a let value" e

rCode :: SExp -> R Code
rCode e = case e of
  SList [SSym "let", SSym x, SStr n, t, v, k] -> Let x n <$> rType t <*> rLetValue v <*> rCode k
  SList [SSym "fun", x, n, ps, t, b, k] -> Fun <$> rFunDecl x n ps t b <*> rCode k
  SList [SSym "jp", x, n, ps, t, b, k] -> Jp <$> rFunDecl x n ps t b <*> rCode k
  SList (SSym "jmp" : SSym x : as) -> Jmp x <$> mapM rArg as
  SList (SSym "cases" : SStr n : t : SSym x : alts) -> Cases n <$> rType t <*> pure x <*> mapM rAlt alts
  SList [SSym "return", SSym x] -> pure (Return x)
  SList [SSym "unreach", t] -> Unreach <$> rType t
  SList [SSym "unsupported"] -> pure Unsupported
  _ -> bad "code" e
  where
    rFunDecl x n ps t b = FunDecl <$> rVar x <*> rStr n <*> rParams ps <*> rType t <*> rCode b
    rAlt a = case a of
      SList [SSym "alt", SStr c, ps, k] -> Alt c <$> rParams ps <*> rCode k
      SList [SSym "default", k] -> Default <$> rCode k
      SList [SSym "unsupported"] -> pure AltUnsupported
      _ -> bad "an alternative" a

rExtern :: [SExp] -> R [ExternEntry]
rExtern = mapM entry
  where entry e = case e of
          SList [SSym "adhoc", SStr b] -> pure (Adhoc b)
          SList [SSym "inline", SStr b, SStr p] -> pure (Inline b p)
          SList [SSym "standard", SStr b, SStr f] -> pure (Standard b f)
          SSym "opaque" -> pure Opaque
          _ -> bad "an extern entry" e

-- | The link and init attributes after a constant's name, and the items after them.
rAttrs :: [SExp] -> R (Link, [Init], [SExp])
rAttrs = go (Link "" Nothing Nothing Nothing Nothing) []
  where
    go l is es = case es of
      SList [SSym "cname", SStr c] : rest -> go l { linkCName = c } is rest
      SList [SSym "export", SStr c] : rest -> go l { linkExport = Just c } is rest
      SList [SSym "boxed-cname", SStr c] : rest -> go l { linkBoxed = Just c } is rest
      SList [SSym "impure", ps, t] : rest -> do
        ps' <- rParams ps; t' <- rType t; go l { linkImpure = Just (ps', t') } is rest
      SList (SSym "extern" : xs) : rest -> do
        xs' <- rExtern xs; go l { linkExtern = Just xs' } is rest
      SList [SSym "init-fn", SStr f] : rest -> go l (is ++ [InitFn f]) rest
      SList [SSym "builtin-init-fn", SStr f] : rest -> go l (is ++ [BuiltinInitFn f]) rest
      SSym "io-unit-init" : rest -> go l (is ++ [IOUnitInit]) rest
      SSym "io-unit-builtin-init" : rest -> go l (is ++ [IOUnitBuiltinInit]) rest
      _ -> pure (l, is, es)

rDecl :: SExp -> R Decl
rDecl e = case e of
  SList (SSym "decl" : SStr n : rest) -> do
    (l, is, rest') <- rAttrs rest
    case rest' of
      [SList [SSym "safe", s], SList [SSym "recursive", r], ps, t, v] ->
        Decl n l is <$> rBool s <*> rBool r <*> rParams ps <*> rType t <*> rValue v
      _ -> bad "a declaration" e
  _ -> bad "a declaration" e
  where
    rValue (SList [SSym "body", c]) = Body <$> rCode c
    rValue (SList (SSym "extern" : xs)) = Extern <$> rExtern xs
    rValue v = bad "a declaration value" v

rConst :: SExp -> R Const
rConst e = case e of
  SList (SSym "const" : SStr n : rest) -> do
    (l, is, rest') <- rAttrs rest
    if not (null is) then bad "a constant without init attributes" e else
      case rest' of
        [] -> pure (Const n l Nothing)
        [SList [SSym "mono", ps, t]] -> Const n l . Just <$> (MonoSig <$> rParams ps <*> rType t)
        [SList [SSym "mono-type", t]] -> Const n l . Just . MonoType <$> rType t
        _ -> bad "a constant" e
  _ -> bad "a constant" e

rInductive :: SExp -> R Inductive
rInductive e = case e of
  SList (SSym "inductive" : SStr n : SList [SSym "impure", it] : rest) -> do
    it' <- case it of SSym "unknown" -> pure Nothing
                      _ -> Just <$> rType it
    case rest of
      SList [SSym "trivial", SStr c, SInt p, SInt f] : cs -> Inductive n it' (Just (c, p, f, Nothing)) <$> mapM rCtor cs
      SList [SSym "trivial", SStr c, SInt p, SInt f, SList [SSym "param", SInt k]] : cs ->
        Inductive n it' (Just (c, p, f, Just k)) <$> mapM rCtor cs
      cs -> Inductive n it' Nothing <$> mapM rCtor cs
  _ -> bad "an inductive type" e
  where
    rCtor c = case c of
      SList (SSym "ctor" : SStr cn : SInt i : SInt np : SInt nf : rest) -> do
        (t, rest') <- case rest of
          SList [SSym "type", t] : r -> do t' <- rType t; pure (Just t', r)
          r -> pure (Nothing, r)
        l <- case rest' of
          [] -> pure Nothing
          [SList (SSym "layout" : SInt s : SInt u : SInt ss : fs)] -> Just . Layout s u ss <$> mapM rField fs
          _ -> bad "a constructor layout" c
        pure (Ctor cn i np nf t l)
      _ -> bad "a constructor" c
    rField f = case f of
      SSym "erased" -> pure FErased
      SSym "void" -> pure FVoid
      SList [SSym "object", SInt i, t] -> FObject i <$> rType t
      SList [SSym "usize", SInt i] -> pure (FUSize i)
      SList [SSym "scalar", SInt s, SInt o, t] -> FScalar s o <$> rType t
      SList [SSym "spilled", SInt d, SInt i, t] -> FSpilled d i <$> rType t
      _ -> bad "a field" f

------------------------------------------------------------------------------
-- Printing
------------------------------------------------------------------------------

-- | The dump in the format 'readDump' reads, one item per line.
showDump :: Dump -> String
showDump d = unlines (map showSExp items)
  where
    items = [ SList [SSym "module", SStr (dumpModule d), SList [SSym "is-module", sBool (dumpIsModule d)]]
            , SList (SSym "imports" : map SStr (dumpImports d)) ]
         ++ [ SList [SSym "mod-init", SSym p, SStr n, SStr l, SList (SSym "imports" : map SStr is)]
            | ModInit p n l is <- dumpInits d ]
         ++ map sDecl (dumpDecls d)
         ++ [ SList [SSym "ctor", SStr c, SStr t, SInt i] | CtorRef c t i <- dumpCtors d ]
         ++ map sConst (dumpConsts d)
         ++ map sInductive (dumpInductives d)
         ++ [ SList [SSym "main", SInt n, sBool b] | Just (Main n b) <- [dumpMain d] ]

sBool :: Bool -> SExp
sBool b = SSym (if b then "true" else "false")

sType :: Type -> SExp
sType t = case t of
  TConst n -> SStr n
  TApp f as -> SList (SSym "app" : sType f : map sType as)
  TArrow a b -> SList [SSym "->", sType a, sType b]
  TBVar i -> SList [SSym "bvar", SInt i]
  TFVar x -> SList [SSym "fvar", SSym x]
  TSort -> SSym "sort"
  TOther s -> SList [SSym "other", SStr s]

sParams :: [Param] -> SExp
sParams ps = SList (SSym "params" : [ SList [SSym "param", SSym x, SStr n, sType t, sBool b] | Param x n t b <- ps ])

sLit :: Lit -> SExp
sLit l = case l of
  LNat n -> SList [SSym "nat", SInt n]
  LStr s -> SList [SSym "str", SStr s]
  LU8 n -> SList [SSym "u8", SInt n]
  LU16 n -> SList [SSym "u16", SInt n]
  LU32 n -> SList [SSym "u32", SInt n]
  LU64 n -> SList [SSym "u64", SInt n]
  LUSize n -> SList [SSym "usize", SInt n]

sArg :: Arg -> SExp
sArg AErased = SSym "erased"
sArg (AVar x) = SSym x
sArg (AType t) = SList [SSym "type", sType t]

sLetValue :: LetValue -> SExp
sLetValue v = case v of
  VLit l -> SList [SSym "lit", sLit l]
  VErased -> SSym "erased"
  VProj t i x -> SList [SSym "proj", SStr t, SInt i, SSym x]
  VConst n as -> SList (SSym "const" : SStr n : map sArg as)
  VFVar x as -> SList (SSym "fvar" : SSym x : map sArg as)
  VUnsupported -> SList [SSym "unsupported"]

sCode :: Code -> SExp
sCode c = case c of
  Let x n t v k -> SList [SSym "let", SSym x, SStr n, sType t, sLetValue v, sCode k]
  Fun f k -> SList (SSym "fun" : sFunDecl f ++ [sCode k])
  Jp f k -> SList (SSym "jp" : sFunDecl f ++ [sCode k])
  Jmp x as -> SList (SSym "jmp" : SSym x : map sArg as)
  Cases n t x alts -> SList (SSym "cases" : SStr n : sType t : SSym x : map sAlt alts)
  Return x -> SList [SSym "return", SSym x]
  Unreach t -> SList [SSym "unreach", sType t]
  Unsupported -> SList [SSym "unsupported"]
  where
    sFunDecl (FunDecl x n ps t b) = [SSym x, SStr n, sParams ps, sType t, sCode b]
    sAlt (Alt n ps k) = SList [SSym "alt", SStr n, sParams ps, sCode k]
    sAlt (Default k) = SList [SSym "default", sCode k]
    sAlt AltUnsupported = SList [SSym "unsupported"]

sExtern :: [ExternEntry] -> SExp
sExtern es = SList (SSym "extern" : map entry es)
  where entry (Adhoc b) = SList [SSym "adhoc", SStr b]
        entry (Inline b p) = SList [SSym "inline", SStr b, SStr p]
        entry (Standard b f) = SList [SSym "standard", SStr b, SStr f]
        entry Opaque = SSym "opaque"

sAttrs :: Link -> [Init] -> [SExp]
sAttrs (Link c ex bx imp ext) is =
  [SList [SSym "cname", SStr c]]
  ++ [ SList [SSym "export", SStr x] | Just x <- [ex] ]
  ++ [ SList [SSym "boxed-cname", SStr x] | Just x <- [bx] ]
  ++ [ SList [SSym "impure", sParams ps, sType t] | Just (ps, t) <- [imp] ]
  ++ [ sExtern xs | Just xs <- [ext] ]
  ++ map sInit is
  where sInit (InitFn f) = SList [SSym "init-fn", SStr f]
        sInit (BuiltinInitFn f) = SList [SSym "builtin-init-fn", SStr f]
        sInit IOUnitInit = SSym "io-unit-init"
        sInit IOUnitBuiltinInit = SSym "io-unit-builtin-init"

sDecl :: Decl -> SExp
sDecl (Decl n l is s r ps t v) =
  SList (SSym "decl" : SStr n : sAttrs l is
         ++ [ SList [SSym "safe", sBool s], SList [SSym "recursive", sBool r], sParams ps, sType t
            , case v of Body c -> SList [SSym "body", sCode c]
                        Extern xs -> sExtern xs ])

sConst :: Const -> SExp
sConst (Const n l m) =
  SList (SSym "const" : SStr n : sAttrs l []
         ++ case m of Nothing -> []
                      Just (MonoSig ps t) -> [SList [SSym "mono", sParams ps, sType t]]
                      Just (MonoType t) -> [SList [SSym "mono-type", sType t]])

sInductive :: Inductive -> SExp
sInductive (Inductive n it tr cs) =
  SList (SSym "inductive" : SStr n : SList [SSym "impure", maybe (SSym "unknown") sType it]
         : [ SList ([SSym "trivial", SStr c, SInt p, SInt f] ++ [SList [SSym "param", SInt k] | Just k <- [pk]])
           | Just (c, p, f, pk) <- [tr] ]
         ++ map sCtor cs)
  where
    sCtor (Ctor cn i np nf t l) =
      SList ([SSym "ctor", SStr cn, SInt i, SInt np, SInt nf]
             ++ [ SList [SSym "type", sType ty] | Just ty <- [t] ]
             ++ [ SList (SSym "layout" : SInt s : SInt u : SInt ss : map sField fs) | Just (Layout s u ss fs) <- [l] ])
    sField f = case f of
      FErased -> SSym "erased"
      FVoid -> SSym "void"
      FObject i t -> SList [SSym "object", SInt i, sType t]
      FUSize i -> SList [SSym "usize", SInt i]
      FScalar s o t -> SList [SSym "scalar", SInt s, SInt o, sType t]
      FSpilled d i t -> SList [SSym "spilled", SInt d, SInt i, sType t]
