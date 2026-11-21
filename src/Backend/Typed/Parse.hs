-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Parsing the printed IR (`Pretty`) back.

  The parser reads a program as `prettyProgram` prints it. The type annotations of values and
  expressions that the printer omits are left unknown (`unknownA`, `unknownV`) for `Annotate`.
  Imported datatypes and signatures are not printed, so the caller passes them.

  The printer only breaks lines between the alternatives of case-like forms and before nested
  expressions. The alternatives of a form start lines at the same column, which ends the
  alternatives of a form nested in the last one.

  A definition is read in the order it is printed, and its binders are collected by how they
  print. The binder of a destructuring of a variable z is z with the step of the form: the form
  prints the tag or index of the step, and the last part of the binder the constructor or field
  that the step names. The other binders are roots. Every other path is the binder that prints
  the same (`Pretty` prints the binders of a definition differently), and a name that no binder
  prints is a global.
-}
module Backend.Typed.Parse( parseProgram, unknownA, unknownV ) where

import qualified Data.Map as M
import Data.Char( isAlpha, isAlphaNum, isDigit, isSpace )
import Data.List( intercalate, isSuffixOf, stripPrefix )
import Text.Parsec hiding ( label, labels )
import Text.Parsec.Pos( newPos )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Pretty( ppr, reserved )
import Backend.Typed.Traversal( child )
import Backend.Typed.Types( orNull )

-- the annotations that the printer omits, until `Annotate` fills them in
unknownA :: AType
unknownA = ACon (newHiddenName "unknown") []

unknownV :: VType
unknownV = VPtr unknownA

--------------------------------------------------------------------------
-- Tokens
--------------------------------------------------------------------------

-- a name (whether it is in backquotes) with the parts of a path after it, or another token
data Tok = TName Bool String [String]
         | TInt Integer
         | TFloat Double
         | TChar Char
         | TString String
         | TSym String
         deriving (Eq,Show)

-- a token, its position, and whether it starts its line
data Token = Token{ tokPos :: SourcePos, tokFirst :: Bool, tokTok :: Tok }

instance Show Token where
  show = show . tokTok

lexTokens :: String -> Either String [Token]
lexTokens = go 1 1 True
  where
    go :: Int -> Int -> Bool -> String -> Either String [Token]
    go line col first s
      = case s of
          [] -> Right []
          '\n':rest -> go (line+1) 1 True rest
          c:rest | isSpace c -> go line (col+1) first rest
          _ -> case lexToken s of
                 Just (t,n,rest) -> (Token (newPos "" line col) first t :) <$> go line (col+n) False rest
                 Nothing -> Left ("line " ++ show line ++ ", column " ++ show col ++ ": unexpected " ++ show (take 10 s))

-- a token, its length and the rest of the input
lexToken :: String -> Maybe (Tok,Int,String)
lexToken s
  = case s of
      '`':rest | (n,'`':rest') <- break (== '`') rest -> Just (withParts (TName True n) (length n + 2) rest')
      '-':'>':rest -> Just (TSym "->", 2, rest)
      '~':'>':rest -> Just (TSym "~>", 2, rest)
      '+':'+':rest -> Just (TSym "++", 2, rest)
      'b':'o':'x':'@':rest -> Just (TSym "box@", 4, rest)   -- names that start so are escaped
      '-':rest | Just rest' <- stripPrefix "Infinity" rest -> Just (TFloat (-1/0), 9, rest')
      '-':c:_ | isDigit c -> Just (lexNumber s)
      c:_ | isDigit c -> Just (lexNumber s)
      '\'':_ | [(ch,rest)] <- reads s -> Just (TChar ch, length (show ch), rest)
      '"':_ | [(str,rest)] <- reads s -> Just (TString str, length (show str), rest)
      c:_ | isNameStart c -> let (n,rest) = lexName s in Just (withParts (TName False n) (length n) rest)
      c:rest | c `elem` "()[]<>,;:=*+!^\\.?" -> Just (TSym [c], 1, rest)
      _ -> Nothing

-- the parts of a path after a name
withParts :: ([String] -> Tok) -> Int -> String -> (Tok,Int,String)
withParts mk n s = let (ps,m,rest) = parts s in (mk ps, n + m, rest)
  where
    parts r = case r of
                '.':c:_ | isNameStart c || isDigit c || c == '(' ->
                  let (p,r') = lexPart (tail r)
                      (ps,m,r'') = parts r'
                  in (p:ps, 1 + length p + m, r'')
                _ -> ([],0,r)
    lexPart r = case r of
                  '(':r1 | (op,')':r2) <- break (== ')') r1 -> ("(" ++ op ++ ")", r2)
                  _ -> lexName r

lexNumber :: String -> (Tok,Int,String)
lexNumber s = (if null frac && null ex then TInt (read txt) else TFloat (read txt), length txt, rest)
  where
    (sign,s1) = case s of
                  '-':r -> ("-",r)
                  _ -> ("",s)
    (ds,s2) = span isDigit s1
    (frac,s3) = case s2 of
                  '.':c:r | isDigit c -> let (f,r') = span isDigit (c:r) in ('.':f, r')
                  _ -> ("",s2)
    (ex,rest) = case s3 of
                  'e':r | (sg,r1) <- (case r of { '-':r' -> ("-",r'); _ -> ("",r) }), (es@(_:_),r2) <- span isDigit r1
                    -> ('e':sg ++ es, r2)
                  _ -> ("",s3)
    txt = sign ++ ds ++ frac ++ ex

isNameStart :: Char -> Bool
isNameStart c = isAlpha c || c == '_' || c == '@'

-- a name, with an operator after its qualifier in parentheses (`std/core/types/(++)`)
lexName :: String -> (String,String)
lexName s
  = case go s of
      (n,'(':r) | "/" `isSuffixOf` n, (op,')':r') <- break (== ')') r -> (n ++ "(" ++ op ++ ")", r')
      res -> res
  where
    go (c:cs) | isNameChar c && not (c == '-' && take 1 cs == ">") = let (n,r) = go cs in (c:n, r)
    go cs = ([],cs)
    isNameChar c = isAlphaNum c || c `elem` "_@'/#-"

--------------------------------------------------------------------------
-- Parsing tokens
--------------------------------------------------------------------------

-- a path as it prints: its root and the other parts
type RawPath = (String,[String])

-- the constructors by how they print, those of the module first, and the binders of the
-- current definition by how they print (`Nothing` if several print the same)
data PState = PState{ psCons :: M.Map String [Cons], psBinders :: M.Map RawPath (Maybe Path) }

-- a constructor, whether it is of a datatype of the module, and how its fields print
data Cons = Cons{ consName :: Name, consLocal :: Bool, consFields :: [String] }

-- (of a reference datatype, as `Pretty.fieldsOf`)
consOf :: Bool -> TypeDef -> M.Map String [Cons]
consOf isLocal d = case tdefBody d of
                     BodyRef _ -> M.fromListWith (flip (++)) [(show (Con c), [Cons c isLocal (map show fs)]) | ConLabel c fs _ <- tdefLabels d]
                     _ -> M.empty

type P a = Parsec [Token] PState a

satisfyTok :: (Token -> Maybe a) -> P a
satisfyTok = tokenPrim (show . tokTok) next
  where
    next pos _ ts = case ts of
                      t:_ -> tokPos t
                      [] -> pos

tokenP :: (Tok -> Maybe a) -> P a
tokenP f = satisfyTok (f . tokTok)

sym :: String -> P ()
sym s = tokenP (\t -> if t == TSym s then Just () else Nothing) <?> show s

kw :: String -> P ()
kw s = tokenP (\t -> case t of
                       TName False n [] | n == s -> Just ()
                       _ -> Nothing) <?> s

parensP, bracketsP, anglesP :: P a -> P a
parensP p = sym "(" *> p <* sym ")"
bracketsP p = sym "[" *> p <* sym "]"
anglesP p = sym "<" *> p <* sym ">"

commaSep :: P a -> P [a]
commaSep p = sepBy p (sym ",")

-- a name that is not a keyword
nameP :: P String
nameP = tokenP (\t -> case t of
                        TName True n [] -> Just n
                        TName False n [] | not (reserved n) -> Just n
                        _ -> Nothing) <?> "name"

pathP :: P RawPath
pathP = tokenP (\t -> case t of
                        TName e n ps | e || not (reserved n) -> Just (n,ps)
                        _ -> Nothing) <?> "path"

-- the label of a component of a type, which is not escaped
labelP :: P String
labelP = tokenP (\t -> case t of
                         TName _ n [] -> Just n
                         _ -> Nothing) <?> "label"

-- a keyword with a number (`inj1`, `reuse16`, `v3`)
numbered :: String -> P Int
numbered p = tokenP (\t -> case t of
                             TName False n [] | Just ds@(_:_) <- stripPrefix p n, all isDigit ds -> Just (read ds)
                             _ -> Nothing) <?> (p ++ "<n>")

intP :: P Int
intP = tokenP (\t -> case t of
                       TInt i -> Just (fromInteger i)
                       _ -> Nothing) <?> "number"

litP :: P Lit
litP = tokenP (\t -> case t of
                       TInt i -> Just (LitInt i)
                       TFloat d -> Just (LitFloat d)
                       TChar c -> Just (LitChar c)
                       TString s -> Just (LitString s)
                       TName False "NaN" [] -> Just (LitFloat (0/0))
                       TName False "Infinity" [] -> Just (LitFloat (1/0))
                       _ -> Nothing) <?> "literal"

modeP :: P Mode
modeP = option Owned ((Unique <$ sym "!") <|> (Borrowed <$ sym "^"))

-- the alternatives of a case-like form, which start lines at the same column
alternatives :: P a -> P [a]
alternatives p
  = do t <- lookAhead (satisfyTok Just)
       let col = sourceColumn (tokPos t)
           atColumn = do t' <- lookAhead (satisfyTok Just)
                         if tokFirst t' && sourceColumn (tokPos t') == col then return () else parserZero
       many1 (atColumn >> p)

--------------------------------------------------------------------------
-- Names and paths
--------------------------------------------------------------------------

-- Global names are qualified by their module.
globalName :: String -> Name
globalName = readQualifiedName

-- Local names have no module, but may have a local qualifier (`@implicit/(==)`), which prints
-- like a module.
localName :: String -> Name
localName s = let n = readQualifiedName s
              in if null (nameLocalQual n) then newLocallyQualified "" (nameModule n) (nameStem n) else n

-- The constructor that prints so: one of a datatype of the module if there is one. Where
-- several remain, any one will do if their fields print the same (as for the indirections of
-- lazy datatypes), as constructors compare by tag.
conName :: M.Map String [Cons] -> String -> Name
conName cons c
  = case filter consLocal candidates of
      [] -> pick candidates
      locals -> pick locals
  where
    candidates = M.findWithDefault [] c cons
    pick ks = case ks of
                k:rest | all ((== consFields k) . consFields) rest -> consName k
                _ -> labelName c

-- the name of a constructor or field as it prints, which may be an operator in parentheses
labelName :: String -> Name
labelName = readQualifiedName

showRaw :: RawPath -> String
showRaw (r,ps) = intercalate "." (r:ps)

bind :: RawPath -> Path -> P Path
bind raw x = do modifyState (\st -> st{ psBinders = M.insertWith same raw (Just x) (psBinders st) })
                return x
  where
    same new old = if new == old then old else Nothing

rootBinder :: RawPath -> P Path
rootBinder raw@(r,ps)
  | null ps = bind raw (root (localName r))
  | otherwise = fail ("a binder with steps where a root is expected: " ++ showRaw raw)

-- the binder of a destructuring of a value: a root, or a child of a variable with the step for
-- the last part of the binder
childBinder :: VVal -> (String -> Step) -> RawPath -> P Path
childBinder v step raw@(_,ps)
  = case (v,ps) of
      (_,[]) -> rootBinder raw
      (Var z,_) -> bind raw (child z (step (last ps)))
      _ -> fail ("a binder with steps of a value that is not a variable: " ++ showRaw raw)

data Use = Local Path | Global Name

useP :: RawPath -> P Use
useP raw@(r,ps)
  = do binders <- psBinders <$> getState
       case M.lookup raw binders of
         Just (Just x) -> return (Local x)
         Just Nothing -> fail ("ambiguous path " ++ showRaw raw)
         Nothing | null ps -> return (Global (globalName r))
                 | otherwise -> fail ("unknown path " ++ showRaw raw)

localP :: P Path
localP = do raw <- pathP
            u <- useP raw
            case u of
              Local x -> return x
              Global _ -> fail ("unbound variable " ++ showRaw raw)

valueOf :: RawPath -> P VVal
valueOf raw = do u <- useP raw
                 return (case u of
                           Local x -> Var x
                           Global n -> Glob n [])

--------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------

tvarP :: P TVar
tvarP = numbered "v"

tyParamsP :: P [TVar]
tyParamsP = option [] (anglesP (sepBy1 tvarP (sym ",")))

tyArgsP :: P [AType]
tyArgsP = bracketsP (commaSep aP)

aP :: P AType
aP = tyP >>= asA

vP :: P VType
vP = tyP >>= asV

asA :: Ty -> P AType
asA t = case t of
          A a -> return a
          V v -> fail ("expecting a boxed type instead of " ++ ppr v)

asV :: Ty -> P VType
asV t = case t of
          V v -> return v
          A a -> fail ("expecting an unboxed type instead of " ++ ppr a)

-- Boxed and unboxed types share parts of their syntax, so they are parsed together.
tyP :: P Ty
tyP = choice
        [ do kw "forall"; vs <- many1 tvarP; sym "."; A . AForall vs <$> aP
        , do t <- baseTyP
             t' <- (sym "*" >> (V . VPtr <$> asA t)) <|> return t
             nullable t' ]
  where
    nullable t = (sym "?" >> (asV t >>= nullable . V . orNull)) <|> return t

baseTyP :: P Ty
baseTyP
  = choice
      [ kw "Box" >> (A . ABox <$> parensP vP)
      , kw "Scalar" >> (A . AScalar <$> parensP rawP)
      , A AUnit <$ tokenP (\t -> if t == TInt 1 then Just () else Nothing)
      , V VUnit <$ kw "I"
      , V VToken <$ kw "KCtx"
      , V . VRaw <$> rawP
      , do (f,n) <- (do kw "reuse"; sym "!"; n <- intP; return (Full,n)) <|> ((,) MaybeEmpty <$> numbered "reuse")
           V . VReuse f n <$> optionMaybe contentsP
      , do kw "ctx"; f <- option MaybeEmpty (Full <$ sym "+"); sym "<"; a <- aP; sym ","; b <- aP; sym ">"; return (V (VCtx f a b))
      , do n <- numbered "cell"; V . VCell n <$> anglesP aP
      , do v <- tvarP; mts <- optionMaybe (anglesP (commaSep aP)); return (A (maybe (AVar v) (AApp v) mts))
      , do n <- nameP; ts <- option [] (anglesP (commaSep aP)); return (A (ACon (globalName n) ts))
      , sym "(" >> parenTyP ]

rawP :: P Raw
rawP = tokenP (\t -> case t of
                       TName False n [] -> lookup n raws
                       _ -> Nothing) <?> "raw type"
  where
    raws = [("char",RChar),("ssize_t",RSSize),("intptr_t",RIntPtr),("float64",RFloat64),("float32",RFloat32)
           ,("int64",RInt64),("int32",RInt32),("int16",RInt16),("int8",RInt8),("uint8",RUInt8)]

contentsP :: P Contents
contentsP = bracketsP (do k <- (Nothing <$ kw "_") <|> (Just <$> intP)
                          sym ";"
                          v <- valP
                          sym ":"
                          Contents k v <$> vP)

-- after an opening parenthesis: an existential, a type function, a sum, a lazy sum, the
-- parameters of a function, a sum or product of unboxed types, or a type in parentheses
parenTyP :: P Ty
parenTyP
  = choice
      [ do kw "exists"; vs <- many1 tvarP; sym "."; b <- vP; sym ")"; return (V (VExists vs b))
      , do sym "\\"; vs <- many1 tvarP; sym "."; b <- aP; sym ")"; return (A (ALam vs b))
      , sym ")" >> funTail []
      , do ts <- sepBy1 sumAlt (sym "+"); sym ")"; return (A (ASum ts))
      , do m <- modeP; l <- optionMaybe (try (labelP <* sym ":")); t <- tyP; components m l t ]
  where
    sumAlt = do i <- try (intP <* sym ":"); t <- aP; return (i,t)
    component = do l <- optionMaybe (try (labelP <* sym ":")); t <- tyP; return (l,t)
    components m l t
      = choice
          [ do op <- opP
               rest <- (sym ")" >> return []) <|> (do c <- component; cs <- many (opP >> component); sym ")"; return (c:cs))
               ts <- mapM (\(l',s) -> (,) l' <$> asV s) ((l,t) : rest)
               return (V (if op == "+" then VSum [(maybe (tagCon i) (Con . labelName) l', s) | (i,(l',s)) <- zip [0..] ts]
                                       else VProd [(maybe (posField i) (Field . labelName) l', s) | (i,(l',s)) <- zip [0..] ts]))
          , do sym "~>"; s <- aP; sym ")"; a <- asA t; return (A (ALazy a s))
          , do sym ","; ps <- sepBy1 ((,) <$> modeP <*> tyP) (sym ","); sym ")"; funTail ((m,t) : ps)
          , sym ")" >> (funTail [(m,t)] <|> (A <$> asA t)) ]
    opP = try (do sym "("; op <- ("+" <$ sym "+") <|> ("x" <$ kw "x"); sym ")"; return op)
    funTail ps = do sym "->"
                    r <- vP
                    ps' <- mapM (\(m,t) -> (,) m <$> asV t) ps
                    return (A (AFun ps' r))

--------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------

valP :: P VVal
valP
  = choice
      [ do i <- numbered "inj"; Inj i unknownV <$> atomValP
      , kw "ptr" >> (Ptr unknownA <$> atomAValP)
      , kw "pack" >> (do ts <- tyArgsP; Pack unknownV ts <$> atomValP)
      , kw "up" >> (Up <$> atomValP)
      , kw "down" >> (do b <- bracketsP aP; Down b <$> atomValP)
      , kw "dup" >> (DupV <$> atomValP)
      , kw "ctx" >> (Context unknownA <$> atomValP)
      , kw "some" >> (Some <$> atomValP)
      , atomValP ]

atomValP :: P VVal
atomValP = baseValP >>= tyApps
  where
    tyApps v = (do ts <- try tyArgsP; tyApps (TyApp v ts)) <|> return v

-- a value without type applications after it
baseValP :: P VVal
baseValP
  = choice
      [ Lit <$> litP
      , Hole <$ kw "hole"
      , Null unknownV <$ kw "null"
      , do n <- numbered "no-reuse"; NoReuse n <$> optionMaybe contentsP
      , do raw <- pathP
           u <- useP raw
           case u of
             Local x -> return (Var x)
             Global n -> Glob n <$> option [] (try tyArgsP)
      , sym "(" >> ((UnitV <$ sym ")")
                    <|> (do v <- valP
                            (v <$ sym ")") <|> (do sym ","; vs <- commaSep valP; sym ")"; return (Tuple (v:vs))))) ]

argsP :: P [VVal]
argsP = parensP (commaSep valP)

atomAValP :: P AVal
atomAValP = (Fun . globalName <$> nameP) <|> (sym "(" >> ((UnitA <$ sym ")") <|> (aValP <* sym ")")))

aValP :: P AVal
aValP
  = choice
      [ do i <- numbered "inj-a"; InjA i unknownA <$> atomAValP
      , kw "roll" >> (Roll unknownA <$> atomAValP)
      , kw "whnf" >> (InjLazy Whnf unknownA <$> atomAValP)
      , kw "delay" >> (InjLazy Delay unknownA <$> atomAValP)
      , kw "box" >> (Box <$> atomValP)
      , kw "scalar" >> (Scalar <$> atomValP)
      , kw "fn" >> (do ps <- paramsP; sym ":"; r <- vP; sym "->"; Lam ps r <$> exprP)
      , sym "box@" >> (do r <- localP; BoxAt r <$> atomValP)
      , do c <- globalName <$> nameP
           (do ts <- tyArgsP; OpenCon c ts <$> argsP) <|> return (Fun c)
      , atomAValP ]

-- the parameters of a function, closure or join point, which are roots
paramsP :: P [(Path,Mode,VType)]
paramsP = parensP (commaSep (do m <- modeP; raw <- pathP; sym ":"; t <- vP; x <- rootBinder raw; return (x,m,t)))

--------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------

exprP :: P VExpr
exprP
  = choice
      [ kw "ret" >> (Ret <$> atomValP)
      , kw "let" >> letP
      , kw "case" >> caseP
      , kw "split" >> splitP
      , kw "if-whnf" >> ifWhnfP
      , kw "is-null" >> isNullP
      , kw "if-yielding" >> ifYieldingP
      , kw "dup" >> (Dup <$> localP <* sym ";" <*> exprP)
      , kw "drop" >> (Drop <$> localP <* sym ";" <*> exprP)
      , kw "free" >> (Free <$> localP <* sym ";" <*> exprP)
      , kw "if-unique" >> (IsUnique <$> localP <*> (kw "then" >> exprP) <*> (kw "else" >> exprP))
      , kw "if-full" >> (IfFull <$> localP <*> (kw "then" >> exprP) <*> (kw "else" >> exprP))
      , kw "join" >> joinP
      , kw "jump" >> (Jump <$> (localName <$> nameP) <*> option [] tyArgsP <*> argsP)
      , Unreachable unknownV <$ kw "unreachable"
      , kw "ctx-copy" >> (CtxCopy <$> atomValP)
      , kw "cast-ev" >> (do (u,t) <- bracketsP ((,) <$> vP <* sym "," <*> vP); CastEv u t <$> exprP)
      , kw "memoize" >> memoizeP
      , kw "gen" >> (do vs <- many1 tvarP; sym "."; Gen vs <$> exprP)
      , kw "total" >> (do k <- pathP >>= rootBinder; sym "."; Total k <$> exprP)
      , headP ]

-- calls, applications, and plugging and appending contexts
headP :: P VExpr
headP
  = (do raw <- pathP
        choice [ do vs <- argsP
                    u <- useP raw
                    return (case u of
                              Local f -> App f vs
                              Global f -> Call f [] vs)
               , do ts <- try (tyArgsP <* lookAhead (sym "("))
                    Call (globalName (fst raw)) ts <$> argsP
               , valueOf raw >>= contextOp ])
    <|> (baseValP >>= contextOp)
  where
    contextOp c = (Plug c <$> bracketsP valP) <|> (sym "++" >> (Append c <$> atomValP))

letP :: P VExpr
letP
  = choice
      [ do m <- (Unique <$ sym "!") <|> (Borrowed <$ sym "^"); kw "scalar"; unscalar m
      , kw "scalar" >> unscalar Owned
      , kw "ptr" >> (do raw <- pathP; sym "="; v <- valP; kw "in"; x <- childBinder v (const SDeref) raw; Deref v x <$> exprP)
      , kw "roll" >> destruct Unroll SRoll
      , kw "box" >> destruct Unbox SContents
      , kw "pack" >> (do vs <- bracketsP (commaSep tvarP); raw <- pathP; sym "="; v <- valP; kw "in"
                         x <- childBinder v (const SPack) raw
                         Unpack v vs x <$> exprP)
      , kw "@" >> (do (raw,z) <- takeBlock; _ <- bind raw (child z SCredit); UnboxRu z <$> exprP)
      , kw "@copy" >> (do (raw,z) <- takeBlock; r <- rootBinder raw; CopyRu z r <$> exprP)
      , kw "lock" >> (do (raw,z) <- takeBlock; _ <- bind raw (child z SCredit); Lock z <$> exprP)
      , do raw <- pathP
           (sym ":" >> typed raw) <|> (sym "=" >> proj raw) ]
  where
    unscalar m = do raw <- pathP; sym "="; z <- localP; kw "in"; x <- rootBinder raw; Unscalar m z x <$> exprP
    destruct form step = do raw <- pathP; sym "="; z <- localP; kw "in"; x <- childBinder (Var z) (const step) raw; form z x <$> exprP
    takeBlock = do raw <- pathP; sym "="; z <- localP; kw "in"; return (raw,z)
    typed raw = do t <- vP
                   sym "="
                   x <- rootBinder raw
                   e1 <- exprP
                   kw "in"
                   Let x t e1 <$> exprP
    proj raw = do (v,i) <- projected
                  kw "in"
                  x <- childBinder v (\f -> SField i (Field (labelName f))) raw
                  Proj v i x <$> exprP
    -- a path with the index of a field as its last part, or a value with an index after it
    projected = (do (r,ps) <- try indexed; v <- valueOf (r, init ps); return (v, read (last ps)))
                <|> (do v <- atomValP; sym "."; i <- intP; return (v,i))
    indexed = do raw@(_,ps) <- pathP
                 if not (null ps) && all isDigit (last ps) then return raw else parserZero

-- the alternatives of the forms printed as `case`
data Alt = AltV Int Path VExpr
         | AltA Int Path VExpr
         | AltRest (Maybe Path) VExpr
         | AltLit Lit VExpr
         | AltOpen Name [Path] VExpr

caseP :: P VExpr
caseP = do v <- valP
           kw "of"
           cons <- psCons <$> getState
           as <- alternatives (altP cons v)
           caseOf v as

altP :: M.Map String [Cons] -> VVal -> P Alt
altP cons v
  = choice
      [ do i <- numbered "inj-a"; raw <- pathP; sym "->"
           x <- childBinder v (\c -> SInjA i (Con (conName cons c))) raw
           AltA i x <$> exprP
      , do i <- numbered "inj"; raw <- pathP; sym "->"
           x <- childBinder v (\c -> SInjV i (Con (labelName c))) raw
           AltV i x <$> exprP
      , do kw "_"
           (sym "->" >> (AltRest Nothing <$> exprP))
             <|> (do raw <- pathP; sym "->"; x <- childBinder v (const SRest) raw; AltRest (Just x) <$> exprP)
      , do l <- litP; sym "->"; AltLit l <$> exprP
      , do c <- globalName <$> nameP
           raws <- parensP (commaSep pathP)
           sym "->"
           xs <- openBinders c raws
           AltOpen c xs <$> exprP ]
  where
    -- the fields of the product `v.C`, or `v.C` itself if there is one (`Traversal.openSteps`)
    openBinders c raws
      = case raws of
          [raw] -> sequence [childBinder v (const (SOpen c)) raw]
          _ -> sequence [case (v,ps) of
                           (Var z,_:_) -> bind raw (child (child z (SOpen c)) (SField i (Field (labelName (last ps)))))
                           _ -> rootBinder raw
                        | (i,raw@(_,ps)) <- zip [0..] raws]

caseOf :: VVal -> [Alt] -> P VExpr
caseOf v as
  | Just alts <- mapM altV as = return (CaseV v alts)
  | Just alts <- mapM altA as = scrut >>= \z -> return (CaseA z alts Nothing)
  | Just alts <- mapM altA (init as), AltRest (Just x) e <- last as = scrut >>= \z -> return (CaseA z alts (Just (x,e)))
  | Just alts <- mapM altLit (init as), AltRest Nothing e <- last as = return (CaseLit v alts e)
  | Just alts <- mapM altOpen (init as), AltRest Nothing e <- last as = scrut >>= \z -> return (CaseOpen z alts e)
  | otherwise = fail "inconsistent alternatives"
  where
    scrut = case v of
              Var z -> return z
              _ -> fail ("a case on a value that is not a variable: " ++ ppr v)
    altV a = case a of { AltV i x e -> Just (i,x,e); _ -> Nothing }
    altA a = case a of { AltA i x e -> Just (i,x,e); _ -> Nothing }
    altLit a = case a of { AltLit l e -> Just (l,e); _ -> Nothing }
    altOpen a = case a of { AltOpen c xs e -> Just (c,xs,e); _ -> Nothing }

-- a side of `split` or `if-whnf`
sideP :: Path -> Step -> P (Path,VExpr)
sideP z step = do raw <- pathP; sym "->"; x <- childBinder (Var z) (const step) raw; (,) x <$> exprP

splitP :: P VExpr
splitP = do z <- localP; kw "at"; k <- intP; kw "of"
            SplitA z k <$> sideP z SLo <*> sideP z SHi

isNullP :: P VExpr
isNullP = do v <- valP; kw "of"
             kw "null"; sym "->"; n <- exprP
             raw <- pathP; sym "->"; x <- childBinder v (const SSome) raw
             IsNull v n . (,) x <$> exprP

ifYieldingP :: P VExpr
ifYieldingP = do v <- valP; kw "of"
                 kw "yield"; k3 <- pathP >>= rootBinder; sym "->"; e3 <- exprP
                 k2 <- pathP >>= rootBinder; sym "->"; e2 <- exprP
                 return (IfYielding v (k3,e3) (k2,e2))

ifWhnfP :: P VExpr
ifWhnfP = do z <- localP; kw "of"
             IfWhnf z <$> (kw "whnf" >> sideP z SWhnf) <*> (kw "delay" >> sideP z SDelay)

joinP :: P VExpr
joinP = do r <- option False (True <$ kw "rec")
           j <- localName <$> nameP
           tvs <- tyParamsP
           ps <- paramsP
           rec <- if r then Rec <$> (sym ":" >> vP) else return NonRec
           sym "="
           e1 <- exprP
           kw "in"
           Join rec j tvs ps e1 <$> exprP

memoizeP :: P VExpr
memoizeP = do c <- atomValP
              sym "("
              d <- (Whnf <$ kw "whnf") <|> (Delay <$ kw "delay")
              sym "("
              k <- numbered "inj"
              v <- atomValP
              sym ")"
              sym ")"
              return (Memoize c d k v)

--------------------------------------------------------------------------
-- Programs
--------------------------------------------------------------------------

data Item = IType TypeDef | ISig Name Sig | IExtern Name Extern | IForeign String String | IDef Def

-- Parses a program, given the imported datatypes, signatures and externals. Its datatypes,
-- signatures and externals include them.
parseProgram :: TypeDefs -> Sigs -> Externs -> String -> Either String Program
parseProgram types sigs externs src
  = do toks <- lexTokens src
       (m,items) <- either (Left . show) Right (runParser programP st0 "" toks)
       let defs = [d | IDef d <- items]
           code k = [c | IForeign k' c <- items, k' == k]
       return Program{ progName = m
                     , progTypes = M.union (M.fromList [(tdefName d, d) | IType d <- items]) types
                     , progSigs = M.unions [M.fromList [(n,s) | ISig n s <- items], M.fromList [(defName d, sigOf d) | d <- defs], sigs]
                     , progExterns = M.union (M.fromList [(n,x) | IExtern n x <- items]) externs
                     , progForeign = Foreign (code "header") (code "end") (code "source")
                     , progDefs = defs }
  where
    st0 = PState (M.unionsWith (++) (map (consOf False) (M.elems types))) M.empty

sigOf :: Def -> Sig
sigOf def
  = case def of
      DefFun _ tvs ps q r _ -> SigFun tvs [(m,t) | (_,m,t) <- ps] q r
      DefVal _ tvs t _ -> SigVal tvs t

programP :: P (Name,[Item])
programP = do kw "module"
              m <- newModuleName <$> nameP
              items <- many itemP
              eof
              return (m,items)

itemP :: P Item
itemP = do modifyState (\st -> st{ psBinders = M.empty })
           choice [dataP, funP, valDefP, conP, externP, foreignP]

funP :: P Item
funP = do kw "fun"
          n <- globalName <$> nameP
          tvs <- tyParamsP
          ps <- parensP (commaSep param)
          sym ":"
          q <- modeP
          r <- vP
          (do sym "="; args <- mapM named ps; IDef . DefFun n tvs args q r <$> exprP)
            <|> (do ts <- mapM unnamed ps; return (ISig n (SigFun tvs ts q r)))
  where
    param = do m <- modeP; mx <- optionMaybe (try (pathP <* sym ":")); t <- vP; x <- traverse rootBinder mx; return (m,x,t)
    named (m,mx,t) = maybe (fail "a parameter without a name") (\x -> return (x,m,t)) mx
    unnamed (m,mx,t) = maybe (return (m,t)) (const (fail "a named parameter of a function without a body")) mx

valDefP :: P Item
valDefP = do kw "val"
             n <- globalName <$> nameP
             tvs <- tyParamsP
             sym ":"
             t <- vP
             (do sym "="; IDef . DefVal n tvs t <$> exprP) <|> return (ISig n (SigVal tvs t))

externP :: P Item
externP = do kw "extern"
             n <- globalName <$> nameP
             ps <- parensP (commaSep (do x <- globalName <$> nameP; sym ":"; t <- ktypeP; return (x,t)))
             sym ":"
             r <- ktypeP
             sym "="
             fmt <- stringP
             return (IExtern n (Extern fmt ps r))
  where
    ktypeP = choice [KBox <$ kw "box", KFun <$ kw "fun", KCon . globalName <$> nameP]

foreignP :: P Item
foreignP = do kw "foreign"
              k <- choice [k <$ kw k | k <- ["header","end","source"]]
              IForeign k <$> stringP

stringP :: P String
stringP = tokenP (\t -> case t of
                          TString s -> Just s
                          _ -> Nothing) <?> "string"

conP :: P Item
conP = do kw "con"
          n <- globalName <$> nameP
          tvs <- tyParamsP
          ts <- parensP (commaSep vP)
          sym ":"
          t <- globalName <$> nameP
          _ <- tyParamsP
          return (ISig n (SigCon tvs ts t))

-- the alternatives of a datatype in the order they print: a sum, a lazy sum, or one alternative
data Body = BSum [BAlt] | BLazy Body Body | BOne BAlt

-- an alternative: its tag or the name of its constructor, its shape and the names of its fields
type BAlt = (Either Int String, AType, [Field])

dataP :: P Item
dataP = do kw "data"
           n <- globalName <$> nameP
           tvs <- tyParamsP
           (body,labels) <- choice
             [ do sym ":"; sym "="; (t,labels) <- numberBody n <$> bodyP; return (BodyRef t, labels)
             , do kw "value"; sym ":"; sym "="; (t,labels) <- valueBodyP n; return (BodyValue t, labels)
             , (BodyOpen,[]) <$ kw "open"
             , return (BodyAbstract,[]) ]
           decls <- many (do kw "decl"; c <- labelP; ds <- parensP (commaSep declP); return (conOf n c, ds))
           let label (ConLabel c fs _) = ConLabel c fs (maybe (map (const Nothing) fs) id (lookup c decls))
               d = TypeDef n tvs body (map label labels)
           modifyState (\st -> st{ psCons = M.unionWith (++) (consOf True d) (psCons st) })
           return (IType d)
  where
    declP = (Nothing <$ kw "_") <|> (Just . globalName <$> nameP)

-- The body of a value datatype: a raw type, or its constructors, whose fields are labelled as
-- a product (even a single one, which the type does not wrap)
valueBodyP :: Name -> P (VType,[ConLabel])
valueBodyP tname
  = (do r <- rawP; return (VRaw r, []))
    <|> (do alts <- (sym "(" *> sepBy1 altP (sym "+") <* sym ")") <|> ((:[]) <$> altP)
            let labels = [ConLabel (conOf tname c) (fields v) [] | (c,v) <- alts]
                ts = [unlabel v | (_,v) <- alts]
            return (case ts of
                      [t] -> t
                      _   -> VSum (zip (map (Con . lblCon) labels) ts), labels))
  where
    altP = do c <- labelP; sym ":"; v <- vP; return (c,v)
    fields v = case v of
                 VProd fs -> map fst fs
                 VExists _ b -> fields b
                 _ -> []
    unlabel v = case v of
                  VProd [(_,t)] -> t
                  VExists vs b -> VExists vs (unlabel b)
                  _ -> v

bodyP :: P Body
bodyP = (sym "(" >> (lazy <|> sumP)) <|> (BOne <$> altP')
  where
    lazy = do _ <- lookAhead (sym "("); l <- bodyP; sym "~>"; s <- bodyP; sym ")"; return (BLazy l s)
    sumP = do as <- sepBy1 altP' (sym "+"); sym ")"; return (BSum as)
    altP' = do lbl <- (Left <$> intP) <|> (Right <$> labelP)
               sym ":"
               (t,fs) <- shapeP
               return (lbl,t,fs)
    -- the only field of a constructor is labelled in its box
    shapeP = (do f <- try (kw "Box" >> sym "(" >> labelP <* sym ":"); v <- vP; sym ")"; return (ABox v, [Field (labelName f)]))
             <|> (do t <- aP
                     return (t, case t of
                                  ABox v -> fields v
                                  _ -> []))
    fields v = case v of
                 VProd fs -> map fst fs
                 VExists _ b -> fields b
                 _ -> []

-- a constructor of a datatype: it is in the module of the datatype, and may have a local qualifier
conOf :: Name -> String -> Name
conOf tname s = let c = localName s in newLocallyQualified (nameModule tname) (nameLocalQual c) (nameStem c)

-- The tags of the alternatives of a datatype follow the order of its constructors, where the
-- strict alternatives S of a lazy sum `L ~> S` come first. Alternatives without a constructor
-- print their tags.
numberBody :: Name -> Body -> (AType,[ConLabel])
numberBody tname body = (shape, [ConLabel (conOf tname c) fs [] | (_,Right c,_,fs) <- tagged])
  where
    altsOf b = case b of
                 BSum as -> as
                 BOne a -> [a]
                 BLazy l s -> altsOf s ++ altsOf l
    tagged = [(either id (const k) lbl, lbl, t, fs) | (k,(lbl,t,fs)) <- zip [1..] (altsOf body)]
    sumOf ts = ASum [(i,t) | (i,_,t,_) <- ts]
    shape = case body of
              BOne (_,t,_) -> t
              BSum _ -> sumOf tagged
              BLazy _ s -> let (ss,ls) = splitAt (length (altsOf s)) tagged in ALazy (sumOf ls) (sumOf ss)
