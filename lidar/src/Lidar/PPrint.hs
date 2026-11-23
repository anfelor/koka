------------------------------------------------------------------------------
-- Copyright 2012-2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{- Pretty printing, based on Philip Wadler's /prettier printer/.

  A copy of the document part of Koka's `Lib.PPrint`, without colours and
  output to handles and files. `show` renders a document exactly as Koka does.
-}
module Lidar.PPrint
  ( Doc, Docs
  , Pretty(pretty,prettyList)

  , (<.>), (<+>), (</>), (<//>), (<->), (<-->)

  , sep, fillSep, hsep, vsep
  , cat, fillCat, hcat, vcat
  , punctuate

  , align, hang, indent
  , fill, fillBreak

  , list, tupled, angled, semiBraces, encloseSep
  , angles, langle, rangle
  , parens, lparen, rparen
  , braces, lbrace, rbrace
  , brackets, lbracket, rbracket
  , dquotes, dquote, squotes, squote

  , comma, space, dot, backslash
  , semi, colon, equals

  , string, bool, int, integer, float, double, rational

  , softline, softbreak
  , empty, char, text, line, linebreak, nest, group
  , column, nesting, width
  , isEmptyDoc

  , SimpleDoc(..)
  , renderPretty, renderCompact
  , displayS, asString, defaultWidth
  ) where

import Data.String( IsString(..) )

infixr 5 </>,<//>,<->,<-->
infixr 6 <.>,<+>

-----------------------------------------------------------
-- Primitives
-----------------------------------------------------------
type Docs = [Doc]

data Doc = Empty
         | Char !Char             -- invariant: char is not '\n'
         | Text !String           -- invariant: text doesn't contain '\n'
         | Line !Bool             -- True <=> when undone by group, do not insert a space
         | Cat Doc Doc
         | Nest !Int Doc
         | Union Doc Doc          -- invariant: first lines of first doc longer than the first lines of the second doc
         | Column  (Int -> Doc)
         | Nesting (Int -> Doc)

data SimpleDoc = SEmpty
               | SChar Int Char SimpleDoc
               | SText Int String SimpleDoc
               | SLine Int SimpleDoc

isEmptyDoc :: Doc -> Bool
isEmptyDoc Empty = True
isEmptyDoc _     = False

empty :: Doc
empty = Empty

char :: Char -> Doc
char '\n' = line
char c    = Char c

text :: String -> Doc
text "" = Empty
text s  = Text s

text' :: String -> Doc
text' x | null x    = Empty
        | otherwise = Text x

line, linebreak :: Doc
line      = Line False
linebreak = Line True

beside :: Doc -> Doc -> Doc
beside Empty y = y
beside x Empty = x
beside x y     = Cat x y

nest :: Int -> Doc -> Doc
nest i x = Nest i x

column, nesting :: (Int -> Doc) -> Doc
column f  = Column f
nesting f = Nesting f

group :: Doc -> Doc
group x = Union (flatten x) x

flatten :: Doc -> Doc
flatten (Cat x y)    = Cat (flatten x) (flatten y)
flatten (Nest i x)   = Nest i (flatten x)
flatten (Line brk)   = if brk then Empty else Text " "
flatten (Union x _)  = flatten x
flatten (Column f)   = Column (flatten . f)
flatten (Nesting f)  = Nesting (flatten . f)
flatten other        = other   -- Empty, Char, Text

-----------------------------------------------------------
-- list, tupled and semiBraces pretty print a list of
-- documents either horizontally or vertically aligned.
-----------------------------------------------------------
list, tupled, semiBraces, angled :: [Doc] -> Doc
list       = encloseSep lbracket rbracket (text ", ")
tupled     = encloseSep lparen   rparen   (text ", ")
semiBraces = encloseSep lbrace   rbrace   semi
angled     = encloseSep langle   rangle   comma

encloseSep :: Doc -> Doc -> Doc -> [Doc] -> Doc
encloseSep left right sepr ds
  = case ds of
      []  -> left <.> right
      [d] -> left <.> d <.> right
      _   -> nest 2 (hcat (zipWith (<.>) (left : repeat sepr) ds) <.> right)

-- | punctuate p [d1,d2,...,dn] => [d1 <.> p,d2 <.> p, ... ,dn]
punctuate :: Doc -> [Doc] -> [Doc]
punctuate _ []     = []
punctuate _ [d]    = [d]
punctuate p (d:ds) = (d <.> p) : punctuate p ds

-----------------------------------------------------------
-- high-level combinators
-----------------------------------------------------------
sep, fillSep, hsep, vsep, cat, fillCat, hcat, vcat :: [Doc] -> Doc
sep     = group . vsep
fillSep = fold (</>)
hsep    = fold (<+>)
vsep    = fold (<->) . filter (not . isEmptyDoc)
cat     = group . vcat
fillCat = fold (<//>)
hcat    = fold (<.>)
vcat    = fold (<-->) . filter (not . isEmptyDoc)

fold :: (Doc -> Doc -> Doc) -> [Doc] -> Doc
fold _ [] = empty
fold f ds = foldr1 f ds

(<.>), (<+>), (</>), (<//>), (<->), (<-->) :: Doc -> Doc -> Doc
x <.> y = x `beside` y
x <+> y = x <.> space <.> y

Empty </> x = x
x </> Empty = x
x </> y     = x <.> softline <.> y

x <//> y = x <.> softbreak <.> y

Empty <-> x = x
x <-> Empty = x
x <-> y     = x <.> line <.> y

x <--> y = x <.> linebreak <.> y

softline, softbreak :: Doc
softline  = group line
softbreak = group linebreak

squotes, dquotes, braces, parens, angles, brackets :: Doc -> Doc
squotes  = enclose squote squote
dquotes  = enclose dquote dquote
braces   = enclose lbrace rbrace
parens   = enclose lparen rparen
angles   = enclose langle rangle
brackets = enclose lbracket rbracket

enclose :: Doc -> Doc -> Doc -> Doc
enclose l r x = l <.> x <.> r

lparen, rparen, langle, rangle, lbrace, rbrace, lbracket, rbracket :: Doc
lparen   = char '('
rparen   = char ')'
langle   = char '<'
rangle   = char '>'
lbrace   = char '{'
rbrace   = char '}'
lbracket = char '['
rbracket = char ']'

squote, dquote, semi, colon, comma, space, dot, backslash, equals :: Doc
squote    = char '\''
dquote    = char '"'
semi      = char ';'
colon     = char ':'
comma     = char ','
space     = char ' '
dot       = char '.'
backslash = char '\\'
equals    = char '='

-----------------------------------------------------------
-- Combinators for prelude types
-----------------------------------------------------------

-- | Like `text`, but replaces '\n' by `line`.
string :: String -> Doc
string ""       = empty
string ('\n':s) = line <.> string s
string s        = case span (/='\n') s of
                    (xs,ys) -> text xs <.> string ys

bool :: Bool -> Doc
bool b = text (show b)

int :: Int -> Doc
int i = text (show i)

integer :: Integer -> Doc
integer i = text (show i)

float :: Float -> Doc
float f = text (show f)

double :: Double -> Doc
double d = text (show d)

rational :: Rational -> Doc
rational r = text (show r)

-----------------------------------------------------------
-- overloading "pretty"
-----------------------------------------------------------
class Pretty a where
  pretty     :: a -> Doc
  prettyList :: [a] -> Doc
  prettyList = list . map pretty

instance Pretty a => Pretty [a] where
  pretty = prettyList

instance Pretty Doc where
  pretty = id

instance Pretty () where
  pretty () = text "()"

instance Pretty Bool where
  pretty b = bool b

instance Pretty Char where
  pretty c     = char c
  prettyList s = string s

instance Pretty Int where
  pretty i = int i

instance Pretty Integer where
  pretty i = integer i

instance Pretty Float where
  pretty f = float f

instance Pretty Double where
  pretty d = double d

instance (Pretty a,Pretty b) => Pretty (a,b) where
  pretty (x,y) = tupled [pretty x, pretty y]

instance (Pretty a,Pretty b,Pretty c) => Pretty (a,b,c) where
  pretty (x,y,z) = tupled [pretty x, pretty y, pretty z]

instance Pretty a => Pretty (Maybe a) where
  pretty Nothing  = empty
  pretty (Just x) = pretty x

-----------------------------------------------------------
-- semi primitive: fill and fillBreak
-----------------------------------------------------------
fillBreak :: Int -> Doc -> Doc
fillBreak f x = width x (\w -> if w > f then nest f linebreak
                                        else text' (spaces (f - w)))

fill :: Int -> Doc -> Doc
fill f d = width d (\w -> if w >= f then empty
                                    else text' (spaces (f - w)))

width :: Doc -> (Int -> Doc) -> Doc
width d f = column (\k1 -> d <.> column (\k2 -> f (k2 - k1)))

-----------------------------------------------------------
-- semi primitive: Alignment and indentation
-----------------------------------------------------------
indent :: Int -> Doc -> Doc
indent i d = hang i (text' (spaces i) <.> d)

hang :: Int -> Doc -> Doc
hang i d = align (nest i d)

align :: Doc -> Doc
align d = column (\k -> nesting (\i -> nest (k - i) d))   -- nesting might be negative :-)

-- string literals are documents under `OverloadedStrings`; like `string`, a newline is a `line`
instance IsString Doc where
  fromString = string

-----------------------------------------------------------
-- Renderers
-----------------------------------------------------------
instance Eq Doc where
  d1 == d2 = asString d1 == asString d2

-- | The default pretty printing algorithm.
renderPretty :: Float -> Int -> Doc -> SimpleDoc
renderPretty rfrac w x
  = best 0 0 0 [(0, x)]
  where
    -- r :: the ribbon width in characters
    r = max 0 (min w (round (fromIntegral w * rfrac)))

    -- best :: b = base nesting
    --         n = indentation of current line
    --         k = current column
    --        (ie. (k >= n) && (k - n == count of inserted characters)
    best :: Int -> Int -> Int -> [(Int,Doc)] -> SimpleDoc
    best _ _ _ [] = SEmpty
    best b n k ((i,d):ds)
      = case d of
          Empty     -> best b n k ds
          Char c    -> let k' = k+1 in seq k' (SChar b c (best b n k' ds))
          Text s    -> let k' = k + length s in seq k' (SText b s (best b n k' ds))
          Line _    -> SLine i (best b i i ds)
          Cat y z   -> best b n k ((i,y):(i,z):ds)
          Nest j y  -> let i' = i+j in seq i' (best (if b==0 then i' else b) n k ((i',y):ds))
          Union y z -> nicest n k (best b n k ((i,y):ds))
                                  (best b n k ((i,z):ds))
          Column f  -> best b n k ((i,f k):ds)
          Nesting f -> best b n k ((i,f i):ds)

    -- precondition: first lines of y are longer than the first lines of z.
    nicest n k y z | fits (min (w - k) (r - k + n)) y = y
                   | otherwise                         = z

fits :: Int -> SimpleDoc -> Bool
fits w _ | w < 0     = False
fits _ SEmpty        = True
fits w (SChar _ _ x) = fits (w - 1) x
fits w (SText _ s x) = fits (w - length s) x
fits _ (SLine _ _)   = True

-- | Render a document without indentation: fast and fewer characters, good for machines.
renderCompact :: Doc -> SimpleDoc
renderCompact x
  = scan 0 [x]
  where
    scan :: Int -> [Doc] -> SimpleDoc
    scan _ [] = SEmpty
    scan k (d:ds)
      = case d of
          Empty     -> scan k ds
          Char c    -> let k' = k+1 in seq k' (SChar 0 c (scan k' ds))
          Text s    -> let k' = k + length s in seq k' (SText 0 s (scan k' ds))
          Line _    -> SLine 0 (scan 0 ds)
          Cat y z   -> scan k (y:z:ds)
          Nest _ y  -> scan k (y:ds)
          Union _ z -> scan k (z:ds)
          Column f  -> scan k (f k:ds)
          Nesting f -> scan k (f 0:ds)

asString :: Doc -> String
asString doc = displayS (renderCompact doc) ""

displayS :: SimpleDoc -> ShowS
displayS SEmpty        = id
displayS (SChar _ c x) = showChar c . displayS x
displayS (SText _ s x) = showString s . displayS x
displayS (SLine i x)   = showString ('\n' : spaces i) . displayS x

instance Show Doc where
  showsPrec _ doc = displayS (renderPretty 0.5 defaultWidth doc)

spaces :: Int -> String
spaces n | n <= 0    = ""
         | otherwise = replicate n ' '

defaultWidth :: Int
defaultWidth = 512
