-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Printing.

  A program prints with everything but the type annotations of values, which follow from where
  the values occur: the module name, the datatypes of the module with the labels of their
  constructors in their bodies, the signatures of the module without a definition (externals and constructors
  of open types), and the definitions. Imported datatypes and signatures are not printed.

  In a definition, paths are shortened by the labels of datatypes (`shortSteps`): `t.Node.left`
  for `t.deref.roll.Node.contents.left`. The binder of a destructuring prints the information
  that its path omits (the tag of an alternative, the index of a field), and every path prints
  differently from the other binders of the definition, so that a printed path names its binder.
  Where two binders would print the same, they print with all their steps. Names that could be
  read as keywords or other tokens are in backquotes.

  Messages print values, types and expressions without a program, with all their steps.
-}
module Backend.Typed.Pretty( ppr, prettyProgram, reserved ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Char( isDigit )
import Data.List( intercalate, isPrefixOf )
import Lib.PPrint
import Common.Name
import Common.Syntax( DefInline(..) )
import Backend.Typed.Syntax
import Backend.Typed.Traversal( bindersE, child )

-- how a definition prints its paths
type PP = Path -> Doc

instance Pretty AType   where pretty = prettyA fullPath
instance Pretty VType   where pretty = prettyV fullPath
instance Pretty Ty      where pretty = prettyT fullPath
instance Pretty AVal    where pretty = prettyAVal fullPath
instance Pretty VVal    where pretty = prettyVal fullPath
instance Pretty VExpr   where pretty = prettyExpr fullPath
instance Pretty Def     where pretty = prettyDef fullPath
instance Pretty Program where pretty = prettyProgram

-- for messages
ppr :: Pretty a => a -> String
ppr x = show (pretty x)

--------------------------------------------------------------------------
-- Names and paths
--------------------------------------------------------------------------

nm :: Name -> Doc
nm n = text (escape (show n))

-- a name in backquotes if it could be read as a keyword or another token (an operator in
-- parentheses could be read as that of a sum or product)
escape :: String -> String
escape s = if reserved s then "`" ++ s ++ "`" else s

reserved :: String -> Bool
reserved s = null s || "(" `isPrefixOf` s || s `elem` keywords || "box@" `isPrefixOf` s || any numbered ["v","inj","inj-a","reuse","no-reuse","cell"]
  where
    numbered p = p `isPrefixOf` s && not (null (drop (length p) s)) && all isDigit (drop (length p) s)
    keywords = words ("ret let in of case split at if-whnf whnf delay ptr roll box scalar pack dup drop free"
                      ++ " if-unique if-full then else join rec and jump fn gen forall exists unreachable"
                      ++ " cast-ev total memoize ctx ctx-copy hole some null is-null if-yielding yield up down lock @ @copy _"
                      ++ " module data con inline noinline fun val extern foreign Box Scalar I KCtx NaN Infinity"
                      ++ " char ssize_t intptr_t float64 float32 int64 int32 int16 int8 uint8")

-- a path with all its steps
fullPath :: PP
fullPath (Path x ss) = text (intercalate "." (escape (show x) : map show ss))

-- the fields of each constructor of a reference datatype (paths into values name no
-- constructors of value datatypes, whose names may clash with those of reference datatypes)
type Fields = M.Map Name [Field]

fieldsOf :: TypeDefs -> Fields
fieldsOf tdefs = M.fromList [(lblCon l, lblFields l) | d@TypeDef{ tdefBody = BodyRef _ } <- M.elems tdefs, l <- tdefLabels d]

-- The steps of a path, shortened by labels: a constructor stands for the steps to its
-- alternative (`deref`, `roll`, and the tests of the tag on the way: `whnf`, `delay`, `lo`, `hi`
-- and `rest`), and a field for the steps into the contents of its box (from the pointer, if it
-- has no constructor). The contents of a constructor with one field are that field.
shortSteps :: Fields -> [Step] -> [String]
shortSteps fields = go []
  where
    -- fs: the fields of the constructor of the box at which the steps start
    go fs ss
      = case ss of
          [] -> []
          SContents : rest | [f] <- fs -> show f : go [] rest
          SContents : SField _ f : rest -> show f : go [] rest
          _ | (_:_, rest@(SInjA _ _ : _)) <- span toAlt ss -> go [] rest
            | (_:_, rest@(SContents : SField _ _ : _)) <- span toBox ss -> go [] rest
          SInjA _ c@(Con n) : rest -> show c : go (M.findWithDefault [] n fields) rest
          s : rest -> show s : go [] rest
    toAlt s = s `elem` [SDeref, SRoll, SWhnf, SDelay, SLo, SHi, SRest]
    toBox s = s `elem` [SDeref, SRoll]

-- The paths of a definition: shortened, unless another binder of the definition would print the
-- same, shortened or with all its steps. Steps compare by tag and index, so a path prints with
-- the constructors and fields of its binder.
defPaths :: Fields -> Def -> PP
defPaths fields def = pathDoc . asBound
  where
    asBound x = M.findWithDefault x x bound
    bound = M.fromList [(y,y) | y <- xs]
    pathDoc x = let s = short x
                in if all (== x) (M.findWithDefault [] s binders) then text s else fullPath x
    short (Path r ss) = intercalate "." (escape (show r) : shortSteps fields ss)
    binders = M.fromListWith (++) ([(short x,[x]) | x <- xs] ++ [(show (fullPath x),[x]) | x <- xs])
    xs = params ++ bindersE (defBody def)
    params = case def of
               DefFun{ defArgs = ps } -> [x | (x,_,_) <- ps]
               DefVal{} -> []

--------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------

tv :: TVar -> Doc
tv v = text ("v" ++ show v)

prettyA :: PP -> AType -> Doc
prettyA pp a
  = case a of
      ABox t        -> text "Box" <.> parens (prettyV pp t)
      AScalar r     -> text "Scalar" <.> parens (prettyRaw r)
      AUnit         -> text "1"
      ASum ts       -> parens (hsep (punctuate (text " +") [int i <.> text ":" <.> atomA pp t | (i,t) <- ts]))
      AFun ps r     -> parens (commaSep [mode m <.> prettyV pp p | (m,p) <- ps]) <+> text "->" <+> prettyV pp r
      AForall vs b  -> text "forall" <+> hsep (map tv vs) <.> text "." <+> prettyA pp b
      AVar v        -> tv v
      AApp v ts     -> tv v <.> angles (commaSep (map (prettyA pp) ts))
      ACon n []     -> nm n
      ACon n ts     -> nm n <.> angles (commaSep (map (prettyA pp) ts))
      ALam vs b     -> parens (text "\\" <.> hsep (map tv vs) <.> text "." <+> prettyA pp b)
      ALazy l b     -> parens (atomA pp l <+> text "~>" <+> atomA pp b)

-- a type that extends to the right in parentheses
atomA :: PP -> AType -> Doc
atomA pp a
  = case a of
      AFun _ _    -> parens (prettyA pp a)
      AForall _ _ -> parens (prettyA pp a)
      _           -> prettyA pp a

mode :: Mode -> Doc
mode Owned    = empty
mode Unique   = text "!"
mode Borrowed = text "^"

prettyV :: PP -> VType -> Doc
prettyV pp t
  = case t of
      VPtr a@(AVar _)   -> prettyA pp a <.> text "*"
      VPtr a@(ACon _ _) -> prettyA pp a <.> text "*"
      VPtr a     -> parens (prettyA pp a) <.> text "*"
      VReuse f n contents -> text ("reuse" ++ (if f == Full then "!" else "") ++ show n) <.> prettyContents pp contents
      VUnit      -> text "I"
      VSum ts    -> infixes "(+)" [labelled (show c) ("inj" ++ show i) (prettyV pp s) | (i,(c,s)) <- zip [0 :: Int ..] ts]
      VProd fs   -> infixes "(x)" [labelled (show f) ("field" ++ show i) (prettyV pp s) | (i,(f,s)) <- zip [0 :: Int ..] fs]
      VRaw r     -> prettyRaw r
      VExists vs b -> parens (text "exists" <+> hsep (map tv vs) <.> text "." <+> prettyV pp b)
      VCtx f a b -> text ("ctx" ++ (if f == Full then "+" else "")) <.> angles (commaSep [prettyA pp a, prettyA pp b])
      VCell n a -> text ("cell" ++ show n) <.> angles (prettyA pp a)
      VOrNull b -> prettyV pp b <.> text "?"
      VToken    -> text "KCtx"

-- a component of a sum or product with its label, unless that is the default one for its
-- position (`tagCon`, `posField`)
labelled :: String -> String -> Doc -> Doc
labelled l def d = if l == def then d else text (escape l) <.> colon <+> d

-- an n-ary sum or product; one with a single component ends with the operator
infixes :: String -> [Doc] -> Doc
infixes op [d] = parens (d <+> text op)
infixes op ds  = parens (hsep (punctuate (text (" " ++ op)) ds))

prettyRaw :: Raw -> Doc
prettyRaw r
  = text (case r of
            RChar    -> "char"
            RSSize   -> "ssize_t"
            RIntPtr  -> "intptr_t"
            RFloat64 -> "float64"
            RFloat32 -> "float32"
            RInt64   -> "int64"
            RInt32   -> "int32"
            RInt16   -> "int16"
            RInt8    -> "int8"
            RUInt8   -> "uint8")

prettyT :: PP -> Ty -> Doc
prettyT pp (A a) = prettyA pp a
prettyT pp (V t) = prettyV pp t

prettyContents :: PP -> Maybe Contents -> Doc
prettyContents pp = maybe empty (\(Contents k p t) -> brackets (text (maybe "_" show k) <.> semi <+> prettyVal pp p <+> text ":" <+> prettyV pp t))

commaSep :: [Doc] -> Doc
commaSep ds = hcat (punctuate (text ", ") ds)

tyArgs :: PP -> [AType] -> Doc
tyArgs pp ts = brackets (commaSep (map (prettyA pp) ts))

tyParams :: [TVar] -> Doc
tyParams [] = empty
tyParams vs = angles (commaSep (map tv vs))

params :: PP -> [(Path,Mode,VType)] -> Doc
params pp ps = parens (commaSep [mode m <.> pp x <+> colon <+> prettyV pp t | (x,m,t) <- ps])

side :: Side -> Doc
side Whnf  = text "whnf"
side Delay = text "delay"

--------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------

prettyAVal :: PP -> AVal -> Doc
prettyAVal pp val
  = case val of
      Fun f      -> nm f
      UnitA      -> text "()"
      InjA i _ v -> text "inj-a" <.> int i <+> atomAVal pp v
      Roll _ v   -> text "roll" <+> atomAVal pp v
      InjLazy d _ v -> side d <+> atomAVal pp v
      Box v      -> text "box" <+> atomVal pp v
      Scalar v   -> text "scalar" <+> atomVal pp v
      OpenCon c ts vs -> nm c <.> tyArgs pp ts <.> args pp vs
      Lam ps r e -> text "fn" <.> params pp ps <+> colon <+> prettyV pp r <+> text "->" <-> indent 2 (prettyExpr pp e)
      BoxAt r v  -> text "box@" <.> pp r <+> atomVal pp v

prettyVal :: PP -> VVal -> Doc
prettyVal pp val
  = case val of
      Var x      -> pp x
      Glob x []  -> nm x
      Glob x ts  -> nm x <.> tyArgs pp ts
      UnitV      -> text "()"
      Lit l      -> prettyLit l
      Inj i _ v  -> text "inj" <.> int i <+> atomVal pp v
      Tuple [v]  -> parens (prettyVal pp v <.> comma)   -- not a value in parentheses
      Tuple vs   -> parens (commaSep (map (prettyVal pp) vs))
      Ptr _ v    -> text "ptr" <+> atomAVal pp v
      Pack _ ts v -> text "pack" <.> tyArgs pp ts <+> atomVal pp v
      TyApp v@(Glob _ _) ts -> parens (prettyVal pp v) <.> tyArgs pp ts   -- not `Glob x ts`
      TyApp v ts  -> atomVal pp v <.> tyArgs pp ts
      Up v        -> text "up" <+> atomVal pp v
      Down b v    -> text "down" <.> tyArgs pp [b] <+> atomVal pp v
      DupV v      -> text "dup" <+> atomVal pp v
      NoReuse n p -> text "no-reuse" <.> int n <.> prettyContents pp p
      Hole        -> text "hole"
      Context _ v -> text "ctx" <+> atomVal pp v
      Some v      -> text "some" <+> atomVal pp v
      Null _      -> text "null"

args :: PP -> [VVal] -> Doc
args pp vs = parens (commaSep (map (prettyVal pp) vs))

atomAVal :: PP -> AVal -> Doc
atomAVal pp v
  = case v of
      Fun _ -> prettyAVal pp v
      UnitA -> prettyAVal pp v
      _     -> parens (prettyAVal pp v)

atomVal :: PP -> VVal -> Doc
atomVal pp v
  = case v of
      Inj _ _ _   -> parens (prettyVal pp v)
      Ptr _ _     -> parens (prettyVal pp v)
      Pack _ _ _  -> parens (prettyVal pp v)
      DupV _      -> parens (prettyVal pp v)
      Context _ _ -> parens (prettyVal pp v)
      Some _      -> parens (prettyVal pp v)
      Up _        -> parens (prettyVal pp v)
      Down _ _    -> parens (prettyVal pp v)
      _           -> prettyVal pp v

prettyLit :: Lit -> Doc
prettyLit lit
  = case lit of
      LitInt i    -> text (show i)
      LitFloat d  -> text (show d)
      LitChar c   -> text (show c)
      LitString s -> text (show s)

--------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------

prettyExpr :: PP -> VExpr -> Doc
prettyExpr pp expr
  = case expr of
      Ret v -> text "ret" <+> atomVal pp v
      Let x t e1 e2 -> letIn empty (pp x <+> colon <+> prettyV pp t) (align (prettyExpr pp e1)) e2
      Unreachable _ -> text "unreachable"
      Call f [] vs -> nm f <.> args pp vs
      Call f ts vs -> nm f <.> tyArgs pp ts <.> args pp vs
      App f vs -> pp f <.> args pp vs
      Proj v i x e -> letIn empty (pp x) (atomVal pp v <.> text "." <.> int i) e
      CaseV v alts -> caseOf (text "case") (prettyVal pp v) [(text "inj" <.> int i <+> pp x, e) | (i,x,e) <- alts]
      SplitA v k (x,e1) (y,e2) -> caseOf (text "split") (pp v <+> text "at" <+> int k) [(pp x, e1), (pp y, e2)]
      IfWhnf v (x,e1) (y,e2) -> caseOf (text "if-whnf") (pp v) [(side Whnf <+> pp x, e1), (side Delay <+> pp y, e2)]
      CaseA v alts def -> caseOf (text "case") (pp v)
                              ([(text "inj-a" <.> int i <+> pp x, e) | (i,x,e) <- alts] ++ [(text "_" <+> pp x, e) | Just (x,e) <- [def]])
      Deref v x e -> letIn empty (text "ptr" <+> pp x) (prettyVal pp v) e
      Unroll v x e -> letIn empty (text "roll" <+> pp x) (pp v) e
      Unbox v x e -> letIn empty (text "box" <+> pp x) (pp v) e
      Unscalar m v x e -> letIn (mode m) (text "scalar" <+> pp x) (pp v) e
      IsNull v n (x,e) -> caseOf (text "is-null") (prettyVal pp v) [(text "null", n), (pp x, e)]
      IfYielding v (k3,e3) (k2,e2) -> caseOf (text "if-yielding") (prettyVal pp v) [(text "yield" <+> pp k3, e3), (pp k2, e2)]
      Unpack v vs x e -> letIn empty (text "pack" <.> brackets (commaSep (map tv vs)) <+> pp x) (prettyVal pp v) e
      CaseLit v alts def -> caseOf (text "case") (prettyVal pp v) ([(prettyLit l, e) | (l,e) <- alts] ++ [(text "_", def)])
      Dup x e -> text "dup" <+> pp x <.> semi <-> prettyExpr pp e
      Drop x e -> text "drop" <+> pp x <.> semi <-> prettyExpr pp e
      Free r e -> text "free" <+> pp r <.> semi <-> prettyExpr pp e
      IsUnique x e1 e2 -> ifThen (text "if-unique" <+> pp x) e1 e2
      IfFull r e1 e2 -> ifThen (text "if-full" <+> pp r) e1 e2
      UnboxRu z e -> letIn empty (text "@" <+> pp (child z SCredit)) (pp z) e
      CopyRu z r e -> letIn empty (text "@copy" <+> pp r) (pp z) e
      Lock z e -> letIn empty (text "lock" <+> pp (child z SCredit)) (pp z) e
      Join j tvs ps e1 e2 -> text "join" <+> nm j <.> tyParams tvs <.> params pp ps <+> text "="
                         <-> indent 2 (prettyExpr pp e1) <-> text "in" <+> align (prettyExpr pp e2)
      JoinRec t ds e -> foldr (<->) (text "in" <+> align (prettyExpr pp e))
                          [text kw <+> nm j <.> tyParams tvs <.> params pp ps <+> res <-> indent 2 (prettyExpr pp e1)
                          | (kw,res,JoinDef j tvs ps e1) <- zip3 ("join rec" : repeat "and") (colon <+> prettyV pp t <+> text "=" : repeat (text "=")) ds]
      Jump j [] vs -> text "jump" <+> nm j <.> args pp vs
      Jump j ts vs -> text "jump" <+> nm j <.> tyArgs pp ts <.> args pp vs
      Plug c v -> atomVal pp c <.> brackets (prettyVal pp v)
      Append c d -> atomVal pp c <+> text "++" <+> atomVal pp d
      CtxCopy c -> text "ctx-copy" <+> atomVal pp c
      CastEv u t e -> text "cast-ev" <.> brackets (prettyV pp u <.> comma <+> prettyV pp t) <+> align (prettyExpr pp e)
      Memoize c d k v -> text "memoize" <+> atomVal pp c <+> parens (side d <+> parens (text "inj" <.> int k <+> atomVal pp v))
      Gen vs e -> text "gen" <+> hsep (map tv vs) <.> text "." <+> align (prettyExpr pp e)
      Total k e -> text "total" <+> pp k <.> text "." <+> align (prettyExpr pp e)
      CaseOpen v alts def -> caseOf (text "case") (pp v) ([(nm c <.> parens (commaSep (map pp xs)), e) | (c,xs,e) <- alts] ++ [(text "_", def)])
  where
    -- `let` with a mode, followed by the body on the next line
    letIn m lhs rhs body = text "let" <.> m <+> lhs <+> text "=" <+> rhs <+> text "in" <-> prettyExpr pp body
    -- a case-like expression with one alternative per line
    caseOf kw scrut alts = kw <+> scrut <+> text "of" <-> indent 2 (vcat [pat <+> text "->" <+> align (prettyExpr pp e) | (pat,e) <- alts])
    ifThen test e1 e2 = test <-> indent 2 (vcat [text "then" <+> align (prettyExpr pp e1), text "else" <+> align (prettyExpr pp e2)])

--------------------------------------------------------------------------
-- Programs
--------------------------------------------------------------------------

inline :: DefInline -> Doc
inline InlineAuto = empty
inline inl        = text (show inl) <.> space   -- `inline` or `noinline`

prettyDef :: PP -> Def -> Doc
prettyDef pp def
  = case def of
      DefFun f vs ps q r e inl -> inline inl <.> text "fun" <+> nm f <.> tyParams vs <.> params pp ps <+> colon <+> mode q <.> prettyV pp r <+> text "=" <-> indent 2 (prettyExpr pp e)
      DefVal x vs t e          -> text "val" <+> nm x <.> tyParams vs <+> colon <+> prettyV pp t <+> text "=" <-> indent 2 (prettyExpr pp e)

-- The declaration of a datatype, whose alternatives are labelled by their constructors instead
-- of their tags: the tags are those of the labels, in order (and in a lazy sum `L ~> S`, those of
-- S come first), with their local qualifiers. The only field of a constructor is labelled in its
-- box, as it is no product. The body of a value datatype (`value :=`) labels the fields of each
-- constructor as a product, even a single one. The declared types of the fields of a constructor
-- follow (`decl C(T, _)`), if any.
prettyTypeDef :: TypeDef -> Doc
prettyTypeDef (TypeDef n vs body labels)
  = text "data" <+> nm n <.> tyParams vs <.> bodyDoc
    <.> hcat [text " decl" <+> nm (unqualify c) <.> parens (commaSep (map (maybe (text "_") nm) ds))
             | ConLabel c _ ds <- labels, any (/= Nothing) ds]
  where
    bodyDoc
      = case body of
          BodyRef b    -> text " :=" <+> labelledBody b
          BodyValue v  -> text " value :=" <+> labelledValue v
          BodyOpen     -> text " open"
          BodyAbstract -> empty
    labelledBody b
      = case b of
          ASum ts   -> parens (hsep (punctuate (text " +") [alt i t | (i,t) <- ts]))
          ALazy l s -> parens (labelledBody l <+> text "~>" <+> labelledBody s)
          _         -> alt 1 b
    alt i t
      = case drop (i-1) labels of
          ConLabel c fs _ : _ -> nm (unqualify c) <.> colon <+> shape fs t
          [] -> int i <.> colon <+> atomA fullPath t
    shape [f] (ABox v) = text "Box" <.> parens (text (escape (show f)) <.> colon <+> prettyV fullPath v)
    shape _ t = atomA fullPath t
    labelledValue v
      = case (labels,v) of
          ([],_)     -> prettyV fullPath v
          ([l],_)    -> valt l v
          (_,VSum ts) -> parens (hsep (punctuate (text " +") [valt l t | (l,(_,t)) <- zip labels ts]))
          _          -> prettyV fullPath v
    valt (ConLabel c fs _) t = nm (unqualify c) <.> colon <+> prettyV fullPath (fields fs t)
    fields [f] (VExists ws t) = VExists ws (fields [f] t)
    fields [f] t = VProd [(f,t)]
    fields _ t = t

-- a signature without a definition: an external function or value, or a constructor of an open
-- datatype
prettySig :: Name -> Sig -> Doc
prettySig n sig
  = case sig of
      SigFun vs ps q r -> text "fun" <+> nm n <.> tyParams vs <.> parens (commaSep [mode m <.> prettyV fullPath t | (m,t) <- ps])
                          <+> colon <+> mode q <.> prettyV fullPath r
      SigVal vs t      -> text "val" <+> nm n <.> tyParams vs <+> colon <+> prettyV fullPath t
      SigCon vs ts t   -> text "con" <+> nm n <.> tyParams vs <.> parens (commaSep (map (prettyV fullPath) ts))
                          <+> colon <+> nm t <.> tyParams vs

-- Koka's C types of an external, and its format
prettyExtern :: Name -> Extern -> Doc
prettyExtern n (Extern fmt ps r)
  = text "extern" <+> nm n <.> parens (commaSep [nm x <.> colon <+> ktype t | (x,t) <- ps]) <+> colon <+> ktype r
    <+> text "=" <+> text (show fmt)
  where
    ktype t = case t of
                KCon c -> nm c
                KBox -> text "box"
                KFun -> text "fun"

prettyForeign :: Foreign -> [Doc]
prettyForeign (Foreign hs es ss)
  = [text "foreign" <+> text k <+> text (show c) | (k,cs) <- [("header",hs),("end",es),("source",ss)], c <- cs]

prettyProgram :: Program -> Doc
prettyProgram prog
  = vcat (punctuate linebreak (map vcat (filter (not . null) sections)))
  where
    sections = [ [text "module" <+> nm (progName prog)]
               , prettyForeign (progForeign prog)
               , [prettyTypeDef d | d <- M.elems (progTypes prog), local (tdefName d)]
               , [prettySig n s | (n,s) <- M.toList (progSigs prog), local n, not (S.member n defined)]
               , [prettyExtern n x | (n,x) <- M.toList (progExterns prog), local n]
               , [prettyDef (defPaths fields d) d | d <- progDefs prog] ]
    local n = qualifier n == progName prog
    defined = S.fromList (map defName (progDefs prog))
    fields = fieldsOf (progTypes prog)
