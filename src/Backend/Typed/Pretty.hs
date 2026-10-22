-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

module Backend.Typed.Pretty( ppr ) where

import Lib.PPrint
import Common.Name
import Backend.Typed.Syntax

nm :: Name -> Doc
nm n = text (show n)

pv :: Path -> Doc
pv x = text (show x)

instance Pretty AType   where pretty = prettyA
instance Pretty VType   where pretty = prettyV
instance Pretty Ty      where pretty = prettyT
instance Pretty AVal    where pretty = prettyAVal
instance Pretty VVal    where pretty = prettyVal
instance Pretty VExpr    where pretty = prettyExpr
instance Pretty Def     where pretty = prettyDef
instance Pretty Program where pretty = prettyProgram

-- for messages
ppr :: Pretty a => a -> String
ppr x = show (pretty x)

tv :: TVar -> Doc
tv v = text ("v" ++ show v)

prettyA :: AType -> Doc
prettyA a
  = case a of
      ABox t        -> text "Box" <.> parens (prettyV t)
      AScalar t     -> text "Scalar" <.> parens (prettyV t)
      AUnit         -> text "1"
      ASum ts       -> parens (hsep (punctuate (text " +")
                        [text (show i) <.> text ":" <.> prettyA t | (i,t) <- ts]))
      AFun ps r     -> parens (commaSep [mode m <.> prettyV p | (m,p) <- ps]) <+> text "->" <+> prettyV r
      AForall vs b  -> text "forall" <+> hsep (map tv vs) <.> text "." <+> prettyA b
      AVar v        -> tv v
      AApp v ts     -> tv v <.> angles (commaSep (map prettyA ts))
      ACon n []     -> nm n
      ACon n ts     -> nm n <.> angles (commaSep (map prettyA ts))
      ALam vs b     -> parens (text "\\" <.> hsep (map tv vs) <.> text "." <+> prettyA b)

mode :: Mode -> Doc
mode Owned    = empty
mode Unique   = text "!"
mode Borrowed = text "^"

prettyV :: VType -> Doc
prettyV t
  = case t of
      VPtr a@(AVar _)   -> prettyA a <.> text "*"
      VPtr a@(ACon _ _) -> prettyA a <.> text "*"
      VPtr a     -> parens (prettyA a) <.> text "*"
      VReuse f n contents -> text ("reuse" ++ (if f == Full then "!" else "") ++ show n) <.> prettyContents contents
      VUnit      -> text "I"
      VSum ts    -> parens (hsep (punctuate (text " (+)") (map prettyV ts)))
      VProd x y  -> parens (prettyV x <+> text "(x)" <+> prettyV y)
      VRaw r     -> prettyRaw r
      VExists vs t -> parens (text "exists" <+> hsep (map tv vs) <.> text "." <+> prettyV t)
      VCtx f a b -> text ("ctx" ++ (if f == Full then "+" else "")) <.> angles (commaSep [prettyA a, prettyA b])

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

prettyT :: Ty -> Doc
prettyT (A a) = prettyA a
prettyT (V t) = prettyV t

commaSep :: [Doc] -> Doc
commaSep ds = hcat (punctuate (text ", ") ds)

tyArgs :: [AType] -> Doc
tyArgs ts = brackets (commaSep (map prettyA ts))

args :: [VVal] -> Doc
args vs = parens (commaSep (map prettyVal vs))

params :: [(Path,Mode,VType)] -> Doc
params ps = parens (commaSep [mode m <.> pv x <+> colon <+> prettyV t | (x,m,t) <- ps])

prettyAVal :: AVal -> Doc
prettyAVal val
  = case val of
      Fun f      -> nm f
      UnitA      -> text "()"
      InjA i _ v -> text "inj-a" <.> int i <+> atomAVal v
      Roll _ v   -> text "roll" <+> atomAVal v
      Box v      -> text "box" <+> atomVal v
      Scalar v   -> text "scalar" <+> atomVal v
      OpenCon c ts vs -> nm c <.> tyArgs ts <.> args vs
      Lam ps r e -> text "fn" <.> params ps <+> colon <+> prettyV r <+> text "->" <-> indent 2 (prettyExpr e)
      BoxAt r v   -> text "box@" <.> pv r <+> atomVal v
      BoxIn x v   -> text "box-in@" <.> pv x <+> atomVal v

prettyContents :: Maybe Contents -> Doc
prettyContents = maybe empty (\(Contents k p t) -> brackets (text (maybe "_" show k) <.> semi <+> prettyVal p <+> text ":" <+> prettyV t))

prettyVal :: VVal -> Doc
prettyVal val
  = case val of
      Var x      -> pv x
      Glob x []  -> nm x
      Glob x ts  -> nm x <.> tyArgs ts
      UnitV      -> text "()"
      Lit l      -> prettyLit l
      Inj i _ v  -> text "inj" <.> int i <+> atomVal v
      Pair v w   -> parens (prettyVal v <.> comma <+> prettyVal w)
      Ptr _ v    -> text "ptr" <+> atomAVal v
      Pack _ ts v -> text "pack" <.> tyArgs ts <+> atomVal v
      TyApp v ts  -> atomVal v <.> tyArgs ts
      DupV v      -> text "dup" <+> atomVal v
      NoReuse n p -> text "no-reuse" <.> int n <.> prettyContents p
      Hole        -> text "hole"
      Context _ v -> text "ctx" <+> atomVal v
      Plug c v    -> atomVal c <.> brackets (prettyVal v)
      CtxCopy v   -> text "ctx-copy" <+> atomVal v
      Append c d  -> atomVal c <+> text "++" <+> atomVal d

atomAVal :: AVal -> Doc
atomAVal v
  = case v of
      Fun _ -> prettyAVal v
      UnitA -> prettyAVal v
      _     -> parens (prettyAVal v)

atomVal :: VVal -> Doc
atomVal v
  = case v of
      Inj _ _ _ -> parens (prettyVal v)
      Ptr _ _   -> parens (prettyVal v)
      DupV _    -> parens (prettyVal v)
      Context _ _ -> parens (prettyVal v)
      CtxCopy _ -> parens (prettyVal v)
      Append _ _ -> parens (prettyVal v)
      _         -> prettyVal v

prettyLit :: Lit -> Doc
prettyLit lit
  = case lit of
      LitInt i    -> text (show i)
      LitFloat d  -> text (show d)
      LitChar c   -> text (show c)
      LitString s -> text (show s)

prettyExpr :: VExpr -> Doc
prettyExpr expr
  = case expr of
      Ret v -> text "ret" <+> atomVal v
      Let x t e1 e2 -> letIn empty (pv x <+> colon <+> prettyV t) (align (prettyExpr e1)) e2
      LetYield x t e1 e2 e3 -> text "let" <+> pv x <+> colon <+> prettyV t <+> text "=" <+> align (prettyExpr e1)
                               <-> indent 2 (text "yielding" <+> align (prettyExpr e3)) <-> text "in" <+> align (prettyExpr e2)
      Yielded _ -> text "yielded"
      Call f [] vs -> nm f <.> args vs
      Call f ts vs -> nm f <.> tyArgs ts <.> args vs
      App f vs -> pv f <.> args vs
      Proj m v ss x e -> letIn (mode m) (pv x) (atomVal v <.> hcat [text "." <.> text (show s) | s <- ss]) e
      CaseV m v alts -> caseOf (text "case" <.> mode m) (prettyVal v) [(text "inj" <.> int i <+> pv x, e) | (i,(x,e)) <- zip [0..] alts]
      SplitA m v k (x,e1) (y,e2) -> caseOf (text "split" <.> mode m) (pv v <+> text "at" <+> int k) [(pv x, e1), (pv y, e2)]
      CaseA m v alts def -> caseOf (text "case" <.> mode m) (pv v)
                              ([(text "inj-a" <.> int i <+> pv x, e) | (i,x,e) <- alts] ++ [(text "_" <+> pv x, e) | Just (x,e) <- [def]])
      Deref m v x e -> letIn (mode m) (text "ptr" <+> pv x) (prettyVal v) e
      Unroll m v x e -> letIn (mode m) (text "roll" <+> pv x) (pv v) e
      Unbox m v x e -> letIn (mode m) (text "box" <+> pv x) (pv v) e
      Unscalar m v x e -> letIn (mode m) (text "scalar" <+> pv x) (pv v) e
      UnboxLazy v x e -> letIn (text "-lazy") (text "box" <+> pv x) (pv v) e
      Unpack m v vs x e -> letIn (mode m) (text "pack" <.> brackets (commaSep (map tv vs)) <+> pv x) (prettyVal v) e
      CaseLit v alts def -> caseOf (text "case") (prettyVal v) ([(prettyLit l, e) | (l,e) <- alts] ++ [(text "_", def)])
      Dup x e -> text "dup" <+> pv x <.> semi <-> prettyExpr e
      Drop x e -> text "drop" <+> pv x <.> semi <-> prettyExpr e
      Free r e -> text "free" <+> pv r <.> semi <-> prettyExpr e
      IsUnique x e1 e2 -> ifThen (text "if-unique" <+> pv x) e1 e2
      IfFull r e1 e2 -> ifThen (text "if-full" <+> pv r) e1 e2
      UnboxRu v r e -> letIn empty (text "@" <+> pv r) (pv v) e
      Join j ps e1 e2 -> text "join" <+> nm j <.> params ps <+> text "="
                         <-> indent 2 (prettyExpr e1) <-> text "in" <+> align (prettyExpr e2)
      Jump j vs -> text "jump" <+> nm j <.> args vs
      Gen vs e -> text "gen" <+> hsep (map tv vs) <.> text "." <+> align (prettyExpr e)
      CaseOpen m v alts def -> caseOf (text "case" <.> mode m) (pv v) ([(nm c <.> parens (commaSep (map pv xs)), e) | (c,xs,e) <- alts] ++ [(text "_", def)])

-- `let` with a mode, followed by the body on the next line
letIn :: Doc -> Doc -> Doc -> VExpr -> Doc
letIn m lhs rhs body = text "let" <.> m <+> lhs <+> text "=" <+> rhs <+> text "in" <-> prettyExpr body

-- a case-like expression with one alternative per line
caseOf :: Doc -> Doc -> [(Doc,VExpr)] -> Doc
caseOf kw scrut alts = kw <+> scrut <+> text "of" <-> indent 2 (vcat [pat <+> text "->" <+> align (prettyExpr e) | (pat,e) <- alts])

ifThen :: Doc -> VExpr -> VExpr -> Doc
ifThen test e1 e2 = test <-> indent 2 (vcat [text "then" <+> align (prettyExpr e1), text "else" <+> align (prettyExpr e2)])

prettyDef :: Def -> Doc
prettyDef def
  = case def of
      DefFun f vs ps r e -> text "fun" <+> nm f <.> tparams vs <.> params ps <+> colon <+> prettyV r <+> text "=" <-> indent 2 (prettyExpr e)
      DefVal x vs t e    -> text "val" <+> nm x <.> tparams vs <+> colon <+> prettyV t <+> text "=" <-> indent 2 (prettyExpr e)
  where
    tparams [] = empty
    tparams vs = angles (commaSep (map tv vs))

prettyProgram :: Program -> Doc
prettyProgram prog
  = vcat (map prettyDef (progDefs prog))
