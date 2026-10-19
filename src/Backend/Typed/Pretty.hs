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
      VReuse n contents -> text ("reuse" ++ show n) <.> prettyContents contents
      VUnit      -> text "I"
      VSum ts    -> parens (hsep (punctuate (text " (+)") (map prettyV ts)))
      VProd x y  -> parens (prettyV x <+> text "(x)" <+> prettyV y)
      VRaw n     -> nm n
      VExists vs t -> parens (text "exists" <+> hsep (map tv vs) <.> text "." <+> prettyV t)
      VCtx a b   -> text "ctx" <.> angles (commaSep [prettyA a, prettyA b])

prettyT :: Ty -> Doc
prettyT (A a) = prettyA a
prettyT (V t) = prettyV t

commaSep :: [Doc] -> Doc
commaSep ds = hcat (punctuate (text ", ") ds)

prettyAVal :: AVal -> Doc
prettyAVal val
  = case val of
      Fun f      -> nm f
      UnitA      -> text "()"
      InjA i _ v -> text ("inj-a" ++ show i) <+> atomAVal v
      Roll _ v   -> text "roll" <+> atomAVal v
      Box v      -> text "box" <+> atomVal v
      Scalar v   -> text "scalar" <+> atomVal v
      OpenCon c ts v -> nm c <.> brackets (commaSep (map prettyA ts)) <+> atomVal v
      Lam ps r e -> text "fn" <.> parens (commaSep [mode m <.> pv x <+> colon <+> prettyV t | (x,m,t) <- ps])
                    <+> colon <+> prettyV r <+> text "->" <-> indent 2 (prettyExpr e)
      BoxAt r v   -> text "box@" <.> pv r <+> atomVal v
      BoxIn x v   -> text "box-in@" <.> pv x <+> atomVal v

prettyContents :: Maybe Contents -> Doc
prettyContents = maybe empty (\(Contents k p t) -> brackets (text (show k) <.> semi <+> prettyVal p <+> text ":" <+> prettyV t))

prettyVal :: VVal -> Doc
prettyVal val
  = case val of
      Var x      -> pv x
      Glob x []  -> nm x
      Glob x ts  -> nm x <.> brackets (commaSep (map prettyA ts))
      UnitV      -> text "()"
      Lit l      -> prettyLit l
      Inj i _ v  -> text ("inj" ++ show i) <+> atomVal v
      Pair v w   -> parens (prettyVal v <.> comma <+> prettyVal w)
      Ptr _ v    -> text "ptr" <+> atomAVal v
      Pack _ ts v -> text "pack" <.> brackets (commaSep (map prettyA ts)) <+> atomVal v
      TyApp v ts  -> atomVal v <.> brackets (commaSep (map prettyA ts))
      DupV v      -> text "dup" <+> atomVal v
      NoReuse n p -> text ("no-reuse" ++ show n) <.> prettyContents p
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
      Let x t e1 e2 -> text "let" <+> pv x <+> colon <+> prettyV t <+> text "=" <+> align (prettyExpr e1) <+> text "in" <-> prettyExpr e2
      Call f [] vs -> nm f <.> parens (commaSep (map prettyVal vs))
      Call f ts vs -> nm f <.> brackets (commaSep (map prettyA ts)) <.> parens (commaSep (map prettyVal vs))
      App f vs -> pv f <.> parens (commaSep (map prettyVal vs))
      Unpair m v x y e -> text "let" <.> mode m <+> parens (pv x <.> comma <+> pv y) <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      CaseV m v alts -> text "case" <.> mode m <+> prettyVal v <+> text "of" <-> indent 2 (vcat [text ("inj" ++ show i) <+> pv x <+> text "->" <+> align (prettyExpr e) | (i,(x,e)) <- zip [0::Int ..] alts])
      SplitA m v k (x,e1) (y,e2) -> text "split" <.> mode m <+> pv v <+> text "at" <+> text (show k) <+> text "of"
                                    <-> indent 2 (vcat [pv x <+> text "->" <+> align (prettyExpr e1), pv y <+> text "->" <+> align (prettyExpr e2)])
      CaseA m v alts def -> text "case" <.> mode m <+> pv v <+> text "of" <-> indent 2 (vcat ([text ("inj-a" ++ show i) <+> pv x <+> text "->" <+> align (prettyExpr e) | (i,x,e) <- alts] ++ maybe [] (\(x,e) -> [text "_" <+> pv x <+> text "->" <+> align (prettyExpr e)]) def))
      Deref m v x e -> text "let" <.> mode m <+> text "ptr" <+> pv x <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      Unroll m v x e -> text "let" <.> mode m <+> text "roll" <+> pv x <+> text "=" <+> pv v <+> text "in" <-> prettyExpr e
      Unbox m v x e -> text "let" <.> mode m <+> text "box" <+> pv x <+> text "=" <+> pv v <+> text "in" <-> prettyExpr e
      UnboxLazy v x e -> text "let-lazy box" <+> pv x <+> text "=" <+> pv v <+> text "in" <-> prettyExpr e
      Unpack m v vs x e -> text "let" <.> mode m <+> text "pack" <.> brackets (commaSep (map tv vs)) <+> pv x <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      CaseLit v alts def -> text "case" <+> prettyVal v <+> text "of" <-> indent 2 (vcat ([prettyLit l <+> text "->" <+> align (prettyExpr e) | (l,e) <- alts] ++ [text "_ ->" <+> align (prettyExpr def)]))
      Dup x e -> text "dup" <+> pv x <.> semi <-> prettyExpr e
      Drop x e -> text "drop" <+> pv x <.> semi <-> prettyExpr e
      Free r e -> text "free" <+> pv r <.> semi <-> prettyExpr e
      IsUnique x e1 e2 -> text "if-unique" <+> pv x <-> indent 2 (vcat [text "then" <+> align (prettyExpr e1), text "else" <+> align (prettyExpr e2)])
      UnboxRu v r e -> text "let @" <+> pv r <+> text "=" <+> pv v <+> text "in" <-> prettyExpr e
      Join j ps e1 e2 -> text "join" <+> nm j <.> parens (commaSep [mode m <.> pv x <+> colon <+> prettyV t | (x,m,t) <- ps]) <+> text "="
                         <-> indent 2 (prettyExpr e1) <-> text "in" <+> align (prettyExpr e2)
      Jump j vs -> text "jump" <+> nm j <.> parens (commaSep (map prettyVal vs))
      Gen vs e -> text "gen" <+> hsep (map tv vs) <.> text "." <+> align (prettyExpr e)
      CaseOpen m v alts def -> text "case" <.> mode m <+> pv v <+> text "of" <-> indent 2 (vcat ([nm c <+> pv x <+> text "->" <+> align (prettyExpr e) | (c,x,e) <- alts] ++ [text "_ ->" <+> align (prettyExpr def)]))

prettyDef :: Def -> Doc
prettyDef def
  = case def of
      DefFun f vs ps r e -> text "fun" <+> nm f <.> tparams vs <.> parens (commaSep [mode m <.> pv x <+> colon <+> prettyV t | (x,m,t) <- ps])
                            <+> colon <+> prettyV r <+> text "=" <-> indent 2 (prettyExpr e)
      DefVal x vs t e    -> text "val" <+> nm x <.> tparams vs <+> colon <+> prettyV t <+> text "=" <-> indent 2 (prettyExpr e)
  where
    tparams [] = empty
    tparams vs = angles (commaSep (map tv vs))

prettyProgram :: Program -> Doc
prettyProgram prog
  = vcat (map prettyDef (progDefs prog))
