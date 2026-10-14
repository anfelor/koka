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
      AUnit         -> text "1"
      ASum x y      -> parens (prettyA x <+> text "+" <+> prettyA y)
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
      VReuse n   -> text ("reuse" ++ show n)
      VUnit      -> text "I"
      VSum ts    -> parens (hsep (punctuate (text " (+)") (map prettyV ts)))
      VProd x y  -> parens (prettyV x <+> text "(x)" <+> prettyV y)
      VRaw n     -> nm n
      VExists vs t -> parens (text "exists" <+> hsep (map tv vs) <.> text "." <+> prettyV t)

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
      Inl _ v    -> text "inl" <+> atomAVal v
      Inr _ v    -> text "inr" <+> atomAVal v
      Roll _ v   -> text "roll" <+> atomAVal v
      Box v      -> text "box" <+> atomVal v
      OpenCon c ts v -> nm c <.> brackets (commaSep (map prettyA ts)) <+> atomVal v
      Lam ps r e -> text "fn" <.> parens (commaSep [mode m <.> nm x <+> colon <+> prettyV t | (x,m,t) <- ps])
                    <+> colon <+> prettyV r <+> text "->" <-> indent 2 (prettyExpr e)
      BoxAt r v   -> text "box@" <.> nm r <+> atomVal v
      BoxIn x v   -> text "box-in@" <.> nm x <+> atomVal v

prettyVal :: VVal -> Doc
prettyVal val
  = case val of
      Var x      -> nm x
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
      NoReuse n   -> text ("no-reuse" ++ show n)

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
      Let x t e1 e2 -> text "let" <+> nm x <+> colon <+> prettyV t <+> text "=" <+> align (prettyExpr e1) <+> text "in" <-> prettyExpr e2
      Call f [] vs -> nm f <.> parens (commaSep (map prettyVal vs))
      Call f ts vs -> nm f <.> brackets (commaSep (map prettyA ts)) <.> parens (commaSep (map prettyVal vs))
      App f vs -> nm f <.> parens (commaSep (map prettyVal vs))
      Unpair m v x y e -> text "let" <.> mode m <+> parens (nm x <.> comma <+> nm y) <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      CaseV m v alts -> text "case" <.> mode m <+> prettyVal v <+> text "of" <-> indent 2 (vcat [text ("inj" ++ show i) <+> nm x <+> text "->" <+> align (prettyExpr e) | (i,(x,e)) <- zip [0::Int ..] alts])
      CaseA m v (x,e1) (y,e2) -> text "case" <.> mode m <+> nm v <+> text "of" <-> indent 2 (vcat [text "inl" <+> nm x <+> text "->" <+> align (prettyExpr e1), text "inr" <+> nm y <+> text "->" <+> align (prettyExpr e2)])
      Deref m v x e -> text "let" <.> mode m <+> text "ptr" <+> nm x <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      Unroll m v x e -> text "let" <.> mode m <+> text "roll" <+> nm x <+> text "=" <+> nm v <+> text "in" <-> prettyExpr e
      Unbox m v x e -> text "let" <.> mode m <+> text "box" <+> nm x <+> text "=" <+> nm v <+> text "in" <-> prettyExpr e
      UnboxLazy v x e -> text "let-lazy box" <+> nm x <+> text "=" <+> nm v <+> text "in" <-> prettyExpr e
      Unpack m v vs x e -> text "let" <.> mode m <+> text "pack" <.> brackets (commaSep (map tv vs)) <+> nm x <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      CaseLit v alts def -> text "case" <+> prettyVal v <+> text "of" <-> indent 2 (vcat ([prettyLit l <+> text "->" <+> align (prettyExpr e) | (l,e) <- alts] ++ [text "_ ->" <+> align (prettyExpr def)]))
      Dup x y e -> text "let" <+> nm y <+> text "= dup" <+> nm x <+> text "in" <-> prettyExpr e
      Drop x e -> text "drop" <+> nm x <.> semi <-> prettyExpr e
      Free r e -> text "free" <+> nm r <.> semi <-> prettyExpr e
      IsUnique x e1 e2 -> text "if-unique" <+> nm x <-> indent 2 (vcat [text "then" <+> align (prettyExpr e1), text "else" <+> align (prettyExpr e2)])
      UnboxRu v x r e -> text "let box" <+> nm x <+> text "@" <+> nm r <+> text "=" <+> nm v <+> text "in" <-> prettyExpr e
      Join j ps e1 e2 -> text "join" <+> nm j <.> parens (commaSep [mode m <.> nm x <+> colon <+> prettyV t | (x,m,t) <- ps]) <+> text "="
                         <-> indent 2 (prettyExpr e1) <-> text "in" <+> align (prettyExpr e2)
      Jump j vs -> text "jump" <+> nm j <.> parens (commaSep (map prettyVal vs))
      Gen vs e -> text "gen" <+> hsep (map tv vs) <.> text "." <+> align (prettyExpr e)
      CaseOpen m v alts def -> text "case" <.> mode m <+> nm v <+> text "of" <-> indent 2 (vcat ([nm c <+> nm x <+> text "->" <+> align (prettyExpr e) | (c,x,e) <- alts] ++ [text "_ ->" <+> align (prettyExpr def)]))

prettyDef :: Def -> Doc
prettyDef def
  = case def of
      DefFun f vs ps r e -> text "fun" <+> nm f <.> tparams vs <.> parens (commaSep [mode m <.> nm x <+> colon <+> prettyV t | (x,m,t) <- ps])
                            <+> colon <+> prettyV r <+> text "=" <-> indent 2 (prettyExpr e)
      DefVal x vs t e    -> text "val" <+> nm x <.> tparams vs <+> colon <+> prettyV t <+> text "=" <-> indent 2 (prettyExpr e)
  where
    tparams [] = empty
    tparams vs = angles (commaSep (map tv vs))

prettyProgram :: Program -> Doc
prettyProgram prog
  = vcat (map prettyDef (progDefs prog))
