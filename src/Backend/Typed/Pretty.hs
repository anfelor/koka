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
instance Pretty Val     where pretty = prettyVal
instance Pretty Expr    where pretty = prettyExpr
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

mode :: Mode -> Doc
mode Owned    = empty
mode Unique   = text "!"
mode Borrowed = text "^"

prettyV :: VType -> Doc
prettyV t
  = case t of
      VVar v     -> tv v
      VApp v ts  -> tv v <.> angles (commaSep (map prettyV ts))
      VCon n []  -> nm n
      VCon n ts  -> nm n <.> angles (commaSep (map prettyV ts))
      VPtr a     -> parens (prettyA a) <.> text "*"
      VUnit      -> text "I"
      VSum ts    -> parens (hsep (punctuate (text " (+)") (map prettyV ts)))
      VProd x y  -> parens (prettyV x <+> text "(x)" <+> prettyV y)
      VRaw n     -> nm n
      VExists vs t -> parens (text "exists" <+> hsep (map tv vs) <.> text "." <+> prettyV t)
      VTLam vs t -> parens (text "\\" <.> hsep (map tv vs) <.> text "." <+> prettyV t)
      VReuse n   -> text ("reuse" ++ show n)

prettyT :: Ty -> Doc
prettyT (A a) = prettyA a
prettyT (V t) = prettyV t

commaSep :: [Doc] -> Doc
commaSep ds = hcat (punctuate (text ", ") ds)

prettyVal :: Val -> Doc
prettyVal val
  = case val of
      Var x      -> nm x
      Fun f      -> nm f
      Glob x []  -> nm x
      Glob x ts  -> nm x <.> brackets (commaSep (map prettyV ts))
      Unit       -> text "()"
      Lit l      -> prettyLit l
      Inj i _ v  -> text ("inj" ++ show i) <+> atomVal v
      Inl _ v    -> text "inl" <+> atomVal v
      Inr _ v    -> text "inr" <+> atomVal v
      Pair v w   -> parens (prettyVal v <.> comma <+> prettyVal w)
      Fold _ v   -> text "fold" <+> atomVal v
      Box v      -> text "box" <+> atomVal v
      Pack _ ts v -> text "pack" <.> brackets (commaSep (map prettyV ts)) <+> atomVal v
      OpenCon c ts v -> nm c <.> brackets (commaSep (map prettyV ts)) <+> atomVal v
      Lam ps r e -> text "fn" <.> parens (commaSep [mode m <.> nm x <+> colon <+> prettyV t | (x,m,t) <- ps])
                    <+> colon <+> prettyV r <+> text "->" <-> indent 2 (prettyExpr e)
      TyApp v ts  -> atomVal v <.> brackets (commaSep (map prettyV ts))
      Dup v       -> text "dup" <+> atomVal v
      BoxAt r v   -> text "box@" <.> nm r <+> atomVal v
      BoxIn x v   -> text "box-in@" <.> nm x <+> atomVal v
      NoReuse n   -> text ("no-reuse" ++ show n)

atomVal :: Val -> Doc
atomVal v
  = case v of
      Inj _ _ _ -> parens (prettyVal v)
      Inl _ _   -> parens (prettyVal v)
      Inr _ _   -> parens (prettyVal v)
      Fold _ _  -> parens (prettyVal v)
      Box _     -> parens (prettyVal v)
      BoxAt _ _ -> parens (prettyVal v)
      BoxIn _ _ -> parens (prettyVal v)
      Dup _     -> parens (prettyVal v)
      Lam _ _ _ -> parens (prettyVal v)
      _         -> prettyVal v

prettyLit :: Lit -> Doc
prettyLit lit
  = case lit of
      LitInt i    -> text (show i)
      LitFloat d  -> text (show d)
      LitChar c   -> text (show c)
      LitString s -> text (show s)

prettyExpr :: Expr -> Doc
prettyExpr expr
  = case expr of
      Ret v -> text "ret" <+> atomVal v
      Let x t e1 e2 -> text "let" <+> nm x <+> colon <+> prettyT t <+> text "=" <+> align (prettyExpr e1) <+> text "in" <-> prettyExpr e2
      Call f [] vs -> nm f <.> parens (commaSep (map prettyVal vs))
      Call f ts vs -> nm f <.> brackets (commaSep (map prettyV ts)) <.> parens (commaSep (map prettyVal vs))
      App f vs -> atomVal f <.> parens (commaSep (map prettyVal vs))
      Unpair m v x y e -> text "let" <.> mode m <+> parens (nm x <.> comma <+> nm y) <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      CaseV m v alts -> text "case" <.> mode m <+> prettyVal v <+> text "of" <-> indent 2 (vcat [text ("inj" ++ show i) <+> nm x <+> text "->" <+> align (prettyExpr e) | (i,(x,e)) <- zip [0::Int ..] alts])
      CaseA m v (x,e1) (y,e2) -> text "case" <.> mode m <+> prettyVal v <+> text "of" <-> indent 2 (vcat [text "inl" <+> nm x <+> text "->" <+> align (prettyExpr e1), text "inr" <+> nm y <+> text "->" <+> align (prettyExpr e2)])
      Unfold m v x e -> text "let" <.> mode m <+> text "fold" <+> nm x <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      Unbox m v x e -> text "let" <.> mode m <+> text "box" <+> nm x <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      UnboxLazy v x e -> text "let-lazy box" <+> nm x <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      Unpack m v vs x e -> text "let" <.> mode m <+> text "pack" <.> brackets (commaSep (map tv vs)) <+> nm x <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      CaseLit v alts def -> text "case" <+> prettyVal v <+> text "of" <-> indent 2 (vcat ([prettyLit l <+> text "->" <+> align (prettyExpr e) | (l,e) <- alts] ++ [text "_ ->" <+> align (prettyExpr def)]))
      Drop x e -> text "drop" <+> nm x <.> semi <-> prettyExpr e
      DropRu x r e -> text "let" <+> nm r <+> text "= drop-reuse" <+> nm x <+> text "in" <-> prettyExpr e
      IsUnique x e1 e2 -> text "if-unique" <+> nm x <-> indent 2 (vcat [text "then" <+> align (prettyExpr e1), text "else" <+> align (prettyExpr e2)])
      UnboxRu v x r e -> text "let box" <+> nm x <+> text "@" <+> nm r <+> text "=" <+> prettyVal v <+> text "in" <-> prettyExpr e
      Join j ps e1 e2 -> text "join" <+> nm j <.> parens (commaSep [mode m <.> nm x <+> colon <+> prettyV t | (x,m,t) <- ps]) <+> text "="
                         <-> indent 2 (prettyExpr e1) <-> text "in" <+> align (prettyExpr e2)
      Jump j vs -> text "jump" <+> nm j <.> parens (commaSep (map prettyVal vs))
      Gen vs e -> text "gen" <+> hsep (map tv vs) <.> text "." <+> align (prettyExpr e)
      CaseOpen m v alts def -> text "case" <.> mode m <+> prettyVal v <+> text "of" <-> indent 2 (vcat ([nm c <+> nm x <+> text "->" <+> align (prettyExpr e) | (c,x,e) <- alts] ++ [text "_ ->" <+> align (prettyExpr def)]))

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
