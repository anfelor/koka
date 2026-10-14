-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-- Structural queries shared by the Core-to-typed-IR passes.
module Backend.Typed.Elab.Common( isValue, isConExpr ) where

import Core.Core( Expr(..) )

isValue :: Expr -> Bool
isValue expr
  = case expr of
      Var _ _       -> True
      Lit _         -> True
      Con _ _       -> True
      Lam _ _ _     -> True
      TypeLam _ e   -> isValue e
      TypeApp e _   -> isValue e
      App f args    -> isConExpr f && all isValue args
      _             -> False

isConExpr :: Expr -> Bool
isConExpr (Con _ _)     = True
isConExpr (TypeApp e _) = isConExpr e
isConExpr _             = False
