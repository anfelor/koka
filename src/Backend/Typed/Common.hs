-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Traversals and derived rules for the typed intermediate language.
module Backend.Typed.Common where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Common.Name
import Common.NamePrim( nameTpFieldAddr, nameTpReuse )
import Backend.Typed.Syntax
import Backend.Typed.Types( Types(..), inst )

-- A continuation that wraps an expression.
type K = VExpr -> VExpr

compose :: [K] -> K
compose = foldr (.) id

-- Discard an owned value by destructuring it down to boxed operands and credits.
-- The caller supplies fresh names from its own pass's supply.
dropValue :: Monad m => m Name -> Name -> Ty -> VExpr -> m VExpr
dropValue _ _ t e
  | isTrivial t = return e
dropValue fresh x t e
  = case t of
      A _ -> return (Drop x e)
      V v -> case v of
        VPtr a -> do y <- fresh
                     return (Deref Owned (Var x) y (Drop y e))
        VProd a b -> do y <- fresh
                        z <- fresh
                        rest <- dropValue fresh z (V b) e
                        body <- dropValue fresh y (V a) rest
                        return (Unpair Owned (Var x) y z body)
        VSum ts -> do alts <- mapM dropAlt ts
                      return (CaseV Owned (Var x) alts)
          where
            dropAlt s = do y <- fresh
                           body <- dropValue fresh y (V s) e
                           return (y,body)
        VExists tvs s
          -> do y <- fresh
                u <- fresh
                -- Keep the continuation outside the existential's scope.
                -- Fresh types only need to avoid the payload's free variables.
                let start = minimum (0 : tvs ++ ftv s) - 1
                    bs = take (length tvs) [start,start-1 ..]
                    s' = inst tvs (map AVar bs) s
                body <- dropValue fresh y (V s') (Ret UnitV)
                return (Let u VUnit (Unpack Owned (Var x) bs y body) e)
        VReuse _ -> return (Free x e)
        VUnit -> return e
        VRaw _ -> return e

-- values of these types need no reference counting
isTrivial :: Ty -> Bool
isTrivial t
  = case t of
      V v -> trivialV v
      A a -> trivialA a
  where
    trivialV v = case v of
                   VRaw _       -> True
                   VUnit        -> True
                   VProd x y    -> trivialV x && trivialV y
                   VSum ts      -> all trivialV ts
                   VExists _ b  -> trivialV b
                   VPtr a       -> trivialA a
                   VReuse _     -> False
    trivialA a = case a of
                   AUnit     -> True
                   ASum x y  -> trivialA x && trivialA y
                   ACon n _  -> n `elem` [nameTpFieldAddr, nameTpReuse]
                   ABox _    -> False
                   AFun _ _  -> False
                   AForall _ _ -> False
                   AVar _    -> False
                   AApp _ _  -> False
                   ALam _ _  -> False

-- Boxed sum alternatives must have a tag determined by their construction.
isShape :: AType -> Bool
isShape a = case a of
  AUnit -> True
  ABox _ -> True
  ASum l r -> isShape l && isShape r
  _ -> False

-- Credits have ownership but no reference count: duplication cannot create another owner.
containsReuse :: Ty -> Bool
containsReuse (V v) = case v of
  VPtr a -> containsReuse (A a)
  VProd a b -> containsReuse (V a) || containsReuse (V b)
  VSum ts -> any (containsReuse . V) ts
  VExists _ b -> containsReuse (V b)
  VUnit -> False
  VRaw _ -> False
  VReuse _ -> True
containsReuse (A a) = case a of
  ABox v -> containsReuse (V v)
  ASum a b -> containsReuse (A a) || containsReuse (A b)
  AForall _ b -> containsReuse (A b)
  ALam _ b -> containsReuse (A b)
  ACon _ ts -> any (containsReuse . A) ts
  AApp _ ts -> any (containsReuse . A) ts
  AVar _ -> False
  AFun _ _ -> False
  AUnit -> False

tapp :: VVal -> [AType] -> VVal
tapp v []  = v
tapp v tys = TyApp v tys

sumOf :: [AType] -> AType
sumOf = foldr1 ASum

injA :: [AType] -> Int -> AVal -> AVal
injA [_] 0 v = v
injA ss 0 v  = Inl (sumOf ss) v
injA ss i v  = Inr (sumOf ss) (injA (tail ss) (i-1) v)

-- a case on each alternative of a boxed sum `a`; the branch gets the alternative, a variable at a
-- boxed type that it may only destructure
caseChain :: MonadFail m => (String -> m Name) -> [AType] -> Name -> (Int -> Name -> m VExpr) -> m VExpr
caseChain fresh shapes a branch = go 0 shapes a
  where
    go i [_] v = branch i v
    go _ [] _ = fail "empty case chain"
    go i (_:rest) v
      = do y <- fresh "y"
           z <- fresh "z"
           b1 <- branch i y
           b2 <- go (i+1) rest z
           return (CaseA Owned v (y,b1) (z,b2))

-- one-level traversals

-- Names are operands, not values: a traversal must preserve their variable form.
-- Lambda bodies are handled separately from the values directly inside a value.
descendA :: Applicative f => (Name -> f Name) -> (AVal -> f AVal) -> (VVal -> f VVal) -> AVal -> f AVal
descendA fn fa fv val
  = case val of
      Inl a v        -> Inl a <$> fa v
      Inr a v        -> Inr a <$> fa v
      Roll a v       -> Roll a <$> fa v
      Box v          -> Box <$> fv v
      OpenCon c ts v -> OpenCon c ts <$> fv v
      BoxAt r v      -> BoxAt <$> fn r <*> fv v
      BoxIn x v      -> BoxIn <$> fn x <*> fv v
      Fun _          -> pure val
      UnitA          -> pure val
      Lam _ _ _      -> pure val

descendV :: Applicative f => (AVal -> f AVal) -> (VVal -> f VVal) -> VVal -> f VVal
descendV fa fv val
  = case val of
      Inj i t v      -> Inj i t <$> fv v
      Pair v w       -> Pair <$> fv v <*> fv w
      Ptr a v        -> Ptr a <$> fa v
      Pack t ts v    -> Pack t ts <$> fv v
      TyApp v ts     -> (`TyApp` ts) <$> fv v
      DupV v         -> DupV <$> fv v
      Var _          -> pure val
      Glob _ _       -> pure val
      UnitV          -> pure val
      Lit _          -> pure val
      NoReuse _      -> pure val

mapA :: (Name -> Name) -> (AVal -> AVal) -> (VVal -> VVal) -> AVal -> AVal
mapA fn fa fv = runIdentity . descendA (Identity . fn) (Identity . fa) (Identity . fv)

mapV :: (AVal -> AVal) -> (VVal -> VVal) -> VVal -> VVal
mapV fa fv = runIdentity . descendV (Identity . fa) (Identity . fv)

-- the operands and subexpressions of an expression, with the variables bound in each subexpression
descendE :: Applicative f => (Name -> f Name) -> (VVal -> f VVal) -> ([Name] -> VExpr -> f VExpr) -> VExpr -> f VExpr
descendE fn fv fe expr
  = case expr of
      Ret v                 -> Ret <$> fv v
      Let x t e1 e2         -> Let x t <$> fe [] e1 <*> fe [x] e2
      Call f ts vs          -> Call f ts <$> traverse fv vs
      App f vs              -> App <$> fn f <*> traverse fv vs
      Unpair m v x y e      -> (\v' -> Unpair m v' x y) <$> fv v <*> fe [x,y] e
      CaseV m v alts        -> CaseV m <$> fv v <*> traverse (\(x,e) -> (,) x <$> fe [x] e) alts
      CaseA m v (x,e1) (y,e2) -> (\v' e1' e2' -> CaseA m v' (x,e1') (y,e2')) <$> fn v <*> fe [x] e1 <*> fe [y] e2
      Deref m v x e         -> (\v' -> Deref m v' x) <$> fv v <*> fe [x] e
      Unroll m v x e        -> (\v' -> Unroll m v' x) <$> fn v <*> fe [x] e
      Unbox m v x e         -> (\v' -> Unbox m v' x) <$> fn v <*> fe [x] e
      UnboxLazy v x e       -> (\v' -> UnboxLazy v' x) <$> fn v <*> fe [x] e
      Unpack m v tvs x e    -> (\v' -> Unpack m v' tvs x) <$> fv v <*> fe [x] e
      CaseLit v alts def    -> CaseLit <$> fv v <*> traverse (\(l,e) -> (,) l <$> fe [] e) alts <*> fe [] def
      CaseOpen m v alts def -> CaseOpen m <$> fn v <*> traverse (\(c,x,e) -> (,,) c x <$> fe [x] e) alts <*> fe [] def
      Gen tvs e             -> Gen tvs <$> fe [] e
      Drop x e              -> Drop <$> fn x <*> fe [] e
      Free r e              -> Free <$> fn r <*> fe [] e
      Dup x y e             -> (\x' -> Dup x' y) <$> fn x <*> fe [y] e
      IsUnique x e1 e2      -> IsUnique <$> fn x <*> fe [] e1 <*> fe [] e2
      UnboxRu v x r e       -> (\v' -> UnboxRu v' x r) <$> fn v <*> fe [x,r] e
      Join j ps e1 e2       -> Join j ps <$> fe [x | (x,_,_) <- ps] e1 <*> fe [] e2
      Jump j vs             -> Jump j <$> traverse fv vs

varOf :: VVal -> Name
varOf (Var y) = y
varOf v       = error ("Backend.Typed.Common.varOf: not a variable: " ++ show v)

-- free variables

fvA :: AVal -> S.Set Name
fvA val
  = case val of
      Lam ps _ e -> fvE e `S.difference` S.fromList [x | (x,_,_) <- ps]
      _ -> getConst (descendA (Const . S.singleton) (Const . fvA) (Const . fvV) val)

fvV :: VVal -> S.Set Name
fvV val
  = case val of
      Var x -> S.singleton x
      _ -> getConst (descendV (Const . fvA) (Const . fvV) val)

fvE :: VExpr -> S.Set Name
fvE = getConst . descendE (Const . S.singleton) (Const . fvV) (\xs e -> Const (fvE e `S.difference` S.fromList xs))

-- substitution of unboxed values (their free variables must not be bound in the scope).
-- A substitution at a named operand must itself be a variable; use a let for other values.
replaceA :: M.Map Name VVal -> AVal -> AVal
replaceA sub val
  = case val of
      Lam ps r e -> Lam ps r (replaceE (foldr M.delete sub [x | (x,_,_) <- ps]) e)
      _ -> mapA (replaceName sub) (replaceA sub) (replaceV sub) val

replaceV :: M.Map Name VVal -> VVal -> VVal
replaceV sub val
  = case val of
      Var x -> M.findWithDefault val x sub
      _ -> mapV (replaceA sub) (replaceV sub) val

replaceName :: M.Map Name VVal -> Name -> Name
replaceName sub x = maybe x varOf (M.lookup x sub)

replaceE :: M.Map Name VVal -> VExpr -> VExpr
replaceE sub expr
  | M.null sub = expr
  | otherwise = runIdentity (descendE (Identity . replaceName sub) (Identity . replaceV sub)
                  (\xs e -> Identity (replaceE (foldr M.delete sub xs) e)) expr)

-- renaming includes boxed operands as well as unboxed variables
renameA :: M.Map Name Name -> AVal -> AVal
renameA = replaceA . M.map Var

renameV :: M.Map Name Name -> VVal -> VVal
renameV = replaceV . M.map Var

renameE :: M.Map Name Name -> VExpr -> VExpr
renameE = replaceE . M.map Var

-- all bound variables (with repetitions)
bindersE :: VExpr -> [Name]
bindersE = getConst . descendE (const (Const [])) (Const . bindersV) (\xs e -> Const (xs ++ bindersE e))

bindersA :: AVal -> [Name]
bindersA val
  = case val of
      Lam ps _ e -> [x | (x,_,_) <- ps] ++ bindersE e
      _ -> getConst (descendA (const (Const [])) (Const . bindersA) (Const . bindersV) val)

bindersV :: VVal -> [Name]
bindersV = getConst . descendV (Const . bindersA) (Const . bindersV)

-- destructuring forms: the mode, the scrutinee, the alternatives with their binders, and a rebuild function.
-- Boxed scrutinees are names; unboxed scrutinees are values.
data Destruct v = Destruct{ dsMode :: Mode, dsScrut :: v, dsAlts :: [([Name],VExpr)], dsBuild :: Mode -> v -> [VExpr] -> VExpr }

destructAOf :: VExpr -> Maybe (Destruct Name)
destructAOf expr
  = case expr of
      CaseA m v (x,e1) (y,e2) -> Just (Destruct m v [([x],e1),([y],e2)] (\m' v' es -> CaseA m' v' (x,es !! 0) (y,es !! 1)))
      Unroll m v x e        -> Just (Destruct m v [([x],e)] (\m' v' es -> Unroll m' v' x (head es)))
      Unbox m v x e         -> Just (Destruct m v [([x],e)] (\m' v' es -> Unbox m' v' x (head es)))
      UnboxLazy v x e       -> Just (Destruct Borrowed v [([x],e)] (\_ v' es -> UnboxLazy v' x (head es)))
      CaseOpen m v alts def -> Just (Destruct m v ([([x],e) | (_,x,e) <- alts] ++ [([],def)])
                                       (\m' v' es -> CaseOpen m' v' [(c,x,e) | ((c,x,_),e) <- zip alts es] (last es)))
      Unpair{} -> Nothing
      CaseV{} -> Nothing
      Deref{} -> Nothing
      Unpack{} -> Nothing
      Ret{} -> Nothing
      Let{} -> Nothing
      Call{} -> Nothing
      App{} -> Nothing
      CaseLit{} -> Nothing
      Gen{} -> Nothing
      Dup{} -> Nothing
      Drop{} -> Nothing
      Free{} -> Nothing
      IsUnique{} -> Nothing
      UnboxRu{} -> Nothing
      Join{} -> Nothing
      Jump{} -> Nothing

destructVOf :: VExpr -> Maybe (Destruct VVal)
destructVOf expr
  = case expr of
      Unpair m v x y e      -> Just (Destruct m v [([x,y],e)] (\m' v' es -> Unpair m' v' x y (head es)))
      CaseV m v alts        -> Just (Destruct m v [([x],e) | (x,e) <- alts] (\m' v' es -> CaseV m' v' (zip (map fst alts) es)))
      Deref m v x e         -> Just (Destruct m v [([x],e)] (\m' v' es -> Deref m' v' x (head es)))
      Unpack m v tvs x e    -> Just (Destruct m v [([x],e)] (\m' v' es -> Unpack m' v' tvs x (head es)))
      CaseA{} -> Nothing
      Unroll{} -> Nothing
      Unbox{} -> Nothing
      UnboxLazy{} -> Nothing
      CaseOpen{} -> Nothing
      Ret{} -> Nothing
      Let{} -> Nothing
      Call{} -> Nothing
      App{} -> Nothing
      CaseLit{} -> Nothing
      Gen{} -> Nothing
      Dup{} -> Nothing
      Drop{} -> Nothing
      Free{} -> Nothing
      IsUnique{} -> Nothing
      UnboxRu{} -> Nothing
      Join{} -> Nothing
      Jump{} -> Nothing

-- reading the contents of a box never moves them
isRead :: VExpr -> Bool
isRead expr
  = case expr of
      Unbox{}     -> True
      UnboxLazy{} -> True
      CaseOpen{}  -> True
      Unpair{}    -> False
      CaseV{}     -> False
      CaseA{}     -> False
      Deref{}     -> False
      Unroll{}    -> False
      Unpack{}    -> False
      Ret{}       -> False
      Let{}       -> False
      Call{}      -> False
      App{}       -> False
      CaseLit{}   -> False
      Gen{}       -> False
      Dup{}       -> False
      Drop{}      -> False
      Free{}      -> False
      IsUnique{}  -> False
      UnboxRu{}   -> False
      Join{}      -> False
      Jump{}      -> False

-- the binders of these destructuring forms are the scrutinee's pointer, so they may be unique
keepsPointer :: VExpr -> Bool
keepsPointer expr
  = case expr of
      CaseA{}     -> True
      Deref{}     -> True
      Unroll{}    -> True
      Unpack{}    -> True
      Unpair{}    -> False
      CaseV{}     -> False
      Unbox{}     -> False
      UnboxLazy{} -> False
      CaseOpen{}  -> False
      Ret{}       -> False
      Let{}       -> False
      Call{}      -> False
      App{}       -> False
      CaseLit{}   -> False
      Gen{}       -> False
      Dup{}       -> False
      Drop{}      -> False
      Free{}      -> False
      IsUnique{}  -> False
      UnboxRu{}   -> False
      Join{}      -> False
      Jump{}      -> False
