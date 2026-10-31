-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Shared construction, analysis and lazy metadata for the typed IR.
module Backend.Typed.Common where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Monoid( Sum(..) )
import Common.Name
import Common.NamePrim( nameTpReuse )
import Backend.Typed.Syntax
import Backend.Typed.Types( sumAlts, sumOf )
import Backend.Typed.Traversal

-- A continuation that wraps an expression.
type K = VExpr -> VExpr

compose :: [K] -> K
compose = foldr (.) id

-- the fields of a product variable (`[proj]`), named by their paths
fieldsAt :: Path -> VType -> [(Path,Int,VType)]
fieldsAt x t
  = case t of
      VProd fs -> [(child x (SField i f),i,s) | (i,(f,s)) <- zip [0..] fs]
      _ -> []

-- The duplication rule: the type of the copy of a variable of type `t`
dupType :: Ty -> Either String Ty
dupType t
  = case t of
      V (VReuse _ _ _) -> Left "dup of a reuse credit"
      V (VCell _ _) -> Left "dup of a cell"
      V _ -> Right t
      A _ -> Left "dup of a boxed value"

-- values of these types need no reference counting, where `unroll` gives the body of a
-- named type if it is known (a type with a single constructor without fields, for example)
isTrivialWith :: (AType -> Maybe AType) -> Ty -> Bool
isTrivialWith unroll t
  = case t of
      V v -> trivialV v
      A a -> trivialA a
  where
    trivialV v = case v of
                   VRaw _       -> True
                   VUnit        -> True
                   VProd fs     -> all (trivialV . snd) fs
                   VSum ts      -> all (trivialV . snd) ts
                   VExists _ b  -> trivialV b
                   VPtr a       -> trivialA a
                   VReuse _ _ _   -> False
                   VCtx _ _ _   -> False
                   VCell _ _    -> False
    trivialA a = case a of
                   AUnit     -> True
                   ASum ts   -> all (trivialA . snd) ts
                   ACon n _  -> n == nameTpReuse || maybe False trivialA (unroll a)
                   ALazy l b -> trivialA l && trivialA b
                   AMu _ _ _ _ -> maybe False trivialA (unroll a)
                   ABox _    -> False
                   AScalar _ -> False
                   AFun _ _  -> False
                   AForall _ _ -> False
                   AVar _    -> False
                   AApp _ _  -> False
                   ALam _ _  -> False

-- Boxed sum alternatives must have a tag determined by their construction: sums are flat and
-- their tags are increasing.
isShape :: AType -> Bool
isShape a = case a of
  ASum ts -> not (null ts) && all (\(i,t) -> i >= 1 && isAlt t) ts
             && and [i < j | ((i,_),(j,_)) <- zip ts (drop 1 ts)]
  _ -> isAlt a
  where
    isAlt t = case t of
                AUnit -> True
                ABox _ -> True
                _ -> False

-- Credits and cells have ownership but no reference count: duplication cannot create another
-- owner, so they are not stored in a heap block or captured by a closure.
containsLinear :: Ty -> Bool
containsLinear (V v) = case v of
  VPtr a -> containsLinear (A a)
  VProd fs -> any (containsLinear . V . snd) fs
  VSum ts -> any (containsLinear . V . snd) ts
  VExists _ b -> containsLinear (V b)
  VUnit -> False
  VRaw _ -> False
  VReuse _ _ _ -> True
  VCtx _ _ _ -> False
  VCell _ _ -> True
containsLinear (A a) = case a of
  ABox v -> containsLinear (V v)
  AScalar _ -> False
  ASum ts -> any (containsLinear . A . snd) ts
  AForall _ b -> containsLinear (A b)
  ALam _ b -> containsLinear (A b)
  ALazy l b -> containsLinear (A l) || containsLinear (A b)
  AMu _ _ b ts -> any (containsLinear . A) (b : ts)
  ACon _ ts -> any (containsLinear . A) ts
  AApp _ ts -> any (containsLinear . A) ts
  AVar _ -> False
  AFun _ _ -> False
  AUnit -> False

-- the name under which the type of the hole is bound in the one-hole value of a context
nameHole :: Path
nameHole = root (newHiddenName "hole")

-- the one-hole values `K` of `[ctx]`: the hole occurs once, in a field of a block that `K`
-- allocates, or `K` is the hole itself (the empty context)
isCtxValue :: VVal -> Bool
isCtxValue k
  = holes k == 1 && (k == Hole || path k)
  where
    path v = case v of
               Ptr _ a -> block a
               _ -> False
    block a = case a of
                Roll _ b -> block b
                InjA _ _ b -> block b
                InjLazy _ _ b -> block b
                Box v -> field v
                BoxAt _ v -> field v
                _ -> False
    field v = case v of
                Hole -> True
                Tuple ws -> any field [w | w <- ws, holes w == 1]
                _ -> path v

-- the occurrences of the hole, except in nested contexts and closures (which do not bind it)
holes :: VVal -> Int
holes = getSum . holesV
  where
    holesV v = case v of
                 Hole -> Sum 1
                 Context _ _ -> Sum 0
                 _ -> getConst (descendV (Const . holesA) (Const . holesV) v)
    holesA a = case a of
                 Lam{} -> Sum 0
                 _ -> getConst (descendA (const (Const (Sum 0))) (Const . holesA) (Const . holesV) a)

-- the product of values (`Types.prodV`)
prodVal :: [VVal] -> VVal
prodVal []  = UnitV
prodVal [v] = v
prodVal vs  = Tuple vs

tapp :: VVal -> [AType] -> VVal
tapp v []  = v
tapp v tys = TyApp v tys

injA :: [AType] -> Int -> AVal -> AVal
injA [_] 0 v = v
injA ss i v = InjA (fst (sumAlts ss !! i)) (sumOf ss) v

-- a case on each alternative of a boxed sum `a`; the branch gets the alternative, a variable at a
-- boxed type that it may only destructure. `cons` are the constructors of the alternatives.
caseSum :: MonadFail m => [Con] -> [AType] -> Path -> (Int -> Path -> m VExpr) -> m VExpr
caseSum cons shapes a branch
  = case shapes of
      [] -> fail "empty case"
      [_] -> branch 0 a
      _ -> do alts <- mapM (\i -> do let tag = fst (sumAlts shapes !! i)
                                         y = child a (SInjA tag (cons !! i))
                                     e <- branch i y
                                     return (tag,y,e)) [0 .. length shapes - 1]
              return (CaseA Owned a alts Nothing)

-- `[unbox-ru]` and `[lock]` of a box `z` take its contents out of its block and bind its
-- block as a new root: the box, the root and the body
takesContents :: VExpr -> Maybe (Path,Path,VExpr)
takesContents expr
  = case expr of
      UnboxRu z r e -> Just (z,r,e)
      Lock z c e -> Just (z,c,e)
      _ -> Nothing

-- the variable that a destructuring form destructures
scrutVar :: VExpr -> Maybe Path
scrutVar expr
  = case expr of
      _ | Just (z,_,_) <- takesContents expr -> Just z
        | Just ds <- destructAOf expr -> Just (dsScrut ds)
        | Just ds <- destructVOf expr, Var z <- dsScrut ds -> Just z
        | otherwise -> Nothing

-- the arguments of each jump to a join point; jumps are never inside values, and an inner
-- join of the same name shadows it
jumpArgs :: Name -> VExpr -> [[VVal]]
jumpArgs j expr
  = case expr of
      Jump k _ vs | k == j -> [vs]
      Join k _ _ e1 _ | k == j -> jumpArgs j e1
      _ -> getConst (descendE (const (Const [])) (const (Const [])) (\_ e -> Const (jumpArgs j e)) expr)

-- a top-level value, possibly instantiated (`[dup-glob]`)
isGlob :: VVal -> Bool
isGlob v
  = case v of
      Glob _ _ -> True
      TyApp w _ -> isGlob w
      _ -> False

-- free variables

fvA :: AVal -> S.Set Path
fvA val
  = case val of
      Lam ps _ e -> fvE e `S.difference` S.fromList [x | (x,_,_) <- ps]
      _ -> getConst (descendA (Const . S.singleton) (Const . fvA) (Const . fvV) val)

fvV :: VVal -> S.Set Path
fvV val
  = case val of
      Var x -> S.singleton x
      _ -> getConst (descendV (Const . fvA) (Const . fvV) val)

fvE :: VExpr -> S.Set Path
fvE expr = getConst (descendE (Const . S.singleton) (Const . fvV) (\xs e -> Const (fvE e `S.difference` S.fromList xs)) expr)

-- all bound variables (with repetitions)
bindersE :: VExpr -> [Path]
bindersE = getConst . descendE (const (Const [])) (Const . bindersV) (\xs e -> Const (xs ++ bindersE e))

bindersA :: AVal -> [Path]
bindersA val
  = case val of
      Lam ps _ e -> [x | (x,_,_) <- ps] ++ bindersE e
      _ -> getConst (descendA (const (Const [])) (Const . bindersA) (Const . bindersV) val)

bindersV :: VVal -> [Path]
bindersV = getConst . descendV (Const . bindersA) (Const . bindersV)

-- destructuring forms: the mode, the scrutinee, the alternatives with their binders, and a rebuild function.
-- Boxed scrutinees are names; unboxed scrutinees are values.
data Destruct v = Destruct{ dsMode :: Mode, dsScrut :: v, dsAlts :: [([Path],VExpr)], dsBuild :: Mode -> v -> [VExpr] -> VExpr }

destructAOf :: VExpr -> Maybe (Destruct Path)
destructAOf expr
  = case expr of
      SplitA m v k (x,e1) (y,e2) -> Just (Destruct m v [([x],e1),([y],e2)]
                                      (\m' v' es -> SplitA m' v' k (x,head es) (y,last es)))
      IfWhnf m v (x,e1) (y,e2) -> Just (Destruct m v [([x],e1),([y],e2)]
                                    (\m' v' es -> IfWhnf m' v' (x,head es) (y,last es)))
      CaseA m v alts def -> Just (Destruct m v ([([x],e) | (_,x,e) <- alts] ++ maybe [] (\(x,e) -> [([x],e)]) def)
                                  (\m' v' es -> CaseA m' v' [(i,x,e) | ((i,x,_),e) <- zip alts es]
                                    (fmap (\(x,_) -> (x,last es)) def)))
      Unroll m v x e        -> Just (Destruct m v [([x],e)] (\m' v' es -> Unroll m' v' x (head es)))
      Unbox m v x e         -> Just (Destruct m v [([x],e)] (\m' v' es -> Unbox m' v' x (head es)))
      Unscalar m v x e      -> Just (Destruct m v [([x],e)] (\m' v' es -> Unscalar m' v' x (head es)))
      CaseOpen m v alts def -> Just (Destruct m v ([(xs,e) | (_,xs,e) <- alts] ++ [([],def)])
                                       (\m' v' es -> CaseOpen m' v' [(c,xs,e) | ((c,xs,_),e) <- zip alts es] (last es)))
      Proj{} -> Nothing
      CaseV{} -> Nothing
      Deref{} -> Nothing
      Unpack{} -> Nothing
      Ret{} -> Nothing
      Let{} -> Nothing
      LetYield{} -> Nothing
      Yielded{} -> Nothing
      Unreachable{} -> Nothing
      Call{} -> Nothing
      App{} -> Nothing
      CaseLit{} -> Nothing
      Gen{} -> Nothing
      Dup{} -> Nothing
      Drop{} -> Nothing
      Free{} -> Nothing
      IsUnique{} -> Nothing
      IfFull{} -> Nothing
      UnboxRu{} -> Nothing
      CopyRu{} -> Nothing
      Lock{} -> Nothing
      Join{} -> Nothing
      Jump{} -> Nothing

destructVOf :: VExpr -> Maybe (Destruct VVal)
destructVOf expr
  = case expr of
      SplitA{} -> Nothing
      Proj m v i x e        -> Just (Destruct m v [([x],e)] (\m' v' es -> Proj m' v' i x (head es)))
      CaseV m v alts        -> Just (Destruct m v [([x],e) | (_,x,e) <- alts] (\m' v' es -> CaseV m' v' [(i,x,e) | ((i,x,_),e) <- zip alts es]))
      Deref m v x e         -> Just (Destruct m v [([x],e)] (\m' v' es -> Deref m' v' x (head es)))
      Unpack m v tvs x e    -> Just (Destruct m v [([x],e)] (\m' v' es -> Unpack m' v' tvs x (head es)))
      CaseA{} -> Nothing
      Unroll{} -> Nothing
      Unbox{} -> Nothing
      Unscalar{} -> Nothing
      CaseOpen{} -> Nothing
      Ret{} -> Nothing
      Let{} -> Nothing
      LetYield{} -> Nothing
      Yielded{} -> Nothing
      Unreachable{} -> Nothing
      Call{} -> Nothing
      App{} -> Nothing
      CaseLit{} -> Nothing
      Gen{} -> Nothing
      Dup{} -> Nothing
      Drop{} -> Nothing
      Free{} -> Nothing
      IsUnique{} -> Nothing
      IfWhnf{} -> Nothing
      IfFull{} -> Nothing
      UnboxRu{} -> Nothing
      CopyRu{} -> Nothing
      Lock{} -> Nothing
      Join{} -> Nothing
      Jump{} -> Nothing

-- reading the contents of a box never moves them
isRead :: VExpr -> Bool
isRead expr
  = case expr of
      SplitA{}    -> False
      Unbox{}     -> True
      Unscalar{}  -> False
      CaseOpen{}  -> True
      Proj{}      -> False
      CaseV{}     -> False
      CaseA{}     -> False
      Deref{}     -> False
      Unroll{}    -> False
      Unpack{}    -> False
      Ret{}       -> False
      Let{}       -> False
      LetYield{}  -> False
      Yielded{}   -> False
      Unreachable{} -> False
      Call{}      -> False
      App{}       -> False
      CaseLit{}   -> False
      Gen{}       -> False
      Dup{}       -> False
      Drop{}      -> False
      Free{}      -> False
      IsUnique{}  -> False
      IfWhnf{}    -> False
      IfFull{}    -> False
      UnboxRu{}   -> False
      CopyRu{}    -> False
      Lock{}      -> False
      Join{}      -> False
      Jump{}      -> False

-- the binders of these destructuring forms are the scrutinee's pointer (the scrutinee itself
-- for `[unpack]`), so they may be unique
keepsPointer :: VExpr -> Bool
keepsPointer expr
  = case expr of
      SplitA{}    -> True
      IfWhnf{}    -> True
      CaseA{}     -> True
      Deref{}     -> True
      Unroll{}    -> True
      Unpack{}    -> True
      Proj{}      -> False
      CaseV{}     -> False
      Unbox{}     -> False
      Unscalar{}  -> False
      CaseOpen{}  -> False
      Ret{}       -> False
      Let{}       -> False
      LetYield{}  -> False
      Yielded{}   -> False
      Unreachable{} -> False
      Call{}      -> False
      App{}       -> False
      CaseLit{}   -> False
      Gen{}       -> False
      Dup{}       -> False
      Drop{}      -> False
      Free{}      -> False
      IsUnique{}  -> False
      IfFull{}    -> False
      UnboxRu{}   -> False
      CopyRu{}    -> False
      Lock{}      -> False
      Join{}      -> False
      Jump{}      -> False

-- Where a variable gets the bits of another variable: a copy (`[dup]`) gets those
-- of its variable, and a parameter of a join point those of its arguments.
data Source = Copy Path | Param [VVal]

type Sources = M.Map Path Source

sources :: VExpr -> Sources
sources expr = M.union here (getConst (descendE (const (Const M.empty)) (Const . sourcesV) (\_ e -> Const (sources e)) expr))
  where
    here = case expr of
             Dup x y _ -> M.singleton y (Copy x)
             Join j _ ps _ e2 -> M.fromList [(y,Param [vs !! i | vs <- jumpArgs j e2]) | (i,(y,_,_)) <- zip [0..] ps]
             _ -> M.empty
    sourcesV = getConst . descendV (Const . sourcesA) (Const . sourcesV)
    sourcesA a = case a of
                   Lam _ _ e -> sources e
                   _ -> getConst (descendA (const (Const M.empty)) (Const . sourcesA) (Const . sourcesV) a)

-- The variable whose bits a variable has, through the longest prefix of its path that has a
-- source: a join parameter has the bits of its arguments if they are the same.
sameBits :: Sources -> Path -> Path
sameBits src x@(Path r ss)
  = case [(k,s) | k <- [length ss, length ss - 1 .. 0], Just s <- [M.lookup (Path r (take k ss)) src]] of
      ((k,s):_) -> case s of
                     Copy y -> sameBits src (extend y (drop k ss))
                     Param vs | Just (y:ys) <- mapM sameOf vs, all (== y) ys -> extend y (drop k ss)
                     _ -> x
      [] -> x
  where
    extend (Path y ts) rest = Path y (ts ++ rest)
    sameOf (Var y) = Just (sameBits src y)
    sameOf _ = Nothing

sameBitsV :: Sources -> VVal -> VVal
sameBitsV src v
  = case v of
      Var x -> Var (sameBits src x)
      _ -> mapV id (sameBitsV src) v

-- All the types that a program mentions.
programTypes :: Program -> [VType]
programTypes prog = concatMap sig (M.elems (progSigs prog)) ++ concatMap def (progDefs prog)
                    ++ concatMap (\d -> vars (tdefParams d) ++ maybe [] at (tdefBody d)) (M.elems (progTypes prog))
  where
    vars = map (VPtr . AVar)
    sig s = case s of
      SigFun vs ps r -> vars vs ++ (r : map snd ps)
      SigVal vs t -> vars vs ++ [t]
      SigCon vs ts _ -> vars vs ++ ts
    def d = case d of
      DefFun _ vs ps r e -> vars vs ++ (r : map (\(_,_,t) -> t) ps ++ et e)
      DefVal _ vs t e -> vars vs ++ (t : et e)
    at a = case a of
      ABox t -> [t]
      ASum ts -> concatMap (at . snd) ts
      AFun ps r -> r : map snd ps
      AForall _ b -> at b
      ALam _ b -> at b
      ALazy l b -> at l ++ at b
      AMu _ _ b ts -> concatMap at (b : ts)
      ACon _ ts -> concatMap at ts
      AApp _ ts -> concatMap at ts
      _ -> []
    et e = here ++ getConst (descendE (const (Const [])) (Const . vt) (\_ b -> Const (et b)) e)
      where here = case e of
                     Let _ t _ _ -> [t]
                     LetYield _ t _ _ _ -> [t]
                     Yielded t -> [t]
                     Unreachable t -> [t]
                     Join _ _ ps _ _ -> map (\(_,_,t) -> t) ps
                     Jump _ ts _ -> concatMap at ts
                     Call _ ts _ -> concatMap at ts
                     Gen vs _ -> map (VPtr . AVar) vs
                     Unpack _ _ vs _ _ -> map (VPtr . AVar) vs
                     _ -> []
    vt v = here ++ getConst (descendV (Const . avTypes) (Const . vt) v)
      where here = case v of
                     Glob _ ts -> concatMap at ts
                     TyApp _ ts -> concatMap at ts
                     Context a _ -> at a
                     Ptr a _ -> at a
                     Inj _ t _ -> [t]
                     Pack t ts _ -> t : concatMap at ts
                     NoReuse _ p -> maybe [] (\(Contents _ _ t) -> [t]) p
                     _ -> []
    avTypes a = case a of
      Lam ps r e -> r : map (\(_,_,t) -> t) ps ++ et e
      Roll t w -> at t ++ avTypes w
      InjA _ t w -> at t ++ avTypes w
      InjLazy _ t w -> at t ++ avTypes w
      OpenCon _ ts ws -> concatMap at ts ++ concatMap vt ws
      _ -> getConst (descendA (const (Const [])) (Const . avTypes) (Const . vt) a)

-- The `lazy-C` functions with the tag of their constructor, the size of its cell and its
-- fields (with the padding, see `Elab.TypeInfo.conFieldTypes`), the
-- `lazy-eval-locked` functions, and the tag of the indirection ι of each lazy type.
data Lazies = Lazies{ lzCons :: M.Map Name (Int,Int,[VType]), lzLocked :: S.Set Name
                    , lzIndirect :: M.Map Name Int }

-- the values of the fields of a constructor `fields`, followed by those of its padding
padFields :: [VType] -> [VVal] -> [VVal]
padFields fields vs = vs ++ [Lit (LitChar '\0') | _ <- drop (length vs) fields]
