-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- The typed intermediate language.

  Each syntactic form below carries its typing rule as a comment. The rules follow the FIP
  calculus with unboxed types (fiplazy, "FIP Core Calculus" and its extensions to Perceus and
  unboxed sums), with the changes recorded in FINDINGS.md, and are labelled with their name in
  the paper. `Check` checks the types and `Linear` the modes (after Perceus). Keep the rules and
  the checkers in sync: a change to one must be reflected in the other.

  Contexts and judgements

    Γ ::= ∅ | Γ, x :q t                         variables
    J ::= ∅ | J, j : (q̄ V̄) -> t                 join points in scope
    Σ                                          signatures (`Sigs`)

    Γ ⊢ v :q t       the value v has type t; an owned value consumes Γ
    Γ | J ⊢ e : t    the expression e has type t and consumes every owned variable of Γ
    ⊢ def            a top-level definition is well-typed

    `^Γ` marks every variable of Γ as borrowed. J is passed unchanged to every subexpression in
    tail position and omitted from the rules where that is all that happens; it is reset to ∅
    where an expression is not in tail position.

  Structural rules

         Γ | J ⊢ e : t                       Γ, x :^ t, x :^ t | J ⊢ e : t
    ─────────────────────── [weaken]       ─────────────────────────────── [contract]
     Γ, x :^ t | J ⊢ e : t                   Γ, x :^ t | J ⊢ e : t

    - Variables of a trivial type are unrestricted: they may be weakened and contracted at either
      mode, and used owned or borrowed. They need no `dup` or `drop`. (Not in the paper.)
    - A unique variable `x :! t` is owned and holds the only reference to its block. It may be used
      as an owned one. Any borrowed use of `x`, or of a variable borrowed from `x`, may duplicate the
      reference and demotes it to `x : t`; branches agree on the weaker status.
    - The paper scopes borrowing syntactically: `[let]` lends `^Γ₂` to the bound expression.
      Our IR borrows from an owned variable `z` anywhere (e.g. `case^ z` with `z` owned, as Perceus
      produces), and the binders are *borrowed from* `z`: they become invalid once `z` is consumed.
      In particular a borrowed argument of a call cannot be one that is passed owned.
    - The binder of a borrowed `[case]`, `[unfold]` or `[unpack]` at a boxed type `A` is an *alias*
      of the owned `z` (or of the owned variable that an alias is borrowed from): it is `z`'s
      pointer. Consuming an alias, or testing it with `[if-unique]`, consumes `z` and makes the
      alias owned (unique if `z` was); the variables borrowed from `z` are then borrowed from it.
-}
module Backend.Typed.Syntax where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Common.Name

-- Types. Type variables are pointer-sized: they are only instantiated with pointer-sized types
-- (elaboration uses `boxrep(W)`, Koka's `box`), and so are the variables of `∃` and `λ`.
type TVar = Int

-- modes q ::= · | ! | ^  (owned, unique, borrowed)
data Mode = Owned | Unique | Borrowed
          deriving (Eq,Show)

-- a unique value is also owned
owning :: Mode -> Bool
owning m
  = case m of
      Owned    -> True
      Unique   -> True
      Borrowed -> False

-- boxed types A, B: a pointer whose tag is (partly) known, or a function
data AType = ABox VType                 -- Box V
           | AUnit                      -- 1
           | ASum AType AType           -- A + B, binary and right-nested
           | AFun [(Mode,VType)] VType  -- (q̄ V̄) -> W, for top-level functions and closures alike
           | AForall [TVar] AType       -- ∀ā. A
           deriving (Eq,Show)

-- unboxed types V, W: values of a fixed size without a header.
--
-- - `a`, `a⟨W̄⟩`, `T⟨W̄⟩`, `A*` and `λā.V` are pointer-sized (`Types.isPtr`).
-- - Types are equal up to renaming of bound variables, and applying a variable instantiated with
--   a type lambda gives its boxed representation: `a⟨W̄⟩[λb̄.V / a] = boxrep(V[W̄/b̄])`.
-- - A type is trivial (`Check.isTrivial`) if it contains no pointers: `𝟙`, raw types, `1`, sums,
--   products and existentials of trivial types, and the named types `@field-addr` and `@reuse`.
-- - `unfold(T⟨W̄⟩) = A[W̄/ā]` for a definition `T⟨ā⟩ := A` (`TypeDef`), and `unfold(A*) = A`.
-- - `|V|` is the size of the heap block of a `Box V` (`Layout.blockSize`); it is only defined when
--   the payload is always a heap block (`Layout.isBlock`).
data VType = VVar TVar                  -- a
           | VApp TVar [VType]          -- a⟨W̄⟩, an applied higher-kinded variable
           | VCon Name [VType]          -- T⟨W̄⟩, a named type; replaces μa.A
           | VPtr AType                 -- A* = μa.A (a fresh)
           | VUnit                      -- 𝟙
           | VSum [VType]               -- ⊕ᵢ Vᵢ, n-ary (a Koka value type with several constructors)
           | VProd VType VType          -- V ⊗ W
           | VRaw Name                  -- raw: unboxed primitives (`int32`, `float64`, `char`, ...)
           | VExists [TVar] VType       -- ∃ā. V
           | VTLam [TVar] VType         -- λā. V, a partially applied value type
           | VReuse Int                 -- ◇n, a reuse credit for a heap block of n bytes
           deriving (Eq,Show)

-- t ::= A | V
data Ty = A AType | V VType
          deriving (Eq,Show)

-- a named type `T⟨ā⟩ := A`; without a body (`int`, `string`, ...) it cannot be unfolded
data TypeDef = TypeDef{ tdefName :: Name, tdefParams :: [TVar], tdefBody :: Maybe AType, tdefLazy :: Maybe LazyInfo }
             deriving (Show)

-- lazy datatypes: the index of the indirection constructor, and for each constructor
-- whether it is lazy and Koka's allocation size (Koka decides by these sizes when to memoize in place)
data LazyInfo = LazyInfo{ lazyIndirect :: Int, lazyCons :: [(Bool,Int)] }
              deriving (Show)

type TypeDefs = M.Map Name TypeDef

-- the type of a literal, `type(l)`: `int` and `string` are named types, `char` and `float64` raw
-- (see `Check.litType`)
data Lit = LitInt Integer
         | LitFloat Double
         | LitChar Char
         | LitString String
         deriving (Eq,Show)

-- Values `Γ ⊢ v :q t`. A borrowed value is an atom: a variable, a global, a literal, `()`, a
-- function, or a type application of one of these. A unique value is a variable. All other values
-- are owned. (The paper also allows borrowed pairs and injections.)
data Val
  --  ───────────────── [var]
  --   x :q t ⊢ x :q t
  = Var Name

  --   f : ∀ā. (q̄ V̄) -> W ∈ Σ    q̄ = ·
  --  ──────────────────────────────── [fun]
  --   ∅ ⊢ f :q ∀ā. (q̄ V̄) -> W
  --
  -- A top-level function used as a value is a static closure and can be used at either mode.
  -- Only functions with owned parameters can be used as closures (see `[app]`).
  | Fun Name

  --   x : ∀ā. V ∈ Σ    W̄ pointer-sized
  --  ─────────────────────────────────── [glob]
  --   ∅ ⊢ x[W̄] :^ V[W̄/ā]
  --
  -- A top-level value is borrowed: an owned use needs a `dup` (unless its type is trivial).
  | Glob Name [VType]

  --  ────────────── [unit]    ────────────── [unit]
  --   ∅ ⊢ () : 𝟙                ∅ ⊢ () : 1
  | Unit

  --  ──────────────────── [lit]
  --   ∅ ⊢ l : type(l)
  | Lit Lit

  --   Γ ⊢ v : Vᵢ
  --  ─────────────────────── [inj]
  --   Γ ⊢ injᵢ v : ⊕ⱼ Vⱼ
  | Inj Int VType Val

  --   Γ ⊢ v : A
  --  ──────────────────── [inl]
  --   Γ ⊢ inl v : A + B
  | Inl AType Val

  --   Γ ⊢ v : B
  --  ──────────────────── [inr]
  --   Γ ⊢ inr v : A + B
  | Inr AType Val

  --   Γ₁ ⊢ v₁ : V₁    Γ₂ ⊢ v₂ : V₂
  --  ────────────────────────────────── [pair]
  --   Γ₁, Γ₂ ⊢ (v₁, v₂) : V₁ ⊗ V₂
  | Pair Val Val

  --   Γ ⊢ v : unfold(V)
  --  ──────────────────── [fold]
  --   Γ ⊢ fold v : V
  | Fold VType Val

  --   Γ ⊢ v : V
  --  ──────────────────── [box]
  --   Γ ⊢ box v : Box V
  --
  -- A fresh allocation: the paper's `alloc_n; box v`.
  | Box Val

  --   Γ ⊢ v : V[W̄/ā]    W̄ pointer-sized
  --  ───────────────────────────────────── [pack]
  --   Γ ⊢ pack[W̄] v : ∃ā. V
  | Pack VType [VType] Val

  --   C : ∀ā. V -> W ∈ Σ    Γ ⊢ v : V[W̄/ā]    W̄ pointer-sized
  --  ──────────────────────────────────────────────────────── [open-con]
  --   Γ ⊢ C[W̄] v : W[W̄/ā]
  --
  -- A constructor of an open datatype (whose constructors are spread over modules).
  | OpenCon Name [VType] Val

  --   ⌊Γ⌋, x̄ : V̄ | ∅ ⊢ e : W    q̄ = ·
  --  ───────────────────────────────────────── [lam]
  --   Γ ⊢ fn(x̄ :q̄ V̄) : W -> e : (q̄ V̄) -> W
  --
  -- A closure consumes its captures Γ, which are owned in its body (`⌊Γ⌋`). Closures have the
  -- same arrow type as top-level functions, but only owned parameters.
  | Lam [(Name,Mode,VType)] VType Expr

  --   Γ ⊢ v :q ∀ā. A    W̄ pointer-sized
  --  ─────────────────────────────────── [tyapp]
  --   Γ ⊢ v[W̄] :q A[W̄/ā]
  --
  -- Replaces the paper's `[inst]`, which breaks the memory layout at other types.
  | TyApp Val [VType]

  --   Γ ⊢ v :^ t
  --  ──────────────── [dup]
  --   Γ ⊢ dup v : t
  | Dup Val

  --   Γ ⊢ v : V    |V| = n
  --  ────────────────────────────── [box-at]
  --   Γ, r : ◇n ⊢ box@r v : Box V
  --
  -- A box allocated in the block of a reuse credit, or freshly if the credit is empty (the
  -- paper's `[box]`, where the credit is anonymous).
  | BoxAt Name Val

  --   Γ ⊢ v : V    T⟨ā⟩ := A is lazy    Box V is an alternative of A[W̄/ā]
  --  ────────────────────────────────────────────────────────────────────── [box-in]
  --   Γ, x : T⟨W̄⟩ ⊢ box-in@x v : Box V
  --
  -- A box written over the block of the lazy value `x` under evaluation, keeping its reference
  -- count (`Lazy`). It is an update through a shared reference and only sound because `x` is
  -- locked and its old fields (taken by `[unbox-lazy]`) are not used again.
  | BoxIn Name Val

  --  ────────────────────── [no-reuse]
  --   ∅ ⊢ no-reuse n : ◇n
  --
  -- The empty credit: an allocation in it is fresh. Passed by a jump that has no credit for a
  -- parameter of its join point.
  | NoReuse Int
  deriving (Show)

-- Expressions `Γ | J ⊢ e : t`
data Expr
  --   Γ ⊢ v : t
  --  ──────────────────── [ret]
  --   Γ ⊢ ret v : t
  = Ret Val

  --   Γ₁, ^Γ₂ | ∅ ⊢ e₁ : t₁    Γ₂, x : t₁ | J ⊢ e₂ : t
  --  ─────────────────────────────────────────────────── [let]
  --   Γ₁, Γ₂ | J ⊢ let x : t₁ = e₁ in e₂ : t
  | Let Name Ty Expr Expr

  --   f : ∀ā. (q̄ V̄) -> W ∈ Σ    W̄ pointer-sized    Γᵢ ⊢ vᵢ :qᵢ Vᵢ[W̄/ā]
  --  ───────────────────────────────────────────────────────────────────── [call]
  --   Γ₁, ..., Γₙ ⊢ f[W̄](v₁, ..., vₙ) : W[W̄/ā]
  --
  -- Elaboration only gives our own functions owned parameters; borrowed parameters only occur
  -- for externals.
  | Call Name [VType] [Val]

  --   Γ₀ ⊢ v : (V̄) -> W    Γᵢ ⊢ vᵢ : Vᵢ
  --  ──────────────────────────────────────── [app]
  --   Γ₀, Γ₁, ..., Γₙ ⊢ v(v₁, ..., vₙ) : W
  --
  -- Applying a closure consumes it, and all its parameters are owned (no `[bapp]`).
  | App Val [Val]

  -- Destructuring takes a mode: owned destructuring consumes the scrutinee and its binders are
  -- owned (a move); borrowed destructuring gives binders borrowed from the scrutinee. Unique
  -- destructuring consumes a unique scrutinee and its binders are unique; it is only allowed
  -- where the binder is the scrutinee's pointer: `[case]` on `A + B`, `[unfold]` and `[unpack]`
  -- (`keepsPointer`).
  --
  --   Γ₁ ⊢ v :q V₁ ⊗ V₂    Γ₂, x :q V₁, y :q V₂ ⊢ e : t
  --  ──────────────────────────────────────────────────── [unpair]
  --   Γ₁, Γ₂ ⊢ let_q (x, y) = v in e : t
  | Unpair Mode Val Name Name Expr

  --   Γ₁ ⊢ v :q ⊕ᵢ Vᵢ    Γ₂, xᵢ :q Vᵢ ⊢ eᵢ : t   (for each i)
  --  ────────────────────────────────────────────────────────── [case]
  --   Γ₁, Γ₂ ⊢ case_q v of { injᵢ xᵢ -> eᵢ } : t
  | CaseV Mode Val [(Name,Expr)]

  --   Γ₁ ⊢ v :q A + B    Γ₂, x :q A ⊢ e₁ : t    Γ₂, y :q B ⊢ e₂ : t
  --  ──────────────────────────────────────────────────────────────── [case]
  --   Γ₁, Γ₂ ⊢ case_q v of { inl x -> e₁; inr y -> e₂ } : t
  | CaseA Mode Val (Name,Expr) (Name,Expr)

  --   Γ₁ ⊢ v :q V    Γ₂, x :q unfold(V) ⊢ e : t
  --  ──────────────────────────────────────────── [unfold]
  --   Γ₁, Γ₂ ⊢ let_q fold x = v in e : t
  | Unfold Mode Val Name Expr

  --   Γ₁ ⊢ v :^ Box V    Γ₂, x :^ V ⊢ e : t
  --  ──────────────────────────────────────── [bunbox]
  --   Γ₁, Γ₂ ⊢ let^ box x = v in e : t
  --
  -- Reading the contents of a box is always borrowed. The paper's owned `[unbox]`, which keeps
  -- the block as a credit, is `[unbox-ru]` and requires the box to be unique.
  | Unbox Mode Val Name Expr

  --   Γ₁ ⊢ v :^ Box V    Γ₂, x : V ⊢ e : t
  --  ─────────────────────────────────────────── [unbox-lazy]
  --   Γ₁, Γ₂ ⊢ let-lazy box x = v in e : t
  --
  -- Takes the contents of a box of the lazy value under evaluation without duplicating them
  -- (`Perceus`); the box is left *hollow* until `[box-in]` writes over it or it is freed. In the
  -- calculus this needs a hollow box type (a shared `◇n`). Trusted by `Linear`.
  | UnboxLazy Val Name Expr

  --   Γ₁ ⊢ v :q ∃ā. V    Γ₂, x :q V[b̄/ā] ⊢ e : t    b̄ ∉ ftv(Γ₂, t)
  --  ────────────────────────────────────────────────────────────────── [unpack]
  --   Γ₁, Γ₂ ⊢ let_q pack[b̄] x = v in e : t
  | Unpack Mode Val [TVar] Name Expr

  --   Γ₁ ⊢ v :^ V    lᵢ : V    Γ₂ ⊢ eᵢ : t    Γ₂ ⊢ e : t
  --  ────────────────────────────────────────────────────── [case-lit]
  --   Γ₁, Γ₂ ⊢ case v of { lᵢ -> eᵢ; _ -> e } : t
  | CaseLit Val [(Lit,Expr)] Expr

  --   Γ₁ ⊢ v :^ T    Cᵢ : ∀ā. Vᵢ -> W ∈ Σ    W[W̄ᵢ/ā] = T
  --   Γ₂, xᵢ :^ Vᵢ[W̄ᵢ/ā] ⊢ eᵢ : t    Γ₂ ⊢ e : t
  --  ─────────────────────────────────────────────────── [case-open]
  --   Γ₁, Γ₂ ⊢ case^ v of { Cᵢ xᵢ -> eᵢ; _ -> e } : t
  --
  -- Matching on the tag of an open datatype, with a mandatory default. Always borrowed.
  | CaseOpen Mode Val [(Name,Name,Expr)] Expr

  --   Γ | ∅ ⊢ e : A*    ā ∉ ftv(Γ)
  --  ─────────────────────────────────── [gen]
  --   Γ | J ⊢ gen ā. e : (∀ā. A)*
  --
  -- An expression form (Koka has no value restriction); sound because the result is
  -- pointer-sized and type-erased.
  | Gen [TVar] Expr

  --       Γ ⊢ e : t
  --  ─────────────────────────── [drop]
  --   Γ, x : t' ⊢ drop x; e : t
  --
  -- Dropping a credit frees its block (the paper's `[free]`).
  | Drop Name Expr

  --   Γ, r : ◇n ⊢ e : t    |V| = n
  --  ─────────────────────────────────────────────── [dropru]
  --   Γ, x : Box V ⊢ let r = drop-reuse x in e : t
  --
  -- Drops a box and keeps its block as the credit `r` if it was unique, and else gives the empty
  -- credit.
  | DropRu Name Name Expr

  --   Γ, x :! Box V ⊢ e₁ : t    Γ, x : Box V ⊢ e₂ : t    |V| defined
  --  ──────────────────────────────────────────────────────────────── [if-unique]
  --   Γ, x : Box V ⊢ if-unique x then e₁ else e₂ : t
  --
  -- Branches on whether a box is unique (`DropSpec`).
  | IsUnique Name Expr Expr

  --   Γ, x : V, r : ◇n ⊢ e : t    |V| = n
  --  ─────────────────────────────────────────────── [unbox-ru]
  --   Γ, z :! Box V ⊢ let box x @ r = z in e : t
  --
  -- A unique `Box V` splits into its contents and its block, the inverse of `[box-at]`. With
  -- `[if-unique]` it makes `drop` and `drop-reuse` of a box derivable.
  | UnboxRu Val Name Name Expr

  --   x̄ :q̄ V̄ | ∅ ⊢ e₁ : t    Γ | J, j : (q̄ V̄) -> t ⊢ e₂ : t
  --  ──────────────────────────────────────────────────────── [join]
  --   Γ | J ⊢ join j(x̄ :q̄ V̄) = e₁ in e₂ : t
  --
  -- A join point is closed (only its parameters are free in its body) and not recursive (`j` is
  -- not in scope in its body). Since J is reset outside of tail positions, a jump cannot escape
  -- and is always a tail call. Perceus only produces owned parameters.
  | Join Name [(Name,Mode,VType)] Expr Expr

  --   j : (q̄ V̄) -> t ∈ J    Γᵢ ⊢ vᵢ :qᵢ Vᵢ
  --  ─────────────────────────────────────── [jump]
  --   Γ₁, ..., Γₙ | J ⊢ jump j(v₁, ..., vₙ) : t
  | Jump Name [Val]
  deriving (Show)

-- Definitions `⊢ def`, with `f : ∀ā. (q̄ V̄) -> W ∈ Σ` and `x : ∀ā. V ∈ Σ`
data Def
  --   x̄ :q̄ V̄ | ∅ ⊢ e : W
  --  ──────────────────────────────── [deffun]
  --   ⊢ fun f⟨ā⟩(x̄ :q̄ V̄) : W = e
  = DefFun{ defName :: Name, defParams :: [TVar], defArgs :: [(Name,Mode,VType)], defRes :: VType, defBody :: Expr }

  --   ∅ | ∅ ⊢ e : V
  --  ───────────────────────── [defval]
  --   ⊢ val x⟨ā⟩ : V = e
  --
  -- A top-level value, initialized when the module is loaded. It can be polymorphic over
  -- (pointer-sized) unboxed types.
  | DefVal{ defName :: Name, defParams :: [TVar], defType :: VType, defBody :: Expr }
  deriving (Show)

-- signatures Σ
data Sig = SigFun [TVar] [(Mode,VType)] VType  -- f : ∀ā. (q̄ V̄) -> W
         | SigVal [TVar] VType                 -- x : ∀ā. V
         | SigCon [TVar] VType VType           -- C : ∀ā. V -> W, an open constructor
         deriving (Show)

type Sigs = M.Map Name Sig

data Program = Program{ progName :: Name, progTypes :: TypeDefs, progSigs :: Sigs, progDefs :: [Def] }

-- one-level traversals

-- the values directly inside a value (not under a lambda)
descendV :: Applicative f => (Val -> f Val) -> Val -> f Val
descendV f val
  = case val of
      Inj i t v      -> Inj i t <$> f v
      Inl a v        -> Inl a <$> f v
      Inr a v        -> Inr a <$> f v
      Pair v w       -> Pair <$> f v <*> f w
      Fold t v       -> Fold t <$> f v
      Box v          -> Box <$> f v
      Pack t ts v    -> Pack t ts <$> f v
      OpenCon c ts v -> OpenCon c ts <$> f v
      TyApp v ts     -> (`TyApp` ts) <$> f v
      Dup v          -> Dup <$> f v
      BoxAt r v      -> BoxAt <$> (varOf <$> f (Var r)) <*> f v
      BoxIn x v      -> BoxIn <$> (varOf <$> f (Var x)) <*> f v
      Var _          -> pure val
      Fun _          -> pure val
      Glob _ _       -> pure val
      Unit           -> pure val
      Lit _          -> pure val
      Lam _ _ _      -> pure val
      NoReuse _      -> pure val

childrenV :: Val -> [Val]
childrenV = getConst . descendV (\v -> Const [v])

mapV :: (Val -> Val) -> Val -> Val
mapV f = runIdentity . descendV (Identity . f)

-- the values and the subexpressions of an expression, with the variables bound in each subexpression
descendE :: Applicative f => (Val -> f Val) -> ([Name] -> Expr -> f Expr) -> Expr -> f Expr
descendE fv fe expr
  = case expr of
      Ret v                 -> Ret <$> fv v
      Let x t e1 e2         -> Let x t <$> fe [] e1 <*> fe [x] e2
      Call f ts vs          -> Call f ts <$> traverse fv vs
      App f vs              -> App <$> fv f <*> traverse fv vs
      Unpair m v x y e      -> (\v' -> Unpair m v' x y) <$> fv v <*> fe [x,y] e
      CaseV m v alts        -> CaseV m <$> fv v <*> traverse (\(x,e) -> (,) x <$> fe [x] e) alts
      CaseA m v (x,e1) (y,e2) -> (\v' e1' e2' -> CaseA m v' (x,e1') (y,e2')) <$> fv v <*> fe [x] e1 <*> fe [y] e2
      Unfold m v x e        -> (\v' -> Unfold m v' x) <$> fv v <*> fe [x] e
      Unbox m v x e         -> (\v' -> Unbox m v' x) <$> fv v <*> fe [x] e
      UnboxLazy v x e       -> (\v' -> UnboxLazy v' x) <$> fv v <*> fe [x] e
      Unpack m v tvs x e    -> (\v' -> Unpack m v' tvs x) <$> fv v <*> fe [x] e
      CaseLit v alts def    -> CaseLit <$> fv v <*> traverse (\(l,e) -> (,) l <$> fe [] e) alts <*> fe [] def
      CaseOpen m v alts def -> CaseOpen m <$> fv v <*> traverse (\(c,x,e) -> (,,) c x <$> fe [x] e) alts <*> fe [] def
      Gen tvs e             -> Gen tvs <$> fe [] e
      Drop x e              -> Drop <$> (varOf <$> fv (Var x)) <*> fe [] e
      DropRu x r e          -> (\x' -> DropRu x' r) <$> (varOf <$> fv (Var x)) <*> fe [r] e
      IsUnique x e1 e2      -> IsUnique <$> (varOf <$> fv (Var x)) <*> fe [] e1 <*> fe [] e2
      UnboxRu v x r e       -> (\v' -> UnboxRu v' x r) <$> fv v <*> fe [x,r] e
      Join j ps e1 e2       -> Join j ps <$> fe [x | (x,_,_) <- ps] e1 <*> fe [] e2
      Jump j vs             -> Jump j <$> traverse fv vs

varOf :: Val -> Name
varOf (Var y) = y
varOf v       = error ("Backend.Typed.Syntax.varOf: not a variable: " ++ show v)

-- free variables

fvV :: Val -> S.Set Name
fvV val
  = case val of
      Var x      -> S.singleton x
      Lam ps _ e -> fvE e `S.difference` S.fromList [x | (x,_,_) <- ps]
      _          -> S.unions (map fvV (childrenV val))

fvE :: Expr -> S.Set Name
fvE = getConst . descendE (Const . fvV) (\xs e -> Const (fvE e `S.difference` S.fromList xs))

-- substitution and renaming of free variables (the free variables of the values must not be bound in the scope)

replaceV :: M.Map Name Val -> Val -> Val
replaceV sub val
  = case val of
      Var x      -> M.findWithDefault val x sub
      Lam ps r e -> Lam ps r (replaceE (foldr M.delete sub [x | (x,_,_) <- ps]) e)
      _          -> mapV (replaceV sub) val

replaceE :: M.Map Name Val -> Expr -> Expr
replaceE sub expr
  | M.null sub = expr
  | otherwise  = runIdentity (descendE (Identity . replaceV sub) (\xs e -> Identity (replaceE (foldr M.delete sub xs) e)) expr)

renameV :: M.Map Name Name -> Val -> Val
renameV = replaceV . M.map Var

renameE :: M.Map Name Name -> Expr -> Expr
renameE = replaceE . M.map Var

-- all bound variables (with repetitions)
bindersE :: Expr -> [Name]
bindersE = getConst . descendE (Const . bindersV) (\xs e -> Const (xs ++ bindersE e))

bindersV :: Val -> [Name]
bindersV val
  = case val of
      Lam ps _ e -> [x | (x,_,_) <- ps] ++ bindersE e
      _          -> concatMap bindersV (childrenV val)

-- destructuring forms: the mode, the scrutinee, the alternatives with their binders, and a rebuild function

data Destruct = Destruct{ dsMode :: Mode, dsScrut :: Val, dsAlts :: [([Name],Expr)], dsBuild :: Mode -> Val -> [Expr] -> Expr }

destructOf :: Expr -> Maybe Destruct
destructOf expr
  = case expr of
      Unpair m v x y e      -> Just (Destruct m v [([x,y],e)] (\m' v' es -> Unpair m' v' x y (head es)))
      CaseV m v alts        -> Just (Destruct m v [([x],e) | (x,e) <- alts] (\m' v' es -> CaseV m' v' (zip (map fst alts) es)))
      CaseA m v (x,e1) (y,e2) -> Just (Destruct m v [([x],e1),([y],e2)] (\m' v' es -> CaseA m' v' (x,es !! 0) (y,es !! 1)))
      Unfold m v x e        -> Just (Destruct m v [([x],e)] (\m' v' es -> Unfold m' v' x (head es)))
      Unbox m v x e         -> Just (Destruct m v [([x],e)] (\m' v' es -> Unbox m' v' x (head es)))
      UnboxLazy v x e       -> Just (Destruct Borrowed v [([x],e)] (\_ v' es -> UnboxLazy v' x (head es)))
      Unpack m v tvs x e    -> Just (Destruct m v [([x],e)] (\m' v' es -> Unpack m' v' tvs x (head es)))
      CaseOpen m v alts def -> Just (Destruct m v ([([x],e) | (_,x,e) <- alts] ++ [([],def)])
                                       (\m' v' es -> CaseOpen m' v' [(c,x,e) | ((c,x,_),e) <- zip alts es] (last es)))
      Ret _          -> Nothing
      Let _ _ _ _    -> Nothing
      Call _ _ _     -> Nothing
      App _ _        -> Nothing
      CaseLit _ _ _  -> Nothing
      Gen _ _        -> Nothing
      Drop _ _       -> Nothing
      DropRu _ _ _   -> Nothing
      IsUnique _ _ _ -> Nothing
      UnboxRu _ _ _ _ -> Nothing
      Join _ _ _ _   -> Nothing
      Jump _ _       -> Nothing

-- reading the contents of a box never moves them
isRead :: Expr -> Bool
isRead expr
  = case expr of
      Unbox{}     -> True
      UnboxLazy{} -> True
      CaseOpen{}  -> True
      Unpair{}    -> False
      CaseV{}     -> False
      CaseA{}     -> False
      Unfold{}    -> False
      Unpack{}    -> False
      Ret{}       -> False
      Let{}       -> False
      Call{}      -> False
      App{}       -> False
      CaseLit{}   -> False
      Gen{}       -> False
      Drop{}      -> False
      DropRu{}    -> False
      IsUnique{}  -> False
      UnboxRu{}   -> False
      Join{}      -> False
      Jump{}      -> False

-- the binders of these destructuring forms are the scrutinee's pointer, so they may be unique
keepsPointer :: Expr -> Bool
keepsPointer expr
  = case expr of
      CaseA{}     -> True
      Unfold{}    -> True
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
      Drop{}      -> False
      DropRu{}    -> False
      IsUnique{}  -> False
      UnboxRu{}   -> False
      Join{}      -> False
      Jump{}      -> False
