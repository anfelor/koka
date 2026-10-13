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
    J ::= ∅ | J, j : (q̄ V̄) -> W                 join points in scope
    Σ                                          signatures (`Sigs`)

    Γ ⊢ a :q A       the boxed value a has type A
    Γ ⊢ v :q V       the unboxed value v has type V; an owned value consumes Γ
    Γ | J ⊢ e : W    the expression e has unboxed type W and consumes every owned variable of Γ
    ⊢ def            a top-level definition is well-typed

    `^Γ` marks every variable of Γ as borrowed. J is passed unchanged to every subexpression in
    tail position and omitted from the rules where that is all that happens; it is reset to ∅
    where an expression is not in tail position.

  Structural rules

         Γ | J ⊢ e : W                       Γ, x :^ t, x :^ t | J ⊢ e : W
    ─────────────────────── [weaken]       ─────────────────────────────── [contract]
     Γ, x :^ t | J ⊢ e : W                   Γ, x :^ t | J ⊢ e : W

    - Variables of a trivial type are unrestricted: they may be weakened and contracted at either
      mode, and used owned or borrowed. They need no `dup` or `drop`. (Not in the paper.)
    - A unique variable `x :! t` is owned and holds the only reference to its block. It may be used
      as an owned one. Any borrowed use of `x`, or of a variable borrowed from `x`, may duplicate the
      reference and demotes it to `x : t`; branches agree on the weaker status.
    - The paper scopes borrowing syntactically: `[let]` lends `^Γ₂` to the bound expression.
      Our IR borrows from an owned variable `z` anywhere (e.g. `case^ z` with `z` owned, as Perceus
      produces), and the binders are *borrowed from* `z`: they become invalid once `z` is consumed.
      In particular a borrowed argument of a call cannot be one that is passed owned.
    - The binder of a borrowed `[case]`, `[deref]`, `[unroll]` or `[unpack]` at a boxed type `A`
      is an *alias* of the owned `z` (or of the owned variable that an alias is borrowed from): it
      is `z`'s pointer. Consuming an alias, or testing it with `[if-unique]`, consumes `z` and
      makes the alias owned (unique if `z` was); the variables borrowed from `z` are then borrowed
      from it.
-}
module Backend.Typed.Syntax where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Data.Functor.Identity( Identity(..) )
import Common.Name

-- Types. Type variables range over boxed types `A`, and so do the variables of `∀`, `∃` and `λ`:
-- a value at a type variable `a` has the unboxed type `a*`. Elaboration instantiates a Koka type
-- argument of unboxed type `V` with `rep(V)`: `A` if `V = A*`, else `boxA(V)` (Koka's `box`),
-- with the parameters and results of functions in `A` boxed in turn (Koka's `boxedFunType`).
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

-- boxed types A, B: what a pointer points to.
--
-- - Shapes `Box V`, `1` and `A + B` have known tags and can be destructured by `[case]` and
--   `[unbox]`. The alternatives of a sum must be shapes: `a + 1` or `T⟨B̄⟩ + 1` has no known tags.
-- - `a`, `a⟨B̄⟩` and `T⟨B̄⟩` without a definition are opaque: a value of such a type can only be
--   passed around.
-- - `λā.A` only occurs as the argument of a higher-kinded variable, and applying it is
--   β-reduction: `a⟨B̄⟩[λb̄.A / a] = A[B̄/b̄]`. A partial application `T⟨B̄⟩` is also allowed there.
-- - `unroll(T⟨B̄⟩) = A[B̄/ā]` for a definition `T⟨ā⟩ := A` (`TypeDef`); in the paper `T⟨B̄⟩` is
--   `μt.A[B̄/ā]` with the recursive occurrences replaced by `t`.
data AType = ABox VType                 -- Box V
           | AUnit                      -- 1
           | ASum AType AType           -- A + B, binary and right-nested
           | AFun [(Mode,VType)] VType  -- (q̄ V̄) -> W, for top-level functions and closures alike
           | AForall [TVar] AType       -- ∀ā. A
           | AVar TVar                  -- a
           | AApp TVar [AType]          -- a⟨B̄⟩, an applied higher-kinded variable
           | ACon Name [AType]          -- T⟨B̄⟩, a named (recursive) type
           | ALam [TVar] AType          -- λā. A, a partially applied type
           deriving (Eq,Show)

-- unboxed types V, W: values of a fixed size without a header.
--
-- - `A*` is the only pointer-sized type (`Types.isPtr`): it holds a pointer to an `A` (or, for a
--   shape, an immediate value with its tag).
-- - Types are equal up to renaming of bound variables and β-reduction of type lambdas.
-- - A type is trivial (`Check.isTrivial`) if it contains no pointers: `𝟙`, raw types, sums,
--   products and existentials of trivial types, and `@field-addr*` and `@reuse*` (named types
--   that are not reference counted).
-- - `|V|` is the size of the heap block of a `Box V` (`Layout.blockSize`); it is only defined when
--   the payload is always a heap block (`Layout.isBlock`).
data VType = VPtr AType                 -- A*
           | VUnit                      -- 𝟙
           | VSum [VType]               -- ⊕ᵢ Vᵢ, n-ary (a Koka value type with several constructors)
           | VProd VType VType          -- V ⊗ W
           | VRaw Name                  -- raw: unboxed primitives (`int32`, `float64`, `char`, ...)
           | VExists [TVar] VType       -- ∃ā. V
           | VReuse Int                 -- ◇n, a reuse credit for a heap block of n bytes
           deriving (Eq,Show)

-- t ::= A | V
data Ty = A AType | V VType
          deriving (Eq,Show)

-- a named type `T⟨ā⟩ := A`; without a body (`int`, `string`, ...) it cannot be unrolled
data TypeDef = TypeDef{ tdefName :: Name, tdefParams :: [TVar], tdefBody :: Maybe AType, tdefLazy :: Maybe LazyInfo }
             deriving (Show)

-- lazy datatypes: the index of the indirection constructor, and for each constructor
-- whether it is lazy and Koka's allocation size (Koka decides by these sizes when to memoize in place)
data LazyInfo = LazyInfo{ lazyIndirect :: Int, lazyCons :: [(Bool,Int)] }
              deriving (Show)

type TypeDefs = M.Map Name TypeDef

-- the type of a literal, `type(l)`: `int*` and `string*` (named types without a definition),
-- `char` and `float64` raw
-- (see `Check.litType`)
data Lit = LitInt Integer
         | LitFloat Double
         | LitChar Char
         | LitString String
         deriving (Eq,Show)

-- Values `Γ ⊢ v :q t`. A borrowed value is an atom: a variable, a global, a literal, `()`, a
-- function, or a type application of one of these. A unique value is a variable. All other values
-- are owned. (The paper also allows borrowed pairs and injections.)
--
-- Boxed values `Γ ⊢ a :q A`; boxed variables occur only as named operands.
data AVal
  --   f : ∀ā. (q̄ V̄) -> W ∈ Σ    q̄ = ·
  --  ──────────────────────────────── [fun]
  --   ∅ ⊢ f :q ∀ā. (q̄ V̄) -> W
  --
  -- A top-level function used as a value is a static closure and can be used at either mode.
  -- Only functions with owned parameters can be used as closures (see `[app]`).
  = Fun Name

  --  ────────────── [unit]
  --   ∅ ⊢ () : 1
  | UnitA

  --   Γ ⊢ v : A
  --  ──────────────────── [inl]
  --   Γ ⊢ inl v : A + B
  | Inl AType AVal

  --   Γ ⊢ v : B
  --  ──────────────────── [inr]
  --   Γ ⊢ inr v : A + B
  | Inr AType AVal

  --   Γ ⊢ v : unroll(T⟨B̄⟩)
  --  ──────────────────────── [roll]
  --   Γ ⊢ roll v : T⟨B̄⟩
  --
  -- A no-op at run time; the annotation is `T⟨B̄⟩`.
  | Roll AType AVal

  --   Γ ⊢ v : V
  --  ──────────────────── [box]
  --   Γ ⊢ box v : Box V
  --
  -- A fresh allocation: the paper's `alloc_n; box v`.
  | Box VVal

  --   C : ∀ā. V -> T⟨ā⟩ ∈ Σ    Γ ⊢ v : V[B̄/ā]
  --  ─────────────────────────────────────────── [open-con]
  --   Γ ⊢ C[B̄] v : T⟨B̄⟩
  --
  -- A constructor of an open datatype (whose constructors are spread over modules).
  | OpenCon Name [AType] VVal

  --   ⌊Γ⌋, x̄ : V̄ | ∅ ⊢ e : W    q̄ = ·
  --  ───────────────────────────────────────── [lam]
  --   Γ ⊢ fn(x̄ :q̄ V̄) : W -> e : (q̄ V̄) -> W
  --
  -- A closure consumes its captures Γ, which are owned in its body (`⌊Γ⌋`). Closures have the
  -- same arrow type as top-level functions, but only owned parameters.
  | Lam [(Name,Mode,VType)] VType VExpr

  --  ──────────────── [dup]
  --   x :^ A ⊢ dup x : A
  --
  -- A borrowed boxed variable can be duplicated into an owned boxed value.
  | DupA Name

  --   Γ ⊢ v : V    |V| = n
  --  ────────────────────────────── [box-at]
  --   Γ, r : ◇n ⊢ box@r v : Box V
  --
  -- A box allocated in the block of a reuse credit, or freshly if the credit is empty (the
  -- paper's `[box]`, where the credit is anonymous).
  | BoxAt Name VVal

  --   Γ ⊢ v : V    T⟨ā⟩ := A is lazy    Box V is an alternative of A[B̄/ā]
  --  ────────────────────────────────────────────────────────────────────── [box-in]
  --   Γ, x : T⟨B̄⟩* ⊢ box-in@x v : Box V
  --
  -- A box written over the block of the lazy value `x` under evaluation, keeping its reference
  -- count (`Lazy`). It is an update through a shared reference and only sound because `x` is
  -- locked and its old fields (taken by `[unbox-lazy]`) are not used again.
  | BoxIn Name VVal
  deriving (Show)

-- Unboxed values `Γ ⊢ v :q V`.
data VVal
  --  ───────────────── [var]
  --   x :q V ⊢ x :q V
  --
  -- As in the paper, a variable is only a value at an unboxed type. A variable `x :q A` at a boxed
  -- type (bound by `[case]` on `A + B`, `[deref]` or `[unroll]`) is only an *operand*: the
  -- scrutinee of a destructuring form, the variable of `[drop]` or `[if-unique]`, the value of
  -- `[dup]` or the function of `[app]`. It can only be stored again through `DupA`.
  = Var Name

  --   x : ∀ā. V ∈ Σ
  --  ───────────────────────── [glob]
  --   ∅ ⊢ x[B̄] :^ V[B̄/ā]
  --
  -- A top-level value is borrowed: an owned use needs a `dup` (unless its type is trivial).
  | Glob Name [AType]

  --  ────────────── [unit]
  --   ∅ ⊢ () : 𝟙
  | UnitV

  --  ──────────────────── [lit]
  --   ∅ ⊢ l : type(l)
  | Lit Lit

  --   Γ ⊢ v : Vᵢ
  --  ─────────────────────── [inj]
  --   Γ ⊢ injᵢ v : ⊕ⱼ Vⱼ
  | Inj Int VType VVal

  --   Γ₁ ⊢ v₁ : V₁    Γ₂ ⊢ v₂ : V₂
  --  ────────────────────────────────── [pair]
  --   Γ₁, Γ₂ ⊢ (v₁, v₂) : V₁ ⊗ V₂
  | Pair VVal VVal

  --   Γ ⊢ v : A
  --  ───────────────── [ptr]
  --   Γ ⊢ ptr v : A*
  --
  -- A no-op at run time. The annotation records the pointed-to type `A`.
  | Ptr AType AVal

  --   Γ ⊢ v : V[B̄/ā]
  --  ─────────────────────────── [pack]
  --   Γ ⊢ pack[B̄] v : ∃ā. V
  | Pack VType [AType] VVal

  --   Γ ⊢ v :q (∀ā. A)*
  --  ──────────────────────────── [tyapp]
  --   Γ ⊢ v[B̄] :q (A[B̄/ā])*
  --
  -- The paper's `[inst]`, on pointers so that it preserves the memory layout and applies to a
  -- variable without a boxed one.
  | TyApp VVal [AType]

  --   Γ ⊢ v :^ V
  --  ──────────────── [dup]
  --   Γ ⊢ dup v : V
  --
  -- Keep unboxed duplication primitive so drop specialization and code generation can
  -- duplicate a whole payload without expanding it into destructuring and reconstruction.
  -- Reuse credits remain linear and cannot be duplicated.
  | DupV VVal

  --  ────────────────────── [no-reuse]
  --   ∅ ⊢ no-reuse n : ◇n
  --
  -- The empty credit: an allocation in it is fresh. Passed by a jump that has no credit for a
  -- parameter of its join point.
  | NoReuse Int
  deriving (Show)

-- Expressions `Γ | J ⊢ e : W` (always unboxed).
--
-- The result metavariable of the control-flow rules is W, not an arbitrary t = A | V:
-- return, calls, application and generalization produce V, and every other expression
-- forwards a subexpression's result. Thus no rule introduces an A-typed expression.
data VExpr
  --   Γ ⊢ v : V
  --  ──────────────────── [ret]
  --   Γ ⊢ ret v : V
  --
  -- Expressions only have unboxed types, as in the paper.
  = Ret VVal

  --   Γ₁, ^Γ₂ | ∅ ⊢ e₁ : V    Γ₂, x : V | J ⊢ e₂ : W
  --  ─────────────────────────────────────────────────── [let]
  --   Γ₁, Γ₂ | J ⊢ let x : V = e₁ in e₂ : W
  | Let Name VType VExpr VExpr

  --   f : ∀ā. (q̄ V̄) -> W ∈ Σ    Γᵢ ⊢ vᵢ :qᵢ Vᵢ[B̄/ā]
  --  ───────────────────────────────────────────────── [call]
  --   Γ₁, ..., Γₙ ⊢ f[B̄](v₁, ..., vₙ) : W[B̄/ā]
  --
  -- Elaboration only gives our own functions owned parameters; borrowed parameters only occur
  -- for externals.
  | Call Name [AType] [VVal]

  --   Γ₀ ⊢ v : (V̄) -> W    Γᵢ ⊢ vᵢ : Vᵢ
  --  ──────────────────────────────────────── [app]
  --   Γ₀, Γ₁, ..., Γₙ ⊢ v(v₁, ..., vₙ) : W
  --
  -- Applying a closure consumes it, and all its parameters are owned (no `[bapp]`).
  | App Name [VVal]

  -- Destructuring takes a mode: owned destructuring consumes the scrutinee and its binders are
  -- owned (a move); borrowed destructuring gives binders borrowed from the scrutinee. Unique
  -- destructuring consumes a unique scrutinee and its binders are unique; it is only allowed
  -- where the binder is the scrutinee's pointer: `[case]` on `A + B`, `[deref]`, `[unroll]` and
  -- `[unpack]` (`keepsPointer`).
  --
  --   Γ₁ ⊢ v :q V₁ ⊗ V₂    Γ₂, x :q V₁, y :q V₂ ⊢ e : W
  --  ──────────────────────────────────────────────────── [unpair]
  --   Γ₁, Γ₂ ⊢ let_q (x, y) = v in e : W
  | Unpair Mode VVal Name Name VExpr

  --   Γ₁ ⊢ v :q ⊕ᵢ Vᵢ    Γ₂, xᵢ :q Vᵢ ⊢ eᵢ : W   (for each i)
  --  ────────────────────────────────────────────────────────── [case]
  --   Γ₁, Γ₂ ⊢ case_q v of { injᵢ xᵢ -> eᵢ } : W
  | CaseV Mode VVal [(Name,VExpr)]

  --   Γ₁ ⊢ v :q A + B    Γ₂, x :q A ⊢ e₁ : W    Γ₂, y :q B ⊢ e₂ : W
  --  ──────────────────────────────────────────────────────────────── [case]
  --   Γ₁, Γ₂ ⊢ case_q v of { inl x -> e₁; inr y -> e₂ } : W
  | CaseA Mode Name (Name,VExpr) (Name,VExpr)

  --   Γ₁ ⊢ v :q A*    Γ₂, x :q A ⊢ e : W
  --  ───────────────────────────────────── [deref]
  --   Γ₁, Γ₂ ⊢ let_q ptr x = v in e : W
  | Deref Mode VVal Name VExpr

  --   Γ₁ ⊢ v :q T⟨B̄⟩    Γ₂, x :q unroll(T⟨B̄⟩) ⊢ e : W
  --  ──────────────────────────────────────────────────── [unroll]
  --   Γ₁, Γ₂ ⊢ let_q roll x = v in e : W
  | Unroll Mode Name Name VExpr

  --   Γ₁ ⊢ v :^ Box V    Γ₂, x :^ V ⊢ e : W
  --  ──────────────────────────────────────── [bunbox]
  --   Γ₁, Γ₂ ⊢ let^ box x = v in e : W
  --
  -- Reading the contents of a box is always borrowed. The paper's owned `[unbox]`, which keeps
  -- the block as a credit, is `[unbox-ru]` and requires the box to be unique.
  | Unbox Mode Name Name VExpr

  --   Γ₁ ⊢ v :^ Box V    Γ₂, x : V ⊢ e : W
  --  ─────────────────────────────────────────── [unbox-lazy]
  --   Γ₁, Γ₂ ⊢ let-lazy box x = v in e : W
  --
  -- Takes the contents of a box of the lazy value under evaluation without duplicating them
  -- (`Perceus`); the box is left *hollow* until `[box-in]` writes over it or it is freed. In the
  -- calculus this needs a hollow box type (a shared `◇n`). Trusted by `Linear`.
  | UnboxLazy Name Name VExpr

  --   Γ₁ ⊢ v :q ∃ā. V    Γ₂, x :q V[b̄/ā] ⊢ e : W    b̄ ∉ ftv(Γ₂, W)
  --  ────────────────────────────────────────────────────────────────── [unpack]
  --   Γ₁, Γ₂ ⊢ let_q pack[b̄] x = v in e : W
  | Unpack Mode VVal [TVar] Name VExpr

  --   Γ₁ ⊢ v :^ V    lᵢ : V    Γ₂ ⊢ eᵢ : W    Γ₂ ⊢ e : W
  --  ────────────────────────────────────────────────────── [case-lit]
  --   Γ₁, Γ₂ ⊢ case v of { lᵢ -> eᵢ; _ -> e } : W
  | CaseLit VVal [(Lit,VExpr)] VExpr

  --   Γ₁ ⊢ v :^ T⟨B̄⟩    Cᵢ : ∀ā. Vᵢ -> T⟨ā⟩ ∈ Σ    Γ₂, xᵢ :^ Vᵢ[B̄/ā] ⊢ eᵢ : W    Γ₂ ⊢ e : W
  --  ──────────────────────────────────────────────────────────────────────────────── [case-open]
  --   Γ₁, Γ₂ ⊢ case^ v of { Cᵢ xᵢ -> eᵢ; _ -> e } : W
  --
  -- Matching on the tag of an open datatype, with a mandatory default. Always borrowed.
  | CaseOpen Mode Name [(Name,Name,VExpr)] VExpr

  --   Γ | ∅ ⊢ e : A*    ā ∉ ftv(Γ)
  --  ──────────────────────────────── [gen]
  --   Γ | J ⊢ gen ā. e : (∀ā. A)*
  --
  -- The introduction form of `[tyapp]`. An expression form (Koka has no value restriction);
  -- sound because the result is a type-erased pointer. The paper's `[gen]` on a value `v : A` is
  -- `gen ā. ret (ptr v)`.
  | Gen [TVar] VExpr

  --       Γ ⊢ e : W
  --  ─────────────────────────── [drop]
  --   Γ, x : A ⊢ drop x; e : W
  --
  -- Unboxed values are destructured to drop their boxed components (`Perceus.dropValue`).
  -- The paper's `[dropru]` is derived
  -- from `[if-unique]` and `[unbox-ru]` (`Reuse.dropReuse`):
  --
  --   let r = drop-reuse x in e  ≜  let r = (if-unique x then (let box y @ r' = x in discard y; ret r')
  --                                          else (drop x; ret no-reuse n)) in e
  | Drop Name VExpr

  --       Γ ⊢ e : W
  --  ─────────────────────────── [free]
  --   Γ, r : ◇n ⊢ free r; e : W
  --
  -- Free the block of a reuse credit, or do nothing if the credit is empty.
  | Free Name VExpr

  --   Γ, x :! Box V ⊢ e₁ : W    Γ, x : Box V ⊢ e₂ : W    |V| defined
  --  ──────────────────────────────────────────────────────────────── [if-unique]
  --   Γ, x : Box V ⊢ if-unique x then e₁ else e₂ : W
  --
  -- Branches on whether a box is unique (`DropSpec`).
  | IsUnique Name VExpr VExpr

  --   Γ, x : V, r : ◇n ⊢ e : W    |V| = n
  --  ─────────────────────────────────────────────── [unbox-ru]
  --   Γ, z :! Box V ⊢ let box x @ r = z in e : W
  --
  -- A unique `Box V` splits into its contents and its block, the inverse of `[box-at]`. With
  -- `[if-unique]` it makes `drop-reuse` of a box derivable.
  | UnboxRu Name Name Name VExpr

  --   x̄ :q̄ V̄ | J ⊢ e₁ : W    Γ | J, j : (q̄ V̄) -> W ⊢ e₂ : W
  --  ──────────────────────────────────────────────────────── [join]
  --   Γ | J ⊢ join j(x̄ :q̄ V̄) = e₁ in e₂ : W
  --
  -- A join point is closed over ordinary variables (only its parameters are free in its body)
  -- and not recursive (`j` is not in scope in its body). Its body may jump to outer joins.
  -- Since J is reset outside of tail positions, a jump cannot escape
  -- and is always a tail call. Perceus only produces owned parameters.
  | Join Name [(Name,Mode,VType)] VExpr VExpr

  --   j : (q̄ V̄) -> W ∈ J    Γᵢ ⊢ vᵢ :qᵢ Vᵢ
  --  ─────────────────────────────────────── [jump]
  --   Γ₁, ..., Γₙ | J ⊢ jump j(v₁, ..., vₙ) : W
  | Jump Name [VVal]
  deriving (Show)

-- Definitions `⊢ def`, with `f : ∀ā. (q̄ V̄) -> W ∈ Σ` and `x : ∀ā. V ∈ Σ`
data Def
  --   x̄ :q̄ V̄ | ∅ ⊢ e : W
  --  ──────────────────────────────── [deffun]
  --   ⊢ fun f⟨ā⟩(x̄ :q̄ V̄) : W = e
  = DefFun{ defName :: Name, defParams :: [TVar], defArgs :: [(Name,Mode,VType)], defRes :: VType, defBody :: VExpr }

  --   ∅ | ∅ ⊢ e : V
  --  ───────────────────────── [defval]
  --   ⊢ val x⟨ā⟩ : V = e
  --
  -- A top-level value, initialized when the module is loaded. It can be polymorphic.
  | DefVal{ defName :: Name, defParams :: [TVar], defType :: VType, defBody :: VExpr }
  deriving (Show)

-- signatures Σ
data Sig = SigFun [TVar] [(Mode,VType)] VType  -- f : ∀ā. (q̄ V̄) -> W
         | SigVal [TVar] VType                 -- x : ∀ā. V
         | SigCon [TVar] VType Name            -- C : ∀ā. V -> T⟨ā⟩, a constructor of an open type T
         deriving (Show)

type Sigs = M.Map Name Sig

data Program = Program{ progName :: Name, progTypes :: TypeDefs, progSigs :: Sigs, progDefs :: [Def] }

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
      DupA x         -> DupA <$> fn x
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
      IsUnique x e1 e2      -> IsUnique <$> fn x <*> fe [] e1 <*> fe [] e2
      UnboxRu v x r e       -> (\v' -> UnboxRu v' x r) <$> fn v <*> fe [x,r] e
      Join j ps e1 e2       -> Join j ps <$> fe [x | (x,_,_) <- ps] e1 <*> fe [] e2
      Jump j vs             -> Jump j <$> traverse fv vs

varOf :: VVal -> Name
varOf (Var y) = y
varOf v       = error ("Backend.Typed.Syntax.varOf: not a variable: " ++ show v)

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
      Drop{}      -> False
      Free{}      -> False
      IsUnique{}  -> False
      UnboxRu{}   -> False
      Join{}      -> False
      Jump{}      -> False
