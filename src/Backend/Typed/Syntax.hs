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
    J ::= ∅ | J, j : Γ_c; (q̄ V̄) -> W           join points in scope, with their captures
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
-- - Shapes `Box V`, `1` and `⊕ᵢ Aᵢ` have known tags and can be destructured by `[case]` and
--   `[unbox]`. The alternatives of a sum must be shapes: `a + 1` or `T⟨B̄⟩ + 1` has no known tags.
--   Sum indices are sorted, nonnegative starts of nonoverlapping tag intervals.
--   A nested sum occupies its tag width; gaps retain excluded alternatives' tag positions.
-- - `a`, `a⟨B̄⟩` and `T⟨B̄⟩` without a definition are opaque: a value of such a type can only be
--   passed around.
-- - `λā.A` only occurs as the argument of a higher-kinded variable, and applying it is
--   β-reduction: `a⟨B̄⟩[λb̄.A / a] = A[B̄/b̄]`. A partial application `T⟨B̄⟩` is also allowed there.
-- - `unroll(T⟨B̄⟩) = A[B̄/ā]` for a definition `T⟨ā⟩ := A` (`TypeDef`); in the paper `T⟨B̄⟩` is
--   `μt.A[B̄/ā]` with the recursive occurrences replaced by `t`.
data AType = ABox VType                 -- Box V
           | AUnit                      -- 1
           | ASum [(Int,AType)]         -- ⊕ᵢ Aᵢ, indexed by stable zero-based tag positions
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
-- - A type is trivial (`Common.isTrivial`) if it contains no pointers: `𝟙`, raw types, sums,
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
           | VReuse Int (Maybe VVal)    -- ◇n[p]: if nonempty, an n-byte block containing p
           deriving (Eq,Show)

-- p is an unevaluated structural value describing the original contents.
-- It carries no ownership; its names follow scope and substitution.
-- Descriptions may be forgotten and cannot escape their names' scope.

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
-- (see `Query.litType`)
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

  --   Γ ⊢ v : Aᵢ
  --  ──────────────────────── [inj-a]
  --   Γ ⊢ injᵢ v : ⊕ⱼ Aⱼ
  | InjA Int AType AVal

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
  deriving (Eq,Show)

-- Unboxed values `Γ ⊢ v :q V`.
data VVal
  --  ───────────────── [var]
  --   x :q V ⊢ x :q V
  --
  -- As in the paper, a variable is only a value at an unboxed type. A variable `x :q A` at a boxed
  -- type (bound by `[case]` on `⊕ᵢ Aᵢ`, `[deref]` or `[unroll]`) is only an *operand*: the
  -- scrutinee of a destructuring form, the variable of `[drop]` or `[if-unique]`, the value of
  -- `[dup]` or the function of `[app]`. It cannot be stored again as a boxed value.
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
  -- An empty credit, passed when a join asks for a block that is unavailable.
  | NoReuse Int
  deriving (Eq,Show)

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
  -- Parameter modes come from the function's signature, including imported functions.
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
  -- where the binder is the scrutinee's pointer: `[case]` on `⊕ᵢ Aᵢ`, `[deref]`, `[unroll]` and
  -- `[unpack]` (`keepsPointer`).
  --
  --   Γ₁ ⊢ v :q V₁ ⊗ V₂    Γ₂, x :q V₁, y :q V₂ ⊢ e : W
  --  ──────────────────────────────────────────────────── [unpair]
  --   Γ₁, Γ₂ ⊢ let_q (x, y) = v in e : W
  --
  -- For a variable scrutinee z, credit descriptions substitute (x,y) for z.
  | Unpair Mode VVal Name Name VExpr

  --   Γ₁ ⊢ v :q ⊕ᵢ Vᵢ    Γ₂, xᵢ :q Vᵢ ⊢ eᵢ : W   (for each i)
  --  ────────────────────────────────────────────────────────── [case]
  --   Γ₁, Γ₂ ⊢ case_q v of { injᵢ xᵢ -> eᵢ } : W
  --
  -- For a variable scrutinee z, branch i substitutes injᵢ xᵢ in credit descriptions.
  | CaseV Mode VVal [(Name,VExpr)]

  --   Γ₁ ⊢ v :q ⊕ⱼ∈J Aⱼ    Γ₂, xᵢ :q Aᵢ ⊢ eᵢ : W (i ∈ I)    Γ₂, d :q ⊕ⱼ∈J\I Aⱼ ⊢ e : W
  --  ────────────────────────────────────────────────────────────────────────── [case-a]
  --   Γ₁, Γ₂ ⊢ case_q v of { injᵢ xᵢ -> eᵢ; _ d -> e } : W
  --
  -- Indices must belong to the sum and be distinct. Without a default every alternative occurs.
  -- The default excludes the matched indices without renumbering the remainder;
  -- it must be nonempty. No allocation or retagging occurs, at any mode.
  | CaseA Mode Name [(Int,Name,VExpr)] (Maybe (Name,VExpr))

  --   Γ₁ ⊢ v :q ⊕ᵢ∈J Aᵢ    Γ₂, x :q ⊕ᵢ∈J,i<k Aᵢ ⊢ e₁ : W    Γ₂, y :q ⊕ᵢ∈J,i≥k Aᵢ ⊢ e₂ : W
  --  ────────────────────────────────────────────────────────────────────────────── [split-a]
  --   Γ₁, Γ₂ ⊢ split_q v at k of { x -> e₁; y -> e₂ } : W
  --
  -- Both sides must be nonempty. Both binders retain the original indices,
  -- pointer and runtime tags. Even singleton partitions keep their sum wrapper.
  -- Like CaseA, this supports owned, borrowed and unique modes without repacking.
  | SplitA Mode Name Int (Name,VExpr) (Name,VExpr)

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
  --
  -- For a variable scrutinee z, credit descriptions substitute pack[b̄] x for z.
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
  -- Unboxed values are destructured to drop their boxed components (`Common.dropValue`).
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

  --   Γ, x :^ A, y : A ⊢ e : W    A contains no reuse credits
  --  ──────────────────────────────────────────── [dup-a]
  --   Γ, x :^ A ⊢ let y = dup x in e : W
  --
  -- Duplicate a boxed operand into another operand, preserving its enclosing sum's tag.
  -- It produces no AVal that could be injected into a different sum.
  | Dup Name Name VExpr

  --   Γ, x :! Box V ⊢ e₁ : W    Γ, x : Box V ⊢ e₂ : W    |V| defined
  --  ──────────────────────────────────────────────────────────────── [if-unique]
  --   Γ, x : Box V ⊢ if-unique x then e₁ else e₂ : W
  --
  -- Branches on whether a box is unique (`DropSpec`).
  | IsUnique Name VExpr VExpr

  --   Γ, x : V, r : ◇n[x] ⊢ e : W    |V| = n
  --  ─────────────────────────────────────────────── [unbox-ru]
  --   Γ, z :! Box V ⊢ let box x @ r = z in e : W
  --
  -- A unique `Box V` splits into its contents and its block, the inverse of `[box-at]`. With
  -- `[if-unique]` it makes `drop-reuse` of a box derivable.
  | UnboxRu Name Name Name VExpr

  --   Γ_c, x̄ :q̄ V̄ | J ⊢ e₁ : W    Γ, Γ_c | J, j : Γ_c; (q̄ V̄) -> W ⊢ e₂ : W
  --  ──────────────────────────────────────────────────────────────────── [join]
  --   Γ, Γ_c | J ⊢ join j(x̄ :q̄ V̄) = e₁ in e₂ : W
  --
  -- A join point captures the owned variables Γ_c that are free in its body, and is not
  -- recursive (`j` is not in scope in its body). Its body may jump to outer joins.
  -- Since J is reset outside of tail positions, a jump cannot escape
  -- and is always a tail call. Perceus only produces owned parameters and closed join
  -- points (Γ_c = ∅); only `JoinArgs`, the last pass, introduces captures. A captured
  -- variable must not be bound again in e₂, so every jump sees the same variable.
  | Join Name [(Name,Mode,VType)] VExpr VExpr

  --   j : Γ_c; (q̄ V̄) -> W ∈ J    Γᵢ ⊢ vᵢ :qᵢ Vᵢ
  --  ──────────────────────────────────────────────── [jump]
  --   Γ_c, Γ₁, ..., Γₙ | J ⊢ jump j(v₁, ..., vₙ) : W
  --
  -- A jump passes the captured variables to the join point as well as its arguments.
  | Jump Name [VVal]
  deriving (Eq,Show)

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
