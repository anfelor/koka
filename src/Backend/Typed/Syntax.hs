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

    Γ ::= ∅ | Γ, x :q V | Γ, x :q A             variables
    J ::= ∅ | J, j : Γ_c; (q̄ V̄) -> W           join points in scope, with their captures
    Σ                                          signatures (`Sigs`)

    Γ ⊢ a :q A       the boxed value a has type A
    Γ ⊢ v :q V       the unboxed value v has type V; an owned value consumes Γ
    Γ | J ⊢ e : W    the expression e has unboxed type W and consumes every owned variable of Γ
    Γ | J ⊢ʸ e : W   the same, where the result of e may be the dummy value of an effect yield
    ⊢ def            a top-level definition is well-typed

    `^Γ` marks every variable of Γ as borrowed. J is passed unchanged to every subexpression in
    tail position and omitted from the rules where that is all that happens; it is reset to ∅
    where an expression is not in tail position. The mark `ʸ` follows J: it is passed unchanged
    to every subexpression in tail position (and omitted from the rules), and where J is reset
    to ∅ it is dropped unless the rule writes `⊢ʸ` (the bodies of definitions and closures and
    the bound expression of `[let-yield]`). Only `[yielded]` requires it. Without the mark, a
    position only excludes `[yielded]`: since the IR has no effects, a call bound by `[let]`
    may still return a dummy, which `Yields` ensures is not inspected (see `[let-yield]`).

    The tag of a box z, tag(z), is determined by its path (`Common.boxTag`): it is i if z is
    the binder of alternative i of a `[case-a]`, and 1 otherwise.

  Structural rules

         Γ | J ⊢ e : W                       Γ, x :^ t, x :^ t | J ⊢ e : W
    ─────────────────────── [weaken]       ─────────────────────────────── [contract]
     Γ, x :^ t | J ⊢ e : W                   Γ, x :^ t | J ⊢ e : W

    - Variables of a trivial type are unrestricted: they may be weakened and contracted at either
      mode, and used owned or borrowed. They need no `dup` or `drop`. (Not in the paper.)
    - A unique variable `x :! t` is owned and holds the only reference to its block. It may be used
      as an owned one. Any borrowed use of `x`, or of a variable on its path, may duplicate the
      reference and demotes it to `x : t`; branches agree on the weaker status.
    - The paper scopes borrowing syntactically: `[let]` lends `^Γ₂` to the bound expression.
      Our IR borrows from an owned variable `z` anywhere (e.g. `case^ z` with `z` owned, as Perceus
      produces). The binders of a destructuring of `z` are its *parts*, named by their paths
      (`z.fst`, see `Path`), and their borrowed uses become invalid once `z` is consumed. In
      particular a borrowed argument of a call cannot be one that is passed owned.
    - The parts of an owned variable are owned: consuming a part takes it out of its parent, and
      the parent is consumed once all of its parts are: both components of a pair, the contents
      and the credit of a box, or the binder of any other destructuring. The binder of `[case-a]`,
      `[split-a]`, `[deref]` or `[unroll]` at a boxed type is the parent's pointer, and that of
      `[unpack]` (a no-op) is the parent itself: consuming it, or testing it with `[if-unique]`, consumes or tests the parent (so it is unique
      where the parent is). Hence an owned destructuring of a variable is a borrowed one whose
      binders are consumed, and only a unique destructuring needs its mode: it consumes a unique
      scrutinee.
    - `[dup]` binds its copy as a new root, so a variable holds at most one owned reference.
      For example, after `val y = dup z.fst; drop z` the context holds `y : V`.
    - After `Loads`, the contents of a box are a *place* (`Layout.placeBinders`): `z.contents`
      of a product, and the binder of `[unpack]` of a place, stay in the block of `z`. Every use of a place reads the block and needs a reference to the credit
      `z.credit`, which consuming `z`, or the credit after `[unbox-ru]`, consumes. A `[proj]`
      of a place copies its field out of the block, so the binder holds only its own
      references. Code generation may also load a place at once (`--feager-loads`), which is
      sound as the box is live at `[bunbox]`.

  Constructor contexts

    A context `c : ctx⟨A,B⟩` is an `A` with one hole of type `B*` (Koka's `cctx<a,b>`). At run
    time it is either empty (`ctx □`, with A = B) or a pointer `res` to a block b₀ together with
    the address of the hole, a field of a block bₙ, such that:
    - the path b₀, ..., bₙ consists of blocks allocated by `[ctx]` (or copied by the runtime),
      and the header of each bᵢ records the index of the field that leads to bᵢ₊₁ (or that is
      the hole, for bₙ): the *context path*;
    - each bᵢ with i > 0 is referenced only by bᵢ₋₁;
    - the hole holds a placeholder that is not a pointer, so dropping `res` skips it.
    A unique context `c :! ctx⟨A,B⟩` also holds the only reference to `res`, so the whole path
    is unique and `[plug]` writes into the hole in place. Duplicating a context shares `res`
    and demotes it to owned; `[ctx-copy]` copies the path of an owned context when `res` is
    shared, after which it can be plugged in place.
    The type has no destructuring rule, so nothing else can reach into the path.
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
--   `[unbox]`. A `Box V` is a heap block with a header (unless V has no contents, `𝟙`).
--   Sums are flat: their alternatives are `Box V` or `1` (`a + 1` or `T⟨B̄⟩ + 1` has no known
--   tags), indexed by their runtime tags, which are increasing and start at 1 as in Koka.
--   A sub-sum keeps the tags of its alternatives, with gaps for those it excludes.
-- - `Scalar raw` is Koka's `box` of a raw value: an immediate value, or a block that the runtime
--   allocates (such as a large `float64`). It has no tag, so it is not a shape, and it is not
--   reused. Nothing relies on its uniqueness: `[if-unique]` and `[unbox-ru]` do not apply to it.
--   `boxA` chooses it for a raw value outside a sum, and for a product whose only field is one
--   (`Layout.scalarField`), which Koka boxes like that field; an enumeration there is boxed as
--   its shape.
-- - `a`, `a⟨B̄⟩` and `T⟨B̄⟩` without a definition are opaque: a value of such a type can only be
--   passed around.
-- - `λā.A` only occurs as the argument of a higher-kinded variable, and applying it is
--   β-reduction: `a⟨B̄⟩[λb̄.A / a] = A[B̄/b̄]`. A partial application `T⟨B̄⟩` is also allowed there.
-- - `unroll(T⟨B̄⟩) = A[B̄/ā]` for a definition `T⟨ā⟩ := A` (`TypeDef`); in the paper `T⟨B̄⟩` is
--   `μt.A[B̄/ā]` with the recursive occurrences replaced by `t`.
data AType = ABox VType                 -- Box V
           | AScalar Raw                -- Scalar raw
           | AUnit                      -- 1
           | ASum [(Int,AType)]         -- ⊕ᵢ Aᵢ, indexed by tags
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
-- - A type is trivial (`Query.trivialTy`) if it contains no pointers: `𝟙`, raw types, sums,
--   products and existentials of trivial types, `@reuse*` (a named type that is not
--   reference counted), and named types whose body is trivial.
-- - `ctx⟨A,B⟩` is an abstract pair of a pointer and a field address (see "Constructor
--   contexts" above). It is not trivial and has the layout of `A* ⊗ B*`. A nonempty context
--   `ctx⁺⟨A,B⟩` is also a context `ctx⟨A,B⟩`, as a full credit is also a credit.
-- - `|V|` is the size of the heap block of a `Box V` (`Layout.blockSize`); it is only defined when
--   V has contents (`Layout.isBlock`).
-- - A full credit `◆n[k; p : V]` is also a credit `◇n[k; p : V]` that may be empty: a value of
--   the former can be used where the latter is expected (`Query.expectV`), and branches that
--   disagree on it agree on the latter.
data VType = VPtr AType                 -- A*
           | VUnit                      -- 𝟙
           | VSum [VType]               -- ⊕ᵢ Vᵢ, n-ary (a Koka value type with several constructors)
           | VProd VType VType          -- V ⊗ W
           | VRaw Raw                   -- raw: unboxed primitives (`int32`, `float64`, `char`, ...)
           | VExists [TVar] VType       -- ∃ā. V
           | VReuse Fill Int (Maybe Contents) -- ◇n[k; p : V] or ◆n[k; p : V]: if nonempty, an n-byte block with tag k containing p
           | VCtx Fill AType AType      -- ctx⟨A,B⟩ or ctx⁺⟨A,B⟩: an A with a hole of type B*, nonempty if full
           deriving (Eq,Show)

-- raw types: the primitive value types of Koka (`TypeInfo.rawType`), named by their C type
data Raw = RChar | RSSize | RIntPtr | RFloat64 | RFloat32
         | RInt64 | RInt32 | RInt16 | RInt8 | RUInt8
         deriving (Eq,Show)

-- The description `k; p : V` of a credit's block: the tag k in its header and its contents, an
-- unevaluated structural value p of type V with |V| = n. It carries no ownership, and its names denote the values they were
-- bound to, so they need not be in scope: a binder runs at most once on each path through a
-- definition. A name in a description that is in scope may only be bound again to an alias of
-- its value (`Linear`). Descriptions follow substitution, and may be forgotten but not invented.
-- The tag alone may be forgotten as well (`_; p : V`), so that code generation writes it.
data Contents = Contents (Maybe Int) VVal VType
              deriving (Eq,Show)

-- A full credit `◆n` holds a block; a credit `◇n` may be empty (`no-reuse`). Likewise, a full
-- context `ctx⁺` has a `res` block, and a context `ctx` may be empty.
data Fill = Full | MaybeEmpty
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
-- (see `Query.litType`)
data Lit = LitInt Integer
         | LitFloat Double
         | LitChar Char
         | LitString String
         deriving (Eq,Show)

-- Variables are paths: a root followed by the steps of the destructurings that lead from the
-- root to the variable, outermost first. For example, `z.snd.deref` is the binder of
-- `let_q ptr x = z.snd` where `z.snd` is the binder of `let_q x = z.snd`. A projection
-- (`[proj]`), and a field of `[case-open]`, contributes all of its steps. The binders
-- of other forms are roots, and a root is bound only once in a definition. `Paths`
-- establishes these invariants after elaboration and after `OrderFields` changes
-- the product representation. The other passes preserve them; `Check` validates
-- each pass's output directly.
data Path = Path Name [Step]
          deriving (Eq,Ord)

-- the steps from the scrutinee of a destructuring form to its binders
data Step = SFst | SSnd            -- [proj]
          | SInjV Int              -- [case]
          | SPack                  -- [unpack]
          | SDeref                 -- [deref]
          | SRoll                  -- [unroll]
          | SInjA Int | SRest      -- [case-a]: an alternative or the default
          | SLo | SHi              -- [split-a]
          | SContents | SCredit    -- [bunbox] and [unbox-ru]
          | SOpen Name             -- [case-open]
          deriving (Eq,Ord)

instance Show Path where
  show (Path x ss) = show x ++ concatMap (('.':) . show) ss

instance Show Step where
  show s = case s of
             SFst      -> "fst"
             SSnd      -> "snd"
             SInjV i   -> "inj" ++ show i
             SPack     -> "pack"
             SDeref    -> "deref"
             SRoll     -> "roll"
             SInjA i   -> "inj" ++ show i
             SRest     -> "rest"
             SLo       -> "lo"
             SHi       -> "hi"
             SContents -> "contents"
             SCredit   -> "credit"
             SOpen c   -> show c

root :: Name -> Path
root x = Path x []

-- Values `Γ ⊢ v :q t`. A borrowed value is structural: a variable, a global, a literal, `()`,
-- a function, a type application of one of these, or a pair, injection or pack of borrowed
-- values (as in the paper). A unique value is a variable, a context `ctx K`, `c₁ ++ c₂`,
-- `ctx-copy c`, `()`, a literal of a trivial type, or a pair, injection or pack of unique
-- values. All other values are owned.
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

  --   Γ ⊢ v : raw
  --  ────────────────────────────── [scalar]
  --   Γ ⊢ scalar v : Scalar raw
  --
  -- Koka's `box` of a raw value, which allocates only if the value is not immediate.
  | Scalar VVal

  --   C : ∀ā. V̄ -> T⟨ā⟩ ∈ Σ    Γᵢ ⊢ vᵢ : Vᵢ[B̄/ā]
  --  ───────────────────────────────────────────── [open-con]
  --   Γ̄ ⊢ C[B̄](v̄) : T⟨B̄⟩
  --
  -- A constructor of an open datatype (whose constructors are spread over modules), with one
  -- value for each of its source fields: code generation passes them to Koka's constructor
  -- as they are, so their layout is that of each field on its own.
  | OpenCon Name [AType] [VVal]

  --   ⌊Γ⌋, x̄ : V̄ | ∅ ⊢ʸ e : W    q̄ = ·
  --  ───────────────────────────────────────── [lam]
  --   Γ ⊢ fn(x̄ :q̄ V̄) : W -> e : (q̄ V̄) -> W
  --
  -- A closure consumes its captures Γ, which are owned in its body (`⌊Γ⌋`). Closures have the
  -- same arrow type as top-level functions, but only owned parameters.
  | Lam [(Path,Mode,VType)] VType VExpr

  --   Γ ⊢ v : V    |V| = n
  --  ────────────────────────────── [box-at]
  --   Γ, r : ◇n ⊢ box@r v : Box V
  --
  -- A box allocated in the block of a reuse credit, or freshly if the credit is empty (the
  -- paper's `[box]`, where the credit is anonymous). The block of a full credit `◆n` is
  -- written in place without a test.
  | BoxAt Path VVal

  --   Γ ⊢ v : V    T⟨ā⟩ := A is lazy    Box V is an alternative of A[B̄/ā]
  --  ────────────────────────────────────────────────────────────────────── [box-in]
  --   Γ, x : T⟨B̄⟩* ⊢ box-in@x v : Box V
  --
  -- A box written over the block of the lazy value `x` under evaluation, keeping its reference
  -- count (`Lazy`). It is an update through a shared reference and only sound because `x` is
  -- locked and its old fields (taken by `[unbox-lazy]`) are not used again.
  | BoxIn Path VVal
  deriving (Eq,Show)

-- Unboxed values `Γ ⊢ v :q V`.
data VVal
  --  ───────────────── [var]
  --   x :q V ⊢ x :q V
  --
  -- As in the paper, a variable is only a value at an unboxed type. A variable `x :q A` at a boxed
  -- type (bound by `[case]` on `⊕ᵢ Aᵢ`, `[deref]` or `[unroll]`) is only an *operand*: the
  -- scrutinee of a destructuring form or `[unscalar]`, the variable of `[drop]` or `[if-unique]`, or
  -- the function of `[app]`. It cannot be stored again as a boxed value.
  = Var Path

  --   x : ∀ā. V ∈ Σ
  --  ───────────────────────── [glob]
  --   ∅ ⊢ x[B̄] :^ V[B̄/ā]
  --
  -- A top-level value is borrowed: an owned use needs a `[dup-glob]` (unless its type is trivial).
  | Glob Name [AType]

  --  ─────────────── [unit]
  --   ∅ ⊢ () :q 𝟙
  | UnitV

  --  ──────────────────── [lit]
  --   ∅ ⊢ l : type(l)
  --
  -- A literal of a trivial type is also unique; `int` and `string` literals may be shared.
  | Lit Lit

  --   Γ ⊢ v :q Vᵢ
  --  ──────────────────────── [inj]
  --   Γ ⊢ injᵢ v :q ⊕ⱼ Vⱼ
  | Inj Int VType VVal

  --   Γ₁ ⊢ v₁ :q V₁    Γ₂ ⊢ v₂ :q V₂
  --  ──────────────────────────────────── [pair]
  --   Γ₁, Γ₂ ⊢ (v₁, v₂) :q V₁ ⊗ V₂
  | Pair VVal VVal

  --   Γ ⊢ v : A
  --  ───────────────── [ptr]
  --   Γ ⊢ ptr v : A*
  --
  -- A no-op at run time. The annotation records the pointed-to type `A`.
  | Ptr AType AVal

  --   Γ ⊢ v :q V[B̄/ā]
  --  ──────────────────────────── [pack]
  --   Γ ⊢ pack[B̄] v :q ∃ā. V
  | Pack VType [AType] VVal

  --   Γ ⊢ v :q (∀ā. A)*
  --  ──────────────────────────── [tyapp]
  --   Γ ⊢ v[B̄] :q (A[B̄/ā])*
  --
  -- The paper's `[inst]`, on pointers so that it preserves the memory layout and applies to a
  -- variable without a boxed one.
  | TyApp VVal [AType]

  --   x : ∀ā. V ∈ Σ
  --  ────────────────────────────── [dup-glob]
  --   ∅ ⊢ dup x[B̄] : V[B̄/ā]
  --
  -- An owned reference to a top-level value. Variables are duplicated by `[dup]`.
  | DupV VVal

  --  ────────────────────── [no-reuse]
  --   ∅ ⊢ no-reuse n : ◇n
  --
  --   |V| = n
  --  ─────────────────────────────────────────────── [no-reuse-desc]
  --   ∅ ⊢ no-reuse n [k; p : V] : ◇n[k; p : V]
  --
  -- An empty credit, passed when a join asks for a block that is unavailable. An empty credit
  -- satisfies every description, so a pass can give it the description of the credit that other
  -- branches return, and the branches then agree on it.
  | NoReuse Int (Maybe Contents)

  -- Constructor contexts (see "Constructor contexts" at the top). A context is built from a
  -- one-hole value K whose hole lies in a field of a block that K allocates:
  --
  --   K ::= □ | ptr C          C ::= roll C | injᵢ C | box F | box@r F
  --   F ::= K | (F, v) | (v, F)
  --
  -- The hole is a linear variable of the context, so it occurs exactly once, and it only
  -- occurs in K (not in the values v beside the path, nor in a closure).
  --
  --  ───────────────── [hole]
  --   □ : B* ⊢ □ : B*
  | Hole

  --   Γ, □ : B* ⊢ K : A*    K ≠ □
  --  ────────────────────────────── [ctx]
  --   Γ ⊢ ctx K :! ctx⁺⟨A,B⟩
  --
  --  ────────────────────────── [ctx-empty]
  --   ∅ ⊢ ctx □ :! ctx⟨A,A⟩
  --
  -- A fresh context is unique. The annotation is the hole's type `B`. Code generation records
  -- the context path in the headers of the blocks that K allocates on the path to the hole,
  -- which it locates by the position of `□` (no constructor or field names are involved).
  | Context AType VVal

  --   Γ₁ ⊢ c₁ :! ctx^f₁⟨A,B⟩    Γ₂ ⊢ c₂ :! ctx^f₂⟨B,C⟩
  --  ──────────────────────────────────────────────────── [ctx-append]
  --   Γ₁, Γ₂ ⊢ c₁ ++ c₂ :! ctx^(f₁ ∨ f₂)⟨A,C⟩
  --
  -- Plugs the `res` of `c₂` into the hole of `c₁` in place and keeps the hole of `c₂`; an empty
  -- `c₂` gives `c₁`. The paths of both are unique, so the path of the result is too. The result
  -- is nonempty if either context is. Extending a context with a nonempty one, such as
  -- `c ++ ctx K` with K ≠ □, is TRMC's step (`kk_cctx_extend_linear`): code generation does not
  -- test whether `c₂` is empty.
  | Append VVal VVal

  --   Γ₁ ⊢ c :! ctx⟨A,B⟩    Γ₂ ⊢ v : B*
  --  ─────────────────────────────────── [plug]
  --   Γ₁, Γ₂ ⊢ c[v] : A*
  --
  -- Fills the hole in place without checking uniqueness (`kk_cctx_apply_linear`); the empty
  -- context gives `v` itself. A context that may be shared is copied first (`[ctx-copy]`),
  -- which is Koka's `cctx/(++.)` (`kk_cctx_apply`).
  | Plug VVal VVal

  --   Γ ⊢ c : ctx^f⟨A,B⟩
  --  ───────────────────────────────── [ctx-copy]
  --   Γ ⊢ ctx-copy c :! ctx^f⟨A,B⟩
  --
  -- Makes a context unique by copying its path if `res` is shared (`kk_cctx_copy`). Elaboration
  -- uses it to plug or append a context that may be shared (Koka's `cctx/(++)` copies both
  -- arguments), and where a closure (such as the
  -- continuation of an effect that may resume more than once) passes a captured context to a
  -- unique parameter.
  | CtxCopy VVal
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
  --
  --   Γ₁ ⊢ v :! V    Γ₂, x :! V | J ⊢ e : W
  --  ─────────────────────────────────────────── [let-unique]
  --   Γ₁, Γ₂ | J ⊢ let x : V = ret v in e : W
  | Let Path VType VExpr VExpr

  --   Γ₁, ^Γ₂ | ∅ ⊢ʸ e₁ : V    Γ₂, x : V | J ⊢ e₂ : W    Γ₂ | J ⊢ e₃ : W
  --  ──────────────────────────────────────────────────────────────────────── [let-yield]
  --   Γ₁, Γ₂ | J ⊢ let x : V = e₁ yielding e₃ in e₂ : W
  --
  -- Koka's monadic bind: `e₁` may yield an effect, and then `e₃` runs instead of `e₂` (Koka's
  -- `if yielding() then e₃ else e₂`). While an effect yields, `e₁` returns a dummy value (see
  -- `[yielded]`), and `x` is not in scope in `e₃`, so the dummy is never inspected or dropped.
  -- `e₁` consumes Γ₁ in either case, as a function that yields first releases its owned
  -- arguments. Without a value to bind, the test is `let x : 𝟙 = ret () yielding e₃ in e₂`.
  -- Elaboration moves the coercions of the result of `e₁` into `e₂` (`Yields`); a value that
  -- may be a dummy is only bound by this rule.
  | LetYield Path VType VExpr VExpr VExpr

  --  ──────────────────────── [yielded]
  --   ∅ | J ⊢ʸ yielded : W
  --
  -- The dummy value of an expression that yields an effect, in the yielding branch of a
  -- `[let-yield]` (in place of a coercion of the dummy that a call returns). It is only allowed
  -- where the result may be a dummy (`⊢ʸ`): in the body of a definition or closure, in
  -- the bound expression of `[let-yield]`, and in their tail positions. Code generation fills
  -- its pointers with Koka's shared `box-any`, which the runtime may drop.
  | Yielded VType

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
  | App Path [VVal]

  -- Destructuring takes a mode: owned destructuring consumes the scrutinee and its binders are
  -- owned (a move); borrowed destructuring gives binders borrowed from the scrutinee. Unique
  -- destructuring consumes a unique scrutinee and its binders are unique; it is only allowed
  -- where the binder is the scrutinee's pointer: `[case]` on `⊕ᵢ Aᵢ`, `[deref]`, `[unroll]` and
  -- `[unpack]` (`keepsPointer`).
  --
  --   Γ₁ ⊢ v :q V    V at s̄ is U    Γ₂, x :q U ⊢ e : W
  --  ──────────────────────────────────────────────── [proj]
  --   Γ₁, Γ₂ ⊢ let_q x = v.s̄ in e : W
  --
  -- Reads and binds one part of a product, at the nonempty steps s̄ (each `fst` or `snd`)
  -- from v: `V₁ ⊗ V₂` at `fst s̄` is V₁ at s̄, and at `snd s̄` it is V₂ at s̄. For a variable v
  -- the binder is the path v.s̄, with that part's existing ownership; the other parts remain
  -- available, and the intermediate products are not bound. In layout normal form
  -- (`OrderFields`) a product is a right-nested chain of fields in memory order, and s̄
  -- selects one field: `snd`ⁱ `fst`, or `snd`ⁱ for the last one. Code generation then reads
  -- exactly that field, where the projection is.
  | Proj Mode VVal [Step] Path VExpr

  --   Γ₁ ⊢ v :q ⊕ᵢ Vᵢ    Γ₂, xᵢ :q Vᵢ ⊢ eᵢ : W   (for each i)
  --  ────────────────────────────────────────────────────────── [case]
  --   Γ₁, Γ₂ ⊢ case_q v of { injᵢ xᵢ -> eᵢ } : W
  --
  -- For a variable scrutinee z, branch i substitutes injᵢ xᵢ in credit descriptions.
  | CaseV Mode VVal [(Path,VExpr)]

  --   Γ₁ ⊢ v :q ⊕ⱼ∈J Aⱼ    Γ₂, xᵢ :q Aᵢ ⊢ eᵢ : W (i ∈ I)    Γ₂, d :q ⊕ⱼ∈J\I Aⱼ ⊢ e : W
  --  ──────────────────────────────────────────────────────────────────────────── [case-a]
  --   Γ₁, Γ₂ ⊢ case_q v of { injᵢ xᵢ -> eᵢ; _ d -> e } : W
  --
  -- Indices must belong to the sum and be distinct. Without a default every alternative occurs.
  -- The default excludes the matched indices without renumbering the remainder;
  -- it must be nonempty. No allocation or retagging occurs, at any mode: the binders are
  -- the block of v, with the tags of their alternatives (tag(xᵢ) = i).
  | CaseA Mode Path [(Int,Path,VExpr)] (Maybe (Path,VExpr))

  --   Γ₁ ⊢ v :q ⊕ᵢ∈J Aᵢ    Γ₂, x :q ⊕ᵢ∈J,i<k Aᵢ ⊢ e₁ : W    Γ₂, y :q ⊕ᵢ∈J,i≥k Aᵢ ⊢ e₂ : W
  --  ─────────────────────────────────────────────────────────────────────────── [split-a]
  --   Γ₁, Γ₂ ⊢ split_q v at k of { x -> e₁; y -> e₂ } : W
  --
  -- Both sides must be nonempty. Both binders retain the original indices,
  -- pointer and runtime tags. Even singleton partitions keep their sum wrapper.
  -- Like CaseA, this supports owned, borrowed and unique modes without repacking.
  | SplitA Mode Path Int (Path,VExpr) (Path,VExpr)

  --   Γ₁ ⊢ v :q A*    Γ₂, x :q A ⊢ e : W
  --  ───────────────────────────────────── [deref]
  --   Γ₁, Γ₂ ⊢ let_q ptr x = v in e : W
  | Deref Mode VVal Path VExpr

  --   Γ₁ ⊢ v :q T⟨B̄⟩    Γ₂, x :q unroll(T⟨B̄⟩) ⊢ e : W
  --  ──────────────────────────────────────────────────── [unroll]
  --   Γ₁, Γ₂ ⊢ let_q roll x = v in e : W
  | Unroll Mode Path Path VExpr

  --   Γ₁ ⊢ v :^ Box V    Γ₂, x :^ V ⊢ e : W
  --  ──────────────────────────────────────── [bunbox]
  --   Γ₁, Γ₂ ⊢ let^ box x = v in e : W
  --
  -- Reading the contents of a box is always borrowed. The paper's owned `[unbox]`, which keeps
  -- the block as a credit, is `[unbox-ru]` and requires the box to be unique. After `Loads`,
  -- `x` is a place in the block of `v`, which a read of `x` needs (see "Structural rules").
  | Unbox Mode Path Path VExpr

  --   Γ₁ ⊢ v :q Scalar raw    Γ₂, x : raw ⊢ e : W
  --  ───────────────────────────────────────────── [unscalar]
  --   Γ₁, Γ₂ ⊢ let_q scalar x = v in e : W
  --
  -- Reading a scalar copies its contents, which are trivial: `x` is a root, not a part of `v`.
  -- An owned read consumes the scalar (Koka's owned unbox, which frees a heap-backed one), and so
  -- does a unique one.
  | Unscalar Mode Path Path VExpr

  --   Γ₁ ⊢ v :^ Box V    Γ₂, x : V ⊢ e : W
  --  ─────────────────────────────────────────── [unbox-lazy]
  --   Γ₁, Γ₂ ⊢ let-lazy box x = v in e : W
  --
  -- Takes the contents of a box of the lazy value under evaluation without duplicating them
  -- (`Perceus`); the box is left *hollow* until `[box-in]` writes over it or it is freed. In the
  -- calculus this needs a hollow box type (a shared `◇n`). Trusted by `Linear`.
  | UnboxLazy Path Path VExpr

  --   Γ₁ ⊢ v :q ∃ā. V    Γ₂, x :q V[b̄/ā] ⊢ e : W    b̄ ∉ ftv(Γ₂, W)
  --  ────────────────────────────────────────────────────────────────── [unpack]
  --   Γ₁, Γ₂ ⊢ let_q pack[b̄] x = v in e : W
  --
  -- For a variable scrutinee z, credit descriptions substitute pack[b̄] x for z. The binder of
  -- a place is a place too.
  | Unpack Mode VVal [TVar] Path VExpr

  --   Γ₁ ⊢ v :^ V    lᵢ : V    Γ₂ ⊢ eᵢ : W    Γ₂ ⊢ e : W
  --  ────────────────────────────────────────────────────── [case-lit]
  --   Γ₁, Γ₂ ⊢ case v of { lᵢ -> eᵢ; _ -> e } : W
  | CaseLit VVal [(Lit,VExpr)] VExpr

  --   Γ₁ ⊢ v :^ T⟨B̄⟩    Cᵢ : ∀ā. V̄ᵢ -> T⟨ā⟩ ∈ Σ    Γ₂, x̄ᵢ :^ V̄ᵢ[B̄/ā] ⊢ eᵢ : W    Γ₂ ⊢ e : W
  --  ──────────────────────────────────────────────────────────────────────────────── [case-open]
  --   Γ₁, Γ₂ ⊢ case^ v of { Cᵢ(x̄ᵢ) -> eᵢ; _ -> e } : W
  --
  -- Matching on the tag of an open datatype, with a mandatory default. Always borrowed. An
  -- alternative binds one binder for each source field. For a variable v the binders are the
  -- parts of `v.C` at the steps of the fields of a right-nested product, like `[proj]`: field
  -- i of n at `snd`ⁱ `fst`, the last one at `snd`ⁿ⁻¹ (just `v.C` if there is one field).
  | CaseOpen Mode Path [(Name,[Path],VExpr)] VExpr

  --   Γ | ∅ ⊢ e : A*    ā ∉ ftv(Γ)
  --  ──────────────────────────────── [gen]
  --   Γ | J ⊢ gen ā. e : (∀ā. A)*
  --
  -- The introduction form of `[tyapp]`. An expression form (Koka has no value restriction);
  -- sound because the result is a type-erased pointer. The paper's `[gen]` on a value `v : A` is
  -- `gen ā. ret (ptr v)`.
  | Gen [TVar] VExpr

  --       Γ ⊢ e : W                             Γ ⊢ e : W
  --  ─────────────────────────── [drop]   ───────────────────────────────── [drop-ctx]
  --   Γ, x : A ⊢ drop x; e : W            Γ, x : ctx⟨A,B⟩ ⊢ drop x; e : W
  --
  -- Other unboxed values are destructured to drop their boxed components (`Common.dropValue`).
  -- A context is not: dropping it drops its `res` through the runtime, which skips the
  -- placeholder in the hole. The paper's `[dropru]` is derived
  -- from `[if-unique]` and `[unbox-ru]` (`Reuse.dropReuse`):
  --
  --   let r = drop-reuse x in e  ≜  let^ box x.contents = x in
  --                                 let r = (if-unique x then (let @ r' = x in discard x.contents; ret r')
  --                                          else (drop x; ret no-reuse n)) in e
  | Drop Path VExpr

  --       Γ ⊢ e : W
  --  ─────────────────────────── [free]
  --   Γ, r : ◇n ⊢ free r; e : W
  --
  -- Free the block of a reuse credit, or do nothing if the credit is empty. A full credit `◆n`
  -- is freed without a test.
  | Free Path VExpr

  --   Γ, y : V ⊢ e : W    V is not a credit
  --  ──────────────────────────────── [dup]
  --   Γ, x :^ V ⊢ val y = dup x; e : W
  --
  -- Duplicate an unboxed variable of any type (its pointers and contexts) into a new root
  -- `y`, the copy. The parts of `x` in scope are not parts of `y`, which has none until it
  -- is destructured. A boxed operand is duplicated through the pointer it was dereferenced
  -- from.
  | Dup Path Path VExpr

  --   Γ, x :! t ⊢ e₁ : W    Γ, x : t ⊢ e₂ : W    t = Box V with |V| defined, or t = T⟨B̄⟩* with T lazy
  --  ───────────────────────────────────────────────────────────────────────────────────── [if-unique]
  --   Γ, x : t ⊢ if-unique x then e₁ else e₂ : W
  --
  -- Branches on whether a box (`DropSpec`) or a lazy value (`Lazy`) is unique. A lazy value
  -- may be immediate, and then it is not unique. `Lazy` frees a unique lazy value under
  -- evaluation with `typed-lazy-free : ∀a. (!a) -> 1`, which does not drop its (taken) fields.
  | IsUnique Path VExpr VExpr

  --   Γ, r : ◆n[k; p : V] ⊢ e₁ : W    Γ ⊢ e₂ : W
  --  ─────────────────────────────────────────────── [if-full]
  --   Γ, r : ◇n[k; p : V] ⊢ if-full r then e₁ else e₂ : W
  --
  -- Branches on whether a credit holds a block (`ExpandReuse`): it is full in the first branch,
  -- and empty in the second, where nothing is left to consume.
  | IfFull Path VExpr VExpr

  --   Γ, z.contents : V, r : ◆n[tag(z); z.contents : V] ⊢ e : W    |V| = n
  --  ──────────────────────────────────────────────────────────── [unbox-ru]
  --   Γ, z :! Box V, z.contents :^ V ⊢ let @ r = z in e : W
  --
  -- A unique `Box V` whose contents were read (`[bunbox]`) splits into its contents and its
  -- block, the inverse of `[box-at]`: the contents are taken out of the block without
  -- reference counting, and the block becomes the credit `r` (named `z.credit`). With
  -- `[if-unique]` it makes `drop-reuse` of a box derivable. The block of `z` has tag tag(z).
  | UnboxRu Path Path VExpr

  --   Γ_c, x̄ :q̄ V̄ | J ⊢ e₁ : W    Γ, Γ_c | J, j : Γ_c; (q̄ V̄) -> W ⊢ e₂ : W
  --  ──────────────────────────────────────────────────────────────────── [join]
  --   Γ, Γ_c | J ⊢ join j(x̄ :q̄ V̄) = e₁ in e₂ : W
  --
  -- A join point captures the variables Γ_c that are free in its body (those that are
  -- not parts of other free variables, see "Structural rules"), and is not
  -- recursive (`j` is not in scope in its body). Its body may jump to outer joins. As it runs
  -- at most once, in the scope of its definition, it may also capture unique and borrowed
  -- variables (with their modes in Γ_c). Γ_c is a multiset: it holds an owned variable once
  -- for each reference that e₁ consumes.
  -- Since J is reset outside of tail positions, a jump cannot escape
  -- and is always a tail call. Join points only have owned parameters, except for contexts
  -- that are plugged in place (unique, see `[plug]`). Perceus only produces closed join
  -- points (Γ_c = ∅); only the late passes `JoinArgs` (for owned parameters) and
  -- `ExpandReuse` introduce captures. A captured variable must not be bound again in e₂, so every jump sees
  -- the same variable. The descriptions in V̄ do not name the parameters x̄, as every jump
  -- binds them to different values (a jump can only pass an empty credit for them).
  | Join Name [(Path,Mode,VType)] VExpr VExpr

  --   j : Γ_c; (q̄ V̄) -> W ∈ J    Γᵢ ⊢ vᵢ :qᵢ Vᵢ
  --  ──────────────────────────────────────────────── [jump]
  --   Γ_c, Γ₁, ..., Γₙ | J ⊢ jump j(v₁, ..., vₙ) : W
  --
  -- A jump passes the captured variables to the join point as well as its arguments.
  | Jump Name [VVal]
  deriving (Eq,Show)

-- Definitions `⊢ def`, with `f : ∀ā. (q̄ V̄) -> W ∈ Σ` and `x : ∀ā. V ∈ Σ`
data Def
  --   x̄ :q̄ V̄ | ∅ ⊢ʸ e : W
  --  ──────────────────────────────── [deffun]
  --   ⊢ fun f⟨ā⟩(x̄ :q̄ V̄) : W = e
  = DefFun{ defName :: Name, defParams :: [TVar], defArgs :: [(Path,Mode,VType)], defRes :: VType, defBody :: VExpr }

  --   ∅ | ∅ ⊢ʸ e : V
  --  ───────────────────────── [defval]
  --   ⊢ val x⟨ā⟩ : V = e
  --
  -- A top-level value, initialized when the module is loaded. It can be polymorphic.
  | DefVal{ defName :: Name, defParams :: [TVar], defType :: VType, defBody :: VExpr }
  deriving (Show)

-- signatures Σ
data Sig = SigFun [TVar] [(Mode,VType)] VType  -- f : ∀ā. (q̄ V̄) -> W
         | SigVal [TVar] VType                 -- x : ∀ā. V
         | SigCon [TVar] [VType] Name          -- C : ∀ā. V̄ -> T⟨ā⟩, a constructor of an open type T
         deriving (Show)

type Sigs = M.Map Name Sig

data Program = Program{ progName :: Name, progTypes :: TypeDefs, progSigs :: Sigs, progDefs :: [Def] }
