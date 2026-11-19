-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- The typed intermediate language.

  Each form below carries its typing rule. The rules follow the unboxing and linearity calculus
  of the fiplazy paper, with the changes recorded in FINDINGS.md. `CheckTypes` checks the types
  and `CheckLinear` the modes (after Perceus). Keep the rules and the checkers in sync.

  Contexts and judgements

    Γ ::= ∅ | Γ, x :q V | Γ, x :q A             variables
    J ::= ∅ | J, j : Γ_c; ∀ā. (q̄ V̄) -> W       join points in scope, with their captures
    Σ                                          signatures (`Sigs`) and datatypes (`TypeDefs`)

    Γ ⊢ a :q A       the boxed value a has type A
    Γ ⊢ v :q V       the unboxed value v has type V
    Γ | J ⊢ e : W    the expression e has type W and consumes every owned variable of Γ
    Γ | J ⊢ e :! W   the same, with a unique result
    ⊢ def            the top-level definition is well-typed

    `^Γ` marks every variable of Γ as borrowed. Rules omit J where they only pass it on to
    subexpressions in tail position; outside tail position J is ∅. The result mode works the
    same way: an expression in tail position has the mode of the expression around it (written
    `: W` for both), and one outside tail position is owned (except in `[let-unique]`). Only
    `[ret]`, `[call]`, `[yielded]` and the operations on contexts and cells have their own mode,
    and a jump has the mode of the body of its join point. A unique result can be used as an
    owned one.

    The tag of a box z, tag(z), is i if z is the binder of alternative i of a `[case-a]`, and 1
    otherwise (`Traversal.boxTag`).

  Structural rules

         Γ | J ⊢ e : W                       Γ, x :^ t, x :^ t | J ⊢ e : W
    ─────────────────────── [weaken]       ─────────────────────────────── [contract]
     Γ, x :^ t | J ⊢ e : W                   Γ, x :^ t | J ⊢ e : W

    - Variables of a trivial type are unrestricted and need no `dup` or `drop`. This includes
      the trivial contents of a box after the box is consumed, as `[bunbox]` copied them out.
    - A unique variable `x :! t` is owned and holds the only reference to its block. A borrowed
      use of x, or of a variable on its path, demotes it to `x : t`; branches agree on the
      weaker mode.
    - Borrowing is non-lexical, as in the paper, but the context is not ordered: the IR may
      borrow an owned variable z anywhere before z is consumed. The binders of a destructuring
      of z are its *children*, named by their paths (`z.left`, see `Path`). Borrowed uses of a
      child become invalid once z is consumed, so a call cannot borrow an argument that it also
      takes owned.
    - The children of an owned variable are owned. Consuming a child takes it out of its
      parent, and the parent is consumed once all of its children are: all fields of a product,
      the contents `z.contents` and the block `z.credit` of a box (which are not binders, see
      `[unbox-ru]`), or the single binder of any other destructuring. The binders of `[case-a]`, `[split-a]`, `[if-whnf]`, `[deref]`,
      `[unroll]` and `[unpack]` stand for the parent itself (or its pointer): consuming or
      testing them consumes or tests the parent.
    - Γ is a multiset: `[dup]` adds another owned reference under the same name. A reference
      held by a child outlives its parent, as consuming the parent consumes one reference of
      each child: after `dup z.left; drop z`, the context still holds `z.left : V`.
    - Code generation reads a block only at `[bunbox]`, where it copies the contents out.

  Constructor contexts

    A context `c : ctx⟨A,B⟩` is an `A` with one hole of type `B*` (Koka's `cctx<a,b>`). It is
    either empty (`ctx □`, with A = B), or a pointer `res` to a block together with the address
    of the hole. The hole is a field of the last block on the *context path* from `res`:
    - the blocks on the path were allocated by `[ctx]` (or copied by the runtime), and each
      header records which field leads to the next block (or is the hole);
    - every block on the path except `res` is referenced only by the block before it;
    - the hole holds a placeholder that is not a pointer, so dropping `res` skips it.
    A unique context also holds the only reference to `res`, so `[plug]` can write the hole in
    place. Duplicating a context demotes it to owned; `[ctx-copy]` makes it unique again by
    copying the path. Nothing else can reach into the path. A fresh context `ctx K` is a value,
    but `[ctx-append]`, `[plug]` and `[ctx-copy]` write to existing blocks, so they are
    expressions.

  Effect yields

    Koka compiles effects to a monadic form: while an effect yields, a call returns a dummy
    value and sets a global flag. In the dummy, every pointer is Koka's shared `box-any`, and
    tags and raw values are garbage. A function that may yield returns `Y W`: a W or the dummy.
    `[pure]` injects a value into `Y W`, and `[yielded]` is the dummy. Only `[let-yield]`
    eliminates `Y W`, by testing the flag, so the dummy is never inspected (apart from the
    unchecked `[cast-ev]`). There is no subtyping: elaboration converts between W and `Y W`
    with `[cast-ev]` or by eta-expansion.
    `Y` only occurs at the top of the type of an expression, a binder or a function result
    (`Types.wellYield`), so a type variable never stands for `Y W` and a parameter never has a
    type `Y W`. W itself contains no `Y`, credits or cells. A variable of type `Y W` is
    linear like a cell: it is never duplicated or dropped, and never live across an expression
    that may yield. A unique `Y W` is unique unless it is the dummy.
-}
module Backend.Typed.Syntax where

import qualified Data.Map as M
import Common.Name

-- Types. Type variables range over boxed types: a value at type `a` has the unboxed type `a*`.
-- Elaboration instantiates a Koka type argument V with `rep(V)`: `A` if `V = A*`, and otherwise
-- Koka's `box` of V (`boxA(V)`), which also boxes the parameters and results of functions in V.
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

-- Boxed types A, B: what a pointer points to.
--
-- - `Box V`, `1` and `⊕ᵢ Aᵢ` are *shapes*: their tags are known, so they can be destructured.
--   A `Box V` is always a heap block with a header, even for `𝟙`. Sums are flat: their
--   alternatives are `Box V` or `1` (so `a + 1` or `T⟨B̄⟩ + 1` is not a shape), indexed by their
--   runtime tags, which start at 1 as in Koka. A sub-sum keeps the tags of its alternatives.
-- - `Scalar raw` is Koka's `box` of a raw value: an immediate value, or a block allocated by
--   the runtime (such as a large `float64`). It has no tag, and it is never reused or tested
--   for uniqueness. `boxA` uses it for raw values and for products of one raw field
--   (`Types.scalarField`).
-- - `a`, `a⟨B̄⟩` and `T⟨B̄⟩` without a definition are opaque: their values are only passed around.
-- - `λā.A` only occurs as the argument of a higher-kinded variable, and applying it is
--   β-reduction. A partial application `T⟨B̄⟩` may occur there as well.
-- - `T⟨B̄⟩` with a declaration `data T⟨ā⟩ := A` is a datatype, which may be recursive (also
--   mutually) and nested. Named types are compared by name: only `[roll]`, `[unroll]` and
--   `[memoize]` relate `T⟨B̄⟩` to `A[B̄/ā]` (iso-recursive types). Queries on layout and
--   triviality may look at the definition (`Env.dataBody`).
-- - A lazy sum `L ~> S` is one flat sum at run time, split into the thunks L and the strict
--   alternatives S. Both are nonempty sums, and the tags of S are smaller than those of L. A
--   lazy datatype has the indirection `Box(τ*)` among its thunks. Elaboration pads every thunk
--   to at least the size of the indirection (`Elab.TypeInfo.conFieldTypes`), so that any
--   thunk can be overwritten by one; `[memoize]` checks the size.
data AType = ABox VType                 -- Box V
           | AScalar Raw                -- Scalar raw
           | AUnit                      -- 1
           | ASum [(Int,AType)]         -- ⊕ᵢ Aᵢ, indexed by tags
           | ALazy AType AType          -- L ~> S, a lazy sum of the thunks L and the strict alternatives S
           | AFun [(Mode,VType)] VType  -- (q̄ V̄) -> W, for top-level functions and closures alike
           | AForall [TVar] AType       -- ∀ā. A
           | AVar TVar                  -- a
           | AApp TVar [AType]          -- a⟨B̄⟩, an applied higher-kinded variable
           | ACon Name [AType]          -- T⟨B̄⟩, a named type
           | ALam [TVar] AType          -- λā. A, a partially applied type
           deriving (Eq,Show)

-- the sides of a lazy sum `L ~> S`: its strict alternatives S (`whnf`) and its thunks L (`delay`)
data Side = Whnf | Delay
          deriving (Eq,Show)

-- Unboxed types V, W: values of a fixed size, without a header.
--
-- - `A*` is the only pointer-sized type (`Types.isPtr`): a pointer to an `A`, or for a shape,
--   possibly an immediate value with its tag.
-- - Types are equal up to renaming of bound variables and β-reduction.
-- - A type is *trivial* if it contains no pointers (`Passes.Common.trivialTy`): `𝟙`, raw
--   types, `@reuse*`, and sums, products, existentials and named types of trivial types.
-- - `|V|` is the size of the heap block of a `Box V` (`Layout.blockSize`); unit has a block
--   with just a header. Fields are laid out in memory order, whatever the order of a product.
--   Heap blocks never contain credits or cells.
-- - `ctx⟨A,B⟩` is a constructor context (see "Constructor contexts" above), with the layout of
--   `A* ⊗ B*`. It is not trivial.
-- - A credit `◇n[k; p : V]` is the paper's space credit: an n-byte block, or nothing. A full
--   credit `◆n` always holds a block, and so does a nonempty context `ctx⁺`. A full one can be
--   used where one that may be empty is expected (`Query.expectV`), and branches that disagree
--   agree on the latter.
-- - A cell `cell_n⟨τ⟩` is the n-byte block of a lazy value under evaluation (the paper's
--   locked location), represented by the block pointer. Its contents were taken out by
--   `[lock]`, and other references must see a τ once `[memoize]` fills it. Cells are linear:
--   never duplicated or dropped, but consumed by `[memoize]`, `[if-unique-cell]`, or a call or
--   jump with a cell parameter. They never occur inside another type or a closure, and are
--   never live across `[let-yield]`. A `cell_n` can be used where `cell_m` is expected if m ≤ n.
-- - `Y V` is a `V` or the dummy value of an effect yield (see "Effect yields" above), with the
--   layout of `V`. It is linear like a cell.
data VType = VPtr AType                 -- A*
           | VUnit                      -- 𝟙
           | VSum [(Con,VType)]         -- ⊕ᵢ Vᵢ, n-ary (a Koka value type with several constructors)
           | VProd [(Field,VType)]      -- ⊗ᵢ fᵢ: Vᵢ, n-ary with n ≥ 1 (the fields of a Koka constructor)
           | VRaw Raw                   -- raw: unboxed primitives (`int32`, `float64`, `char`, ...)
           | VExists [TVar] VType       -- ∃ā. V
           | VReuse Fill Int (Maybe Contents) -- ◇n[k; p : V] or ◆n[k; p : V]: if nonempty, an n-byte block with tag k containing p
           | VCtx Fill AType AType      -- ctx⟨A,B⟩ or ctx⁺⟨A,B⟩: an A with a hole of type B*, nonempty if full
           | VCell Int AType            -- cell_n⟨τ⟩: the n-byte block of a lazy value under evaluation
           | VYield VType               -- Y V: a V, or the dummy value of an effect yield
           deriving (Eq,Show)

-- raw types: the primitive value types of Koka (`TypeInfo.rawType`), named by their C type
data Raw = RChar | RSSize | RIntPtr | RFloat64 | RFloat32
         | RInt64 | RInt32 | RInt16 | RInt8 | RUInt8
         deriving (Eq,Show)

-- The description `k; p : V` of a credit's block: the tag k in its header and its contents p,
-- an unevaluated value of type V with |V| = n. A description carries no ownership: its names
-- denote the values they were bound to, and need not be in scope. Descriptions are local to a
-- definition, so the parameters and results of functions carry none (`Query.signature`), and
-- those of join points do not mention the parameters (`[join]`). A pass may forget a
-- description, or just its tag (`_; p : V`, so that code generation writes it), but never
-- invent one.
data Contents = Contents (Maybe Int) VVal VType
              deriving (Eq,Show)

-- A full credit `◆n` holds a block, while a credit `◇n` may be empty (`no-reuse`). Likewise, a
-- full context `ctx⁺` has a `res` block, while a context `ctx` may be empty.
data Fill = Full | MaybeEmpty
          deriving (Eq,Show)

-- t ::= A | V
data Ty = A AType | V VType
          deriving (Eq,Show)

-- a datatype declaration `data T⟨ā⟩ := A` (see `AType`). A lazy datatype has a lazy sum as its
-- body. Without a body (`int`, `string`, open types, ...) the named type is abstract. The labels
-- of its constructors name the paths into its values (see `Path`); an abstract type has none.
data TypeDef = TypeDef{ tdefName :: Name, tdefParams :: [TVar], tdefBody :: Maybe AType, tdefLabels :: [ConLabel] }
             deriving (Show)

-- The label of a constructor: its name and the names of its fields (as in `conFieldNames`). A
-- datatype has the labels of its constructors in the order of their tags, which start at 1.
-- Printed paths name an alternative of a value of the datatype by its constructor, and a field
-- of the alternative by the name of the field.
data ConLabel = ConLabel{ lblCon :: Name, lblFields :: [Field] }
              deriving (Show)

type TypeDefs = M.Map Name TypeDef

-- the type of a literal, `type(l)` (`Query.litType`): `int*` and `string*` (abstract named
-- types), and raw `char` and `float64`
data Lit = LitInt Integer
         | LitFloat Double
         | LitChar Char
         | LitString String
         deriving (Eq,Show)

-- Variables are paths, as in the paper: a root followed by the steps of the destructurings
-- that lead to the variable, outermost first. For example, `let ptr x = z.left` binds
-- `z.left.deref`. A field of `[case-open]` adds two steps, its constructor and its field.
-- The binders of other forms are roots, and each root is bound only once in a definition.
-- `Paths` establishes these invariants after elaboration, and the other passes keep them.
data Path = Path Name [Step]
          deriving (Eq,Ord)

-- the steps from the scrutinee of a destructuring form to its binders
data Step = SField Int Field       -- [proj]
          | SInjV Int Con          -- [case]
          | SPack                  -- [unpack]
          | SDeref                 -- [deref]
          | SRoll                  -- [unroll]
          | SInjA Int Con | SRest  -- [case-a]: an alternative or the default
          | SLo | SHi              -- [split-a]
          | SWhnf | SDelay         -- [if-whnf]
          | SContents | SCredit    -- [bunbox]: the contents; [unbox-ru], [lock]: the rest of the block
          | SOpen Name             -- [case-open]
          deriving (Eq,Ord)

instance Show Path where
  show (Path x ss) = show x ++ concatMap (('.':) . show) ss

instance Show Step where
  show s = case s of
             SField _ f -> show f
             SInjV _ c -> show c
             SPack     -> "pack"
             SDeref    -> "deref"
             SRoll     -> "roll"
             SInjA _ c -> show c
             SRest     -> "rest"
             SLo       -> "lo"
             SHi       -> "hi"
             SWhnf     -> "whnf"
             SDelay    -> "delay"
             SContents -> "contents"
             SCredit   -> "credit"
             SOpen c   -> show c

-- the constructor of an alternative of a sum, for reading the IR: steps and types compare by tag
newtype Con = Con Name

instance Eq Con where
  _ == _ = True

instance Ord Con where
  compare _ _ = EQ

-- shown by its stem, which is unique within its datatype
instance Show Con where
  show (Con c) = show (unqualifyFull c)

-- an alternative without a constructor of its own, named by its tag
tagCon :: Int -> Con
tagCon i = Con (newName ("inj" ++ show i))

-- the name of a field of a product, for reading the IR: steps and types compare by position
newtype Field = Field Name

instance Eq Field where
  _ == _ = True

instance Ord Field where
  compare _ _ = EQ

instance Show Field where
  show (Field f) = show (unqualify f)

-- a field without a name of its own, named by its position (the fields of a constructor are
-- named as in the source, `TypeInfo.conFieldNames`)
posField :: Int -> Field
posField i = Field (newName ("field" ++ show i))

root :: Name -> Path
root x = Path x []

-- the name under which the type of the hole is bound in the one-hole value of a context
nameHole :: Path
nameHole = root (newHiddenName "hole")

-- Values `Γ ⊢ v :q t`. As in the paper, a borrowed value is structural: a variable, global,
-- literal, `()` or function, or a type application, tuple, injection, pack or cast of borrowed
-- values. A unique value is a variable, a context `ctx K`, `()`, a literal of a trivial type,
-- or a tuple, injection, pack or cast of unique values. All other values are owned.
--
-- Boxed values `Γ ⊢ a :q A`. Boxed variables are only operands (see `[var]`).
data AVal
  --   f : ∀ā. (q̄ V̄) -> W ∈ Σ    q̄ = ·
  --  ──────────────────────────────── [fun]
  --   ∅ ⊢ f :q ∀ā. (q̄ V̄) -> W
  --
  -- A top-level function used as a value is a static closure, at any mode. Only functions with
  -- owned parameters can be closures.
  = Fun Name

  --  ────────────── [unit]
  --   ∅ ⊢ () : 1
  | UnitA

  --   Γ ⊢ v : Aᵢ
  --  ──────────────────────── [inj-a]
  --   Γ ⊢ injᵢ v : ⊕ⱼ Aⱼ
  | InjA Int AType AVal

  --   data T⟨ā⟩ := A ∈ Σ    Γ ⊢ v : A[B̄/ā]
  --  ─────────────────────────────────────── [roll]
  --   Γ ⊢ roll v : T⟨B̄⟩
  --
  -- A no-op at run time.
  | Roll AType AVal

  --       Γ ⊢ v : S                          Γ ⊢ v : L
  --  ─────────────────── [whnf]          ─────────────────── [delay]
  --   Γ ⊢ whnf v : L ~> S                 Γ ⊢ delay v : L ~> S
  --
  -- No-ops at run time, as the lazy sum keeps the tags of L and S.
  | InjLazy Side AType AVal

  --   Γ ⊢ v : V
  --  ──────────────────── [box]
  --   Γ ⊢ box v : Box V
  --
  -- A fresh allocation (the paper's `alloc_n; box v`).
  | Box VVal

  --   Γ ⊢ v : raw
  --  ────────────────────────────── [scalar]
  --   Γ ⊢ scalar v : Scalar raw
  --
  -- Allocates only if the value is not immediate.
  | Scalar VVal

  --   C : ∀ā. V̄ -> T⟨ā⟩ ∈ Σ    Γᵢ ⊢ vᵢ : Vᵢ[B̄/ā]
  --  ───────────────────────────────────────────── [open-con]
  --   Γ̄ ⊢ C[B̄](v̄) : T⟨B̄⟩
  --
  -- A constructor of an open datatype, whose constructors are spread over modules. It takes
  -- one value for each source field, each with its own layout.
  | OpenCon Name [AType] [VVal]

  --   ⌊Γ⌋, x̄ : V̄ | ∅ ⊢ e : W    q̄ = ·
  --  ───────────────────────────────────────── [lam]
  --   Γ ⊢ fn(x̄ :q̄ V̄) : W -> e : (q̄ V̄) -> W
  --
  -- A closure consumes its captures Γ, which are owned in its body (`⌊Γ⌋`). Its parameters
  -- are owned.
  | Lam [(Path,Mode,VType)] VType VExpr

  --   Γ ⊢ v : V    |V| = n
  --  ────────────────────────────── [box-at]
  --   Γ, r : ◇n ⊢ box@r v : Box V
  --
  -- Allocates the box in the block of a credit, or freshly if the credit is empty (the paper's
  -- `[box]`). A full credit needs no test.
  | BoxAt Path VVal

  deriving (Eq,Show)

-- Unboxed values `Γ ⊢ v :q V`.
data VVal
  --  ───────────────── [var]
  --   x :q V ⊢ x :q V
  --
  -- As in the paper, a variable is a value only at an unboxed type. A boxed variable (bound by
  -- `[case-a]`, `[deref]` or `[unroll]`) is only an operand: of a destructuring, `[unscalar]`,
  -- `[drop]`, `[dup]`, `[if-unique]` or `[app]`. It cannot be stored again as a boxed value.
  = Var Path

  --   x : ∀ā. V ∈ Σ
  --  ───────────────────────── [glob]
  --   ∅ ⊢ x[B̄] :^ V[B̄/ā]
  --
  -- A top-level value is borrowed: an owned use needs `[dup-glob]` (unless it is trivial).
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

  --   Γᵢ ⊢ vᵢ :q Vᵢ   (for each i)
  --  ──────────────────────────────────────────────── [tuple]
  --   Γ₁, ..., Γₙ ⊢ (v₁, ..., vₙ) :q ⊗ᵢ fᵢ: Vᵢ
  --
  -- The fields are named by their position (`posField`).
  | Tuple [VVal]

  --   Γ ⊢ v : A
  --  ───────────────── [ptr]
  --   Γ ⊢ ptr v : A*
  --
  -- A no-op at run time.
  | Ptr AType AVal

  --   Γ ⊢ v :q V[B̄/ā]
  --  ──────────────────────────── [pack]
  --   Γ ⊢ pack[B̄] v :q ∃ā. V
  | Pack VType [AType] VVal

  --   Γ ⊢ v :q (∀ā. A)*
  --  ──────────────────────────── [tyapp]
  --   Γ ⊢ v[B̄] :q (A[B̄/ā])*
  --
  -- The paper's `[inst]`, on pointers so that it keeps the memory layout.
  | TyApp VVal [AType]

  --   Γ ⊢ v :q A*                    Γ ⊢ v :q any*
  --  ──────────────────── [up]       ───────────────────── [down]
  --   Γ ⊢ up v :q any*                Γ ⊢ down[B] v :q B*
  --
  -- Casts to and from Koka's top type `any`, for front ends whose typing the IR cannot express
  -- (such as erased dependent types). No-ops at run time that keep the mode. `[up]` is safe;
  -- `[down]` is unchecked and trusts the front end, so a destructuring of its result must not
  -- move above the test that justifies it. To match on a downcast with reuse, bind it first
  -- (`let x : B* = ret (down[B] z)`): a destructuring of `down[B] z` binds roots that borrow z.
  | Up VVal
  | Down AType VVal

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
  -- An empty credit. It satisfies every description, so it can take the description of the
  -- credit in the other branches.
  | NoReuse Int (Maybe Contents)

  -- Constructor contexts (see "Constructor contexts" at the top) are built from a one-hole
  -- value K, whose hole lies in a field of a block that K allocates:
  --
  --   K ::= □ | ptr C          C ::= roll C | injᵢ C | whnf C | delay C | box F | box@r F
  --   F ::= K | (F, v) | (v, F)
  --
  -- The hole occurs exactly once, in K (not in the values v beside the path, nor in a closure).
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
  -- A fresh context is unique. The annotation is B. Code generation records the context path
  -- in the headers of the blocks on the way to `□`.
  | Context AType VVal

  --   Γ ⊢ v :q V
  --  ───────────────────── [pure]
  --   Γ ⊢ pure v :q Y V
  --
  -- A value that is not the dummy of a yield. A no-op at run time.
  | Pure VVal
  deriving (Eq,Show)

-- Whether a join point is recursive (`[join-rec]`), with its result type.
data Recursion = NonRec | Rec VType
  deriving (Eq,Show)

mapRecursion :: (VType -> VType) -> Recursion -> Recursion
mapRecursion _ NonRec = NonRec
mapRecursion f (Rec t) = Rec (f t)

recResult :: Recursion -> [VType]
recResult NonRec = []
recResult (Rec t) = [t]

-- Expressions `Γ | J ⊢ e : W`. As in the paper, expressions always have an unboxed type.
data VExpr
  --   Γ ⊢ v :q V
  --  ────────────────── [ret]
  --   Γ ⊢ ret v :q V
  = Ret VVal

  --   Γ₁, ^Γ₂ | ∅ ⊢ e₁ : V    Γ₂, x : V | J ⊢ e₂ : W
  --  ─────────────────────────────────────────────────── [let]
  --   Γ₁, Γ₂ | J ⊢ let x : V = e₁ in e₂ : W
  --
  --   Γ₁, ^Γ₂ | ∅ ⊢ e₁ :! V    Γ₂, x :! V | J ⊢ e₂ : W
  --  ─────────────────────────────────────────────────── [let-unique]
  --   Γ₁, Γ₂ | J ⊢ let x : V = e₁ in e₂ : W
  --
  -- The binder is unique if every tail position of e₁ has a unique result: a unique value, a
  -- call of a function with a unique result, `[ctx-append]` or `[ctx-copy]`.
  | Let Path VType VExpr VExpr

  --   Γ₁, ^Γ₂ | ∅ ⊢ e₁ : Y V    Γ₂, x : V | J ⊢ e₂ : W    Γ₂ | J ⊢ e₃ : W
  --  ──────────────────────────────────────────────────────────────────────── [let-yield]
  --   Γ₁, Γ₂ | J ⊢ let x : V = e₁ yielding e₃ in e₂ : W
  --
  --   Γ₁, ^Γ₂ | ∅ ⊢ e₁ :! Y V    Γ₂, x :! V | J ⊢ e₂ : W    Γ₂ | J ⊢ e₃ : W
  --  ──────────────────────────────────────────────────────────────────────── [let-yield-unique]
  --   Γ₁, Γ₂ | J ⊢ let x : V = e₁ yielding e₃ in e₂ : W
  --
  -- Koka's monadic bind (`if yielding() then e₃ else e₂`), the only elimination of `Y V`. If e₁
  -- yields, it returns the dummy and e₃ runs, where x is not in scope. e₁ consumes Γ₁ in either
  -- case. Without a value to bind, the test is `let x : 𝟙 = ret (pure ()) yielding e₃ in e₂`.
  -- No variable of a type `Y U` or a cell is live in e₂ or e₃.
  | LetYield Path VType VExpr VExpr VExpr

  --   W contains no credits or cells
  --  ──────────────────────────── [yielded]
  --   ∅ | J ⊢ yielded :q Y W
  --
  -- The dummy value, for example in the yielding branch of a `[let-yield]`. It has either mode,
  -- since `:! Y W` promises nothing about the dummy. Code generation fills its pointers with
  -- Koka's shared `box-any`.
  | Yielded VType

  --  ───────────────────────── [unreachable]
  --   Γ | J ⊢ unreachable : W
  --
  -- An impossible alternative, such as the thunks of a forced value. Γ may hold anything,
  -- including credits and cells. Code generation aborts.
  | Unreachable VType

  --   Γ ⊢ v : U    |U| = |V|
  --  ──────────────────────────── [cast-ev]
  --   Γ | J ⊢ cast-ev[V] v : V
  --
  -- Adds or removes `Y`s anywhere in the type of v (`|·|` erases them, `Types.eraseY`). A no-op
  -- at run time, and unchecked, as the IR has no effects: elaboration emits it where Koka knows
  -- that the value is not a dummy. Examples are an effect variable instantiated at a total
  -- effect, and the result of a call that Koka does not test (a total call, a call in
  -- `std/core/hnd`, which tests the flag itself, or a call under `unsafe-total`). It also lets a
  -- function that never yields be used as one that may. In `std/core/hnd`, a dummy may pass at
  -- a type variable, where it is only passed on, duplicated or dropped. `[pure]`, not
  -- `cast-ev`, injects a value into `Y` at the top of a type.
  | CastEv VType VVal

  --   f : ∀ā. (q̄ V̄) -> q W ∈ Σ    Γᵢ ⊢ vᵢ :qᵢ Vᵢ[B̄/ā]
  --  ───────────────────────────────────────────────── [call]
  --   Γ₁, ..., Γₙ ⊢ f[B̄](v₁, ..., vₙ) :q W[B̄/ā]
  --
  -- The modes come from the signature of f.
  | Call Name [AType] [VVal]

  --   Γ₀ ⊢ v : (V̄) -> W    Γᵢ ⊢ vᵢ : Vᵢ
  --  ──────────────────────────────────────── [app]
  --   Γ₀, Γ₁, ..., Γₙ ⊢ v(v₁, ..., vₙ) : W
  --
  -- Applying a closure consumes it. The parameters of closures are always owned.
  | App Path [VVal]

  -- Destructuring. As in the paper, destructuring borrows its scrutinee and has no mode; only
  -- `[unbox-ru]`, `[lock]` and `[unscalar]` take ownership. For a variable scrutinee z, the
  -- binders are children of z (see "Structural rules"): they are owned where z is owned, and
  -- those that stand for z itself are unique where z is unique. For any other scrutinee, the
  -- binders are roots that borrow the variables of the scrutinee in the whole alternative.
  --
  --   Γ₁ ⊢ v :^ ⊗ⱼ fⱼ: Vⱼ    Γ₂, x :^ Vᵢ ⊢ e : W
  --  ──────────────────────────────────────────── [proj]
  --   Γ₁, Γ₂ ⊢ let x = v.fᵢ in e : W
  --
  -- Binds field i of a product; the other fields stay available. Products are logical: their
  -- fields are in source order and may be products themselves, and code generation lays out
  -- their leaves in memory order (`Layout.layout`).
  | Proj VVal Int Path VExpr

  --   Γ₁ ⊢ v :^ ⊕ᵢ Vᵢ    Γ₂, xᵢ :^ Vᵢ ⊢ eᵢ : W   (for each i)
  --  ────────────────────────────────────────────────────────── [case]
  --   Γ₁, Γ₂ ⊢ case v of { injᵢ xᵢ -> eᵢ } : W
  --
  -- Every alternative occurs once; code generation tests them in the given order. For a
  -- variable scrutinee z, branch i substitutes injᵢ xᵢ for z in credit descriptions.
  | CaseV VVal [(Int,Path,VExpr)]

  --   Γ₁ ⊢ v :^ ⊕ⱼ∈J Aⱼ    Γ₂, xᵢ :^ Aᵢ ⊢ eᵢ : W (i ∈ I)    Γ₂, d :^ ⊕ⱼ∈J\I Aⱼ ⊢ e : W
  --  ──────────────────────────────────────────────────────────────────────────── [case-a]
  --   Γ₁, Γ₂ ⊢ case v of { injᵢ xᵢ -> eᵢ; _ d -> e } : W
  --
  -- The indices are distinct and belong to the sum. The default is nonempty and keeps the tags
  -- of the remaining alternatives; without one, every alternative occurs. The binders are the
  -- block of v, with the tags of their alternatives (tag(xᵢ) = i).
  | CaseA Path [(Int,Path,VExpr)] (Maybe (Path,VExpr))

  --   Γ₁ ⊢ v :^ ⊕ᵢ∈J Aᵢ    Γ₂, x :^ ⊕ᵢ∈J,i<k Aᵢ ⊢ e₁ : W    Γ₂, y :^ ⊕ᵢ∈J,i≥k Aᵢ ⊢ e₂ : W
  --  ─────────────────────────────────────────────────────────────────────────── [split-a]
  --   Γ₁, Γ₂ ⊢ split v at k of { x -> e₁; y -> e₂ } : W
  --
  -- Both sides are nonempty sums and keep their tags.
  | SplitA Path Int (Path,VExpr) (Path,VExpr)

  --   Γ₁ ⊢ v :^ L ~> S    Γ₂, s :^ S ⊢ e₁ : W    Γ₂, l :^ L ⊢ e₂ : W
  --  ──────────────────────────────────────────────────────────────── [if-whnf]
  --   Γ₁, Γ₂ ⊢ if-whnf v of { whnf s -> e₁; delay l -> e₂ } : W
  --
  -- Tests whether a lazy value is evaluated, by its tag. As for `[split-a]`, both sides keep
  -- their tags.
  | IfWhnf Path (Path,VExpr) (Path,VExpr)

  --   Γ₁ ⊢ v :^ A*    Γ₂, x :^ A ⊢ e : W
  --  ───────────────────────────────────── [deref]
  --   Γ₁, Γ₂ ⊢ let ptr x = v in e : W
  | Deref VVal Path VExpr

  --   data T⟨ā⟩ := A ∈ Σ    Γ₁ ⊢ v :^ T⟨B̄⟩    Γ₂, x :^ A[B̄/ā] ⊢ e : W
  --  ──────────────────────────────────────────────────────────────── [unroll]
  --   Γ₁, Γ₂ ⊢ let roll x = v in e : W
  | Unroll Path Path VExpr

  --   Γ₁ ⊢ v :^ Box V    Γ₂, x :^ V ⊢ e : W
  --  ──────────────────────────────────────── [bunbox]
  --   Γ₁, Γ₂ ⊢ let box x = v in e : W
  --
  -- Reads the contents of a box; code generation copies them out of the block. The paper's
  -- owned `[unbox]` is `[unbox-ru]`.
  | Unbox Path Path VExpr

  --   Γ₁ ⊢ v :q Scalar raw    Γ₂, x : raw ⊢ e : W
  --  ───────────────────────────────────────────── [unscalar]
  --   Γ₁, Γ₂ ⊢ let_q scalar x = v in e : W
  --
  -- Copies the contents, which are trivial, so x is a root. The only destructuring with a mode:
  -- an owned or unique read consumes the scalar (and frees it if it is in the heap).
  | Unscalar Mode Path Path VExpr

  --   Γ₁ ⊢ v :^ ∃ā. V    Γ₂, x :^ V[b̄/ā] ⊢ e : W    b̄ ∉ ftv(Γ₂, W)
  --  ────────────────────────────────────────────────────────────────── [unpack]
  --   Γ₁, Γ₂ ⊢ let pack[b̄] x = v in e : W
  --
  -- For a variable scrutinee z, credit descriptions substitute pack[b̄] x for z.
  | Unpack VVal [TVar] Path VExpr

  --   Γ₁ ⊢ v :^ V    lᵢ : V    Γ₂ ⊢ eᵢ : W    Γ₂ ⊢ e : W
  --  ────────────────────────────────────────────────────── [case-lit]
  --   Γ₁, Γ₂ ⊢ case v of { lᵢ -> eᵢ; _ -> e } : W
  | CaseLit VVal [(Lit,VExpr)] VExpr

  --   Γ₁ ⊢ v :^ T⟨B̄⟩    Cᵢ : ∀ā. V̄ᵢ -> T⟨ā⟩ ∈ Σ    Γ₂, x̄ᵢ :^ V̄ᵢ[B̄/ā] ⊢ eᵢ : W    Γ₂ ⊢ e : W
  --  ──────────────────────────────────────────────────────────────────────────────── [case-open]
  --   Γ₁, Γ₂ ⊢ case v of { Cᵢ(x̄ᵢ) -> eᵢ; _ -> e } : W
  --
  -- Matches on the tag of an open datatype; the default is required. For a variable v, the
  -- binders are the fields of the product `v.C` (just `v.C` if there is one field).
  | CaseOpen Path [(Name,[Path],VExpr)] VExpr

  --   Γ | ∅ ⊢ e : A*    ā ∉ ftv(Γ)
  --  ──────────────────────────────── [gen]
  --   Γ | J ⊢ gen ā. e : (∀ā. A)*
  --
  -- The introduction form of `[tyapp]`. It is an expression, as Koka has no value restriction;
  -- this is sound because the result is a pointer. The paper's `[gen]` on a value `v : A` is
  -- `gen ā. ret (ptr v)`.
  | Gen [TVar] VExpr

  --       Γ ⊢ e : W                             Γ ⊢ e : W
  --  ─────────────────────────── [drop]   ───────────────────────────────── [drop-ctx]
  --   Γ, x : A ⊢ drop x; e : W            Γ, x : ctx⟨A,B⟩ ⊢ drop x; e : W
  --
  -- Other unboxed values are dropped by destructuring them (`Passes.Common.dropValue`).
  -- Dropping a context drops its `res`. The paper's `[dropru]` is derived (`Reuse.dropReuse`):
  --
  --   let r = drop-reuse x in e  ≜  let box x.contents = x in
  --                                 let r = (if-unique x then (let @ r' = x in discard x.contents; ret r')
  --                                          else (drop x; ret no-reuse n)) in e
  | Drop Path VExpr

  --       Γ ⊢ e : W
  --  ─────────────────────────── [free]
  --   Γ, r : ◇n ⊢ free r; e : W
  --
  -- Frees the block of a credit, if it has one. A full credit needs no test.
  | Free Path VExpr

  --   Γ, x : t ⊢ e : W    t is not a credit or a cell
  --  ──────────────────────────────── [dup]
  --   Γ, x :^ t ⊢ dup x; e : W
  --
  -- x gains an owned reference under the same name, so it is still a child of its parent.
  -- With `[contract]`, x also stays available borrowed. A boxed operand is duplicated through
  -- its pointer.
  | Dup Path VExpr

  --   Γ, x :! Box V ⊢ e₁ : W    Γ, x : Box V ⊢ e₂ : W    |V| defined
  --  ────────────────────────────────────────────────────────────────── [if-unique]
  --   Γ, x : Box V ⊢ if-unique x then e₁ else e₂ : W
  --
  --   Γ, c : ◆n | J ⊢ e₁ : W    Γ, c : cell_n⟨τ⟩ | J ⊢ e₂ : W
  --  ───────────────────────────────────────────────────────────── [if-unique-cell]
  --   Γ, c : cell_n⟨τ⟩ | J ⊢ if-unique c then e₁ else e₂ : W
  --
  -- Tests whether a box or a cell is unique (`DropSpec`). Nobody else sees a unique cell, so
  -- it is just an empty block: a full credit.
  | IsUnique Path VExpr VExpr

  --   Γ, r : ◆n[k; p : V] ⊢ e₁ : W    Γ ⊢ e₂ : W
  --  ─────────────────────────────────────────────── [if-full]
  --   Γ, r : ◇n[k; p : V] ⊢ if-full r then e₁ else e₂ : W
  --
  -- Tests whether a credit holds a block (`ExpandReuse`).
  | IfFull Path VExpr VExpr

  --   Γ, z.contents :^ V, z.credit : ◆n[tag(z); z.contents : V] ⊢ e : W    |V| = n
  --  ──────────────────────────────────────────────────────────────── [unbox-ru]
  --   Γ, z :! Box V, z.contents :^ V ⊢ let @ z.credit = z in e : W
  --
  -- The paper's `[destruct]`, and the inverse of `[box-at]`: a unique box whose contents were
  -- read splits into its contents and its block, which becomes the credit `z.credit`. No
  -- reference counts change. The body consumes both children instead of z. The description of
  -- the credit names the contents, which the block still holds until it is written.
  | UnboxRu Path VExpr

  --   Γ, z :^ Box V, r : ◆n[tag(z); z.contents : V] ⊢ e : W    |V| = n
  --  ─────────────────────────────────────────────────────────────────── [copy-ru]
  --   Γ, z :^ Box V ⊢ let @copy r = z in e : W
  --
  -- Like `[unbox-ru]`, but for a box that may be shared: the credit r is a fresh block that
  -- holds a bitwise copy of z, with the same tag. No reference counts change, as the block of z
  -- still holds the copied fields. As the credit has the same description as in `[unbox-ru]`,
  -- the branches of an `[if-unique]` can agree on it (`FillCredits`).
  | CopyRu Path Path VExpr

  --   Γ, z.contents :^ V, z.credit : cell_|V|⟨τ⟩ | J ⊢ e : W
  --  ──────────────────────────────────────────────────────── [lock]
  --   Γ, z : Box V, z.contents :^ V | J ⊢ let lock z.credit = z in e : W
  --                 (z = y.roll.delay.p.injⱼ with y : τ, p ∈ {lo,hi}*)
  --
  -- Like `[unbox-ru]`, but for an owned thunk that may be shared (the `delay` step shows that
  -- z is a thunk). Its contents are taken out, and its block becomes the cell `z.credit`,
  -- which `[memoize]` must fill (or `[if-unique-cell]` frees). Consuming both children
  -- consumes z, and so the pointer it was matched from.
  | Lock Path VExpr

  --   Γ_c, x̄ :q̄ V̄ | J ⊢ e₁ : W    Γ, Γ_c | J, j : Γ_c; ∀ā. (q̄ V̄) -> W ⊢ e₂ : W    ā ∉ ftv(Γ_c, W)
  --  ────────────────────────────────────────────────────────────────────────────────── [join]
  --   Γ, Γ_c | J ⊢ join j⟨ā⟩(x̄ :q̄ V̄) = e₁ in e₂ : W
  --
  -- A join point captures the variables Γ_c that are free in its body (but not the children
  -- of other free variables), with their modes: as it runs at most once, in the scope of its
  -- definition, it may also capture unique and borrowed variables. It is not recursive, but
  -- its body may jump to outer joins.
  -- As J is ∅ outside tail positions, every jump is a tail call. The parameters are owned,
  -- except for contexts that are plugged in place (unique). Perceus only produces closed join
  -- points; captures come from `DropSpec`, `JoinArgs` and `ExpandReuse`. A captured variable
  -- is not bound again in e₂. The descriptions in V̄ do not mention x̄. The type parameters ā
  -- abstract over existentials that are unpacked before the jumps (`Elab.Match`).
  --
  --   ^Γ_c, x̄ :q̄ V̄ | j : ^Γ_c; ∀ā. (q̄ V̄) -> W ⊢ e₁ : W
  --   Γ, Γ_c | J, j : ^Γ_c; ∀ā. (q̄ V̄) -> W ⊢ e₂ : W    ā ∉ ftv(Γ_c, W)
  --  ────────────────────────────────────────────────────────────────────────────────── [join-rec]
  --   Γ, Γ_c | J ⊢ join rec j⟨ā⟩(x̄ :q̄ V̄) : W = e₁ in e₂ : W
  --
  -- A loop: j is in scope in its body, which may run many times. It therefore only borrows its
  -- captures, which are consumed after the loop if they are owned, and a captured variable is
  -- not bound again in e₂. Its body cannot jump to outer joins, and has the result mode of the
  -- context. Its parameters may have any mode: a borrowed one is lent anew by every jump. W is
  -- annotated for the jumps in the body. Recursive joins come from self tail calls, after
  -- Perceus, and are closed until `JoinArgs` turns invariant borrowed parameters into
  -- captures. (Not in the paper.)
  | Join Recursion Name [TVar] [(Path,Mode,VType)] VExpr VExpr

  -- Operations on contexts and cells. They write to memory that they did not allocate, or
  -- change reference counts, so they are expressions and cannot be duplicated or reordered
  -- like values. Their operands are values.
  --
  --   Γ₁ ⊢ c₁ :! ctx^f₁⟨A,B⟩    Γ₂ ⊢ c₂ :! ctx^f₂⟨B,C⟩
  --  ──────────────────────────────────────────────────── [ctx-append]
  --   Γ₁, Γ₂ | J ⊢ c₁ ++ c₂ :! ctx^(f₁ ∨ f₂)⟨A,C⟩
  --
  -- Plugs the `res` of c₂ into the hole of c₁ in place, and keeps the hole of c₂. An empty c₂
  -- gives c₁. If c₂ is nonempty, this is TRMC's step and needs no test.
  | Append VVal VVal

  --   Γ₁ ⊢ c :! ctx⟨A,B⟩    Γ₂ ⊢ v : B*
  --  ─────────────────────────────────── [plug]
  --   Γ₁, Γ₂ | J ⊢ c[v] : A*
  --
  -- Fills the hole in place, without a test. The empty context gives v itself, which may be
  -- shared, so the result is owned.
  | Plug VVal VVal

  --   Γ ⊢ c : ctx^f⟨A,B⟩
  --  ───────────────────────────────── [ctx-copy]
  --   Γ | J ⊢ ctx-copy c :! ctx^f⟨A,B⟩
  --
  -- Copies the path if `res` is shared. Elaboration uses it before plugging or appending a
  -- context that may be shared, and where a closure passes a captured context to a unique
  -- parameter.
  | CtxCopy VVal

  --   data T⟨ā⟩ := L ~> S ∈ Σ    Sₖ[B̄/ā] = Box V    Γ ⊢ v : V    |V| ≤ n
  --  ──────────────────────────────────────────────────────────────────── [memoize]
  --   Γ, c : cell_n⟨T⟨B̄⟩⟩ | J ⊢ memoize c (whnf (injₖ v)) : T⟨B̄⟩*
  --
  --   data T⟨ā⟩ := L ~> S ∈ Σ    Lₖ[B̄/ā] = Box V    Γ ⊢ v : V    |V| ≤ n
  --  ──────────────────────────────────────────────────────────────────── [memoize-delay]
  --   Γ, c : cell_n⟨T⟨B̄⟩⟩ | J ⊢ memoize c (delay (injₖ v)) : T⟨B̄⟩*
  --
  -- Writes alternative k into the block of the cell, keeping its reference count, and returns
  -- the block. A strict k is the paper's `memoize`; a thunk k replaces the thunk by another
  -- (Koka's step mode), and the indirection is the paper's `indirect`.
  | Memoize VVal Side Int VVal

  --   j : Γ_c; ∀ā. (q̄ V̄) -> W ∈ J    Γᵢ ⊢ vᵢ :qᵢ Vᵢ[B̄/ā]
  --  ──────────────────────────────────────────────────────── [jump]
  --   Γ_c, Γ₁, ..., Γₙ | J ⊢ jump j[B̄](v₁, ..., vₙ) : W
  --
  -- A jump passes the captures of the join point as well as its arguments.
  | Jump Name [AType] [VVal]
  deriving (Eq,Show)

-- Definitions `⊢ def`, with `f : ∀ā. (q̄ V̄) -> q W ∈ Σ` and `x : ∀ā. V ∈ Σ`
data Def
  --   x̄ :q̄ V̄ | ∅ ⊢ e :q W
  --  ──────────────────────────────── [deffun]
  --   ⊢ fun f⟨ā⟩(x̄ :q̄ V̄) :q W = e
  --
  -- The result is owned or unique. Elaboration, imported functions and closures only have
  -- owned results.
  = DefFun{ defName :: Name, defParams :: [TVar], defArgs :: [(Path,Mode,VType)], defResMode :: Mode, defRes :: VType, defBody :: VExpr }

  --   ∅ | ∅ ⊢ e : V
  --  ───────────────────────── [defval]
  --   ⊢ val x⟨ā⟩ : V = e
  --
  -- A top-level value, initialized when the module is loaded. It may be polymorphic.
  | DefVal{ defName :: Name, defParams :: [TVar], defType :: VType, defBody :: VExpr }
  deriving (Show)

-- signatures Σ
data Sig = SigFun [TVar] [(Mode,VType)] Mode VType  -- f : ∀ā. (q̄ V̄) -> q W
         | SigVal [TVar] VType                      -- x : ∀ā. V
         | SigCon [TVar] [VType] Name               -- C : ∀ā. V̄ -> T⟨ā⟩, a constructor of an open type T
         deriving (Show)

type Sigs = M.Map Name Sig

data Program = Program{ progName :: Name, progTypes :: TypeDefs, progSigs :: Sigs, progDefs :: [Def] }
