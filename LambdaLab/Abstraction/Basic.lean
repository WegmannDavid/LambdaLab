/-!
# Abstraction

The indexed abstraction structure, shaped by the pipeline it has to host:
tokenize → parse → elaborate.

Two decisions, both forced by that pipeline:

* **`abstract` is partial** (`Except Diag`). A parser rejects `["(", "("]`, a type checker
  rejects ill-typed terms — the total version cannot host either stage. A rejection carries a
  diagnostic, and **no law mentions it**: error reports are an informal convention between a
  stage and its user, and only success is formalized. The laws below are stated at `.ok`.

* **Both directions are laws.** Soundness — realize an annotation, re-abstract, land on its
  index — and completeness, `lossless`: every accepted concrete is `realize` of some annotation.
  Without the second a morphism may take your concrete and hand back something unrelated to it,
  and be well-formed; the reverse round trip is the one a compiler needs to quote what the user
  wrote.

  This was once a per-morphism predicate, on the argument that a Hindley–Milner elaborator cannot
  satisfy it — the fiber over a typed term is every combination of written-vs-omitted annotations
  *jointly constrained by unification*, so no node-local family covers it and only the tautological
  `{c // abstract c = some a}` does. That argument is right, and it establishes which family to
  choose rather than that the law is unsatisfiable: the elaboration stage was already built on the
  tautological family, and satisfies the law as it stands. `ofFibers` is that choice, made
  available to anything that needs it.

  What the law does *not* say is that `abstract` forgot nothing. Evaluation satisfies it while
  discarding every redex. It says the morphism's annotation is an adequate record of what
  `abstract` collapsed — a claim about the annotation, not about the algorithm.

What every stage keeps *without* completeness: `abstract_realize` at `default` is the
canonical-print round trip — print canonically, re-`abstract`, recover the same
abstract value. That is the compiler-grade guarantee; `Lossless` is only about
preserving the *user's* spelling.

On `default` for an elaborator: the fully-annotated spelling makes it cheap to
provide; the fully-erased spelling is principal typing (`JComplete.elabSubst_principal_below`
for STLC) — a theorem about an instance, not a field obligation.

Argument order is `(Concrete, Abstract)`: a morphism `A ⇝ B` reads concrete-to-
abstract, matching the 1-cell direction of `Abstraction/Bicat.lean`.
-/

set_option autoImplicit false

/-! The structure is declared in `LambdaLab`, not in `LambdaLab.Abstraction`, so that its full name
is `LambdaLab.Abstraction` and its API below lands in the namespace of the same name — the shape
`Nat` and `Finset` have. Declaring it inside `LambdaLab.Abstraction` would name it
`LambdaLab.Abstraction.Abstraction` and stutter through every projection. -/

/-! `Except.map` on a known constructor, which core Lean leaves to unfolding. -/

@[simp] theorem Except.map_ok_eq {ε α β : Type} (f : α → β) (a : α) :
    (Except.ok a : Except ε α).map f = .ok (f a) := rfl

@[simp] theorem Except.map_error_eq {ε α β : Type} (f : α → β) (e : ε) :
    (Except.error e : Except ε α).map f = .error e := rfl

theorem Except.map_eq_ok_iff {ε α β : Type} {f : α → β} {x : Except ε α} {b : β} :
    x.map f = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Except.map]

namespace LambdaLab

/-- A bijection, with both round-trips as fields.

This is Mathlib's `Equiv`, and this file used `Equiv` until the cost was measured: everything
the executables import is linked into them, and one Mathlib import — any Mathlib import — puts
about 1300 modules into that closure. Four fields are not worth 1300 modules; removing this one
and `Nat.digits` in `Parser/Numeral` took `stlc` from 129 MB to 2.8 MB. The seventeen modules
outside the executables' import cone still use Mathlib freely; this is not a policy against
Mathlib, only against Mathlib *below* the executables, `Stlc` and `Float`. -/
structure Iso (α β : Type) where
  /-- The forward map. -/
  toFun : α → β
  /-- The backward map. -/
  invFun : β → α
  /-- `invFun` undoes `toFun`. -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- `toFun` undoes `invFun`. -/
  right_inv : ∀ b, toFun (invFun b) = b

namespace Iso

variable {α β : Type}

instance : CoeFun (Iso α β) (fun _ => α → β) := ⟨Iso.toFun⟩

/-- The inverse bijection — the two round-trip laws simply swap roles. -/
def symm (e : Iso α β) : Iso β α := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

end Iso

/-! ## Diagnostics

What a rejection says. A diagnostic points into the input of the stage that raised it; `locate`
(below) pulls a location in a stage's output back into its input, so a pipeline can point a late
stage's diagnostic at the source text. Both are informal: nothing is proved about them. -/

/-- Where a diagnostic points. -/
inductive Loc where
  /-- Nowhere in particular. -/
  | unknown
  /-- Characters `lo` up to (not including) `hi` of a character stream. -/
  | chars (lo hi : Nat)
  /-- Tokens `lo` up to (not including) `hi` of a token stream. -/
  | tokens (lo hi : Nat)
  /-- The `i`-th declaration of a program, counting from `0`. -/
  | decl (i : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- **A diagnostic**: what went wrong, and where. -/
structure Diag where
  msg : String
  loc : Loc := .unknown
  deriving Repr, Inhabited

/-- A lossy-but-annotated map from `Concrete` to `Abstract`: `abstract` (partial —
not every concrete is meaningful) together with, for each abstract value, a family
`Ann a` of concrete *re-presentations* and their realization back into `Concrete`.
`Ann a` is an account of the fiber of `abstract` over `a`, and it must be a *complete* one: that
is the `lossless` law. Where a structured family covers the fiber it may serve (`Gaps` for the
tokenizer); where none does, the fiber itself always works (`ofFibers`). -/
structure Abstraction (Concrete Abstract : Type) (Ann : Abstract → Type) where
  /-- The forward (lossy, partial) direction — the algorithm: tokenize, parse, elaborate. -/
  abstract : Concrete → Except Diag Abstract
  /-- Realize an annotated abstract value as a concrete one — the printer family. -/
  realize : ∀ {a : Abstract}, Ann a → Concrete
  /-- A canonical annotation: `realize default` is the pretty-printer. -/
  default : ∀ {a : Abstract}, Ann a
  /-- **Soundness**: anything realized re-abstracts to exactly its index. At `default`
  this is the canonical-print round trip. -/
  abstract_realize : ∀ (a : Abstract) (ann : Ann a), abstract (realize ann) = .ok a
  /-- **Completeness**: anything accepted was realized. The reverse direction — without it a
  morphism may take your concrete and hand back something unrelated to it, and be well-formed. -/
  lossless : ∀ (c : Concrete) (a : Abstract), abstract c = .ok a → ∃ ann : Ann a, realize ann = c
  /-- **Where an output location came from** in the input `c`: how a later stage's diagnostic is
  pointed back at this stage's input. Informal, like the diagnostics; by default the identity. -/
  locate : Concrete → Loc → Loc := fun _ l => l
  /-- **Best effort, for diagnostics**: everything wrong with `c`, and as much of an abstract value
  as could be made of it — with where that value's locations came from in `c`. A stage that can
  get past an error (skip a declaration that does not parse, or does not check) says so here, so a
  driver can report every error rather than the first. Informal: no law mentions it, and a driver
  takes its *output* from `abstract` alone. By default, `abstract`'s answer. -/
  recover : Concrete → List Diag × Option (Abstract × (Loc → Loc)) := fun c =>
    match abstract c with
    | .ok a => ([], some (a, locate c))
    | .error d => ([d], none)

namespace Abstraction

variable {A B C : Type} {F : B → Type} {G : C → Type} {F' : B → Type}

/-- The identity abstraction: nothing forgotten, `Unit` annotation. -/
def id (A : Type) : Abstraction A A (fun _ => Unit) where
  abstract := .ok
  realize {a} _ := a
  default := ()
  abstract_realize _ _ := rfl
  lossless _ _ h := ⟨(), (Except.ok.inj h).symm⟩

/-- Run `g` on what `f` made of `a`, pointing a rejection by `g` back into `a` with `f.locate`. -/
def compAbstract (f : Abstraction A B F) (g : Abstraction B C G) (a : A) : Except Diag C :=
  match f.abstract a with
  | .error d => .error d
  | .ok b =>
      match g.abstract b with
      | .error d => .error { d with loc := f.locate a d.loc }
      | .ok c => .ok c

theorem compAbstract_ok (f : Abstraction A B F) (g : Abstraction B C G) {a : A} {b : B}
    (h : f.abstract a = .ok b) : compAbstract f g a = (g.abstract b).mapError
      (fun d => { d with loc := f.locate a d.loc }) := by
  unfold compAbstract
  rw [h]
  dsimp only
  cases g.abstract b <;> rfl

/-- `compAbstract` sees only `f`'s algorithm and locations, not its printers. -/
theorem compAbstract_congr {F' : B → Type} {G' : C → Type} (f : Abstraction A B F)
    (f' : Abstraction A B F') (g : Abstraction B C G) (g' : Abstraction B C G') (a : A)
    (ha : f.abstract a = f'.abstract a) (hl : f.locate a = f'.locate a)
    (hg : g.abstract = g'.abstract) :
    compAbstract f g a = compAbstract f' g' a := by
  unfold compAbstract
  rw [ha, hl, hg]

/-- Composition (diagrammatic: first `f`, then `g`). The composite annotation is the
dependent sum: an outer `G`-annotation `β` picks the intermediate `g.realize β : B`,
and an inner `F`-annotation of *that* recovers the concrete. A diagnostic of `g` is pointed back
into the composite's input. -/
def comp (f : Abstraction A B F) (g : Abstraction B C G) :
    Abstraction A C (fun c => Σ β : G c, F (g.realize β)) where
  abstract := compAbstract f g
  realize γ := f.realize γ.2
  default := ⟨g.default, f.default⟩
  abstract_realize c γ := by
    rw [compAbstract_ok f g (f.abstract_realize (g.realize γ.1) γ.2), g.abstract_realize c γ.1]
    rfl
  lossless x z h := by
    unfold compAbstract at h
    split at h
    · cases h
    · rename_i y hfx
      split at h
      · cases h
      · rename_i z' hgy
        cases h
        obtain ⟨β, hβ⟩ := g.lossless y _ hgy
        subst hβ
        obtain ⟨α, hα⟩ := f.lossless x (g.realize β) hfx
        exact ⟨⟨β, α⟩, hα⟩
  locate a l :=
    match f.abstract a with
    | .ok b => f.locate a (g.locate b l)
    | .error _ => f.locate a l

/-- A composite's `locate` sees only its components' algorithms and locations. -/
theorem comp_locate_congr {F' : B → Type} {G' : C → Type} (f : Abstraction A B F)
    (f' : Abstraction A B F') (g : Abstraction B C G) (g' : Abstraction B C G') (a : A)
    (ha : f.abstract a = f'.abstract a) (hl : f.locate a = f'.locate a)
    (hg : g.locate = g'.locate) :
    (f.comp g).locate a = (f'.comp g').locate a := by
  simp only [comp]
  rw [ha, hl, hg]

/-- Re-choose the canonical annotation, keeping the morphism itself. Legitimate because
`default` carries **no law of its own**: `abstract_realize` is quantified over *every*
annotation, so any element of the family may serve as the canonical one and this leaves the
proof obligation untouched (it is literally `f`'s).

This is what lets a *composite* be pretty-printed. `comp` fixes `default := ⟨g.default,
f.default⟩`, and `f.default : ∀ {b}, F b` is uniform in its index — the earlier stage cannot
consult the later one, so a layout that depends on the abstract structure (one command per
line) is not expressible stage-locally. Re-defaulting the composite is: there both components
are in scope, and the choice is made where the structure is known instead of guessed. -/
def withDefault (f : Abstraction A B F) (d : ∀ {b : B}, F b) : Abstraction A B F :=
  { f with default := d }

/-- Re-defaulting changes only the canonical annotation. -/
@[simp] theorem withDefault_abstract (f : Abstraction A B F) (d : ∀ {b : B}, F b) :
    (f.withDefault d).abstract = f.abstract := rfl

@[simp] theorem withDefault_realize (f : Abstraction A B F) (d : ∀ {b : B}, F b) {b : B} :
    (f.withDefault d).realize (a := b) = f.realize := rfl

@[simp] theorem withDefault_default (f : Abstraction A B F) (d : ∀ {b : B}, F b) {b : B} :
    (f.withDefault d).default (a := b) = d := rfl

/-- Transport an abstraction along a fibrewise bijection of annotation families —
swap an unwieldy annotation type (e.g. the `Σ`-nest a composite produces) for a
hand-rolled presentation of the same data. -/
def reindex (f : Abstraction A B F) (e : ∀ b, Iso (F b) (F' b)) : Abstraction A B F' where
  abstract := f.abstract
  locate := f.locate
  realize {b} ann' := f.realize ((e b).symm ann')
  default {b} := e b f.default
  abstract_realize b ann' := f.abstract_realize b ((e b).symm ann')
  lossless c b h := by
    obtain ⟨ann, hann⟩ := f.lossless c b h
    -- `(e b).symm.toFun` is `(e b).invFun` by definition but not syntactically, so `show` states
    -- the goal in the form `left_inv` can rewrite.
    exact ⟨e b ann, by
      show f.realize ((e b).invFun ((e b).toFun ann)) = c
      rw [(e b).left_inv]; exact hann⟩

/-! ## Building one from a bare algorithm

With completeness a law, a morphism can no longer be assembled from an algorithm and a *chosen*
annotation family — the family must cover the fibers, and most chosen families do not. `ofFibers`
is the construction that always works: take the fiber itself.

The cost is that the annotation stops being *structured*. A family like "a spelling of this
program, command by command" says more than "some token list that parses to it", and the second is
what you get here. It is the right trade wherever the structure was serving only to pick `default`
— which is the case for the parse stage, since the layout is chosen on the composite anyway. -/

/-- **The tautological morphism**: over `b`, an annotation *is* a concrete that abstracts to `b`.
`canon` picks the canonical one, and both laws are then projections. -/
def ofFibers (abstract : A → Except Diag B) (canon : ∀ b : B, { c : A // abstract c = .ok b }) :
    Abstraction A B (fun b => { c : A // abstract c = .ok b }) where
  abstract := abstract
  realize ann := ann.val
  default {b} := canon b
  abstract_realize _ ann := ann.property
  lossless c _ h := ⟨⟨c, h⟩, rfl⟩

/-- **An idempotent function, as a stage**: onto what it leaves unchanged, which is its image. Total,
so it never rejects; the annotation over an output is everything that maps to it, and its
canonical member is the output itself — which is where idempotence is needed. -/
def ofIdempotent (f : A → A) (h : ∀ a, f (f a) = f a) :
    Abstraction A { b : A // f b = b } (fun b => { a : A // f a = b.val }) where
  abstract a := .ok ⟨f a, h a⟩
  realize ann := ann.val
  default {b} := ⟨b.val, b.property⟩
  abstract_realize b ann := by
    show Except.ok ⟨f ann.val, h ann.val⟩ = Except.ok b
    exact congrArg Except.ok (Subtype.ext ann.property)
  lossless c b hc := ⟨⟨c, by cases hc; rfl⟩, rfl⟩

@[simp] theorem ofFibers_abstract (abstract : A → Except Diag B)
    (canon : ∀ b : B, { c : A // abstract c = .ok b }) :
    (ofFibers abstract canon).abstract = abstract := rfl

/-! ## Bundling the annotation family

`Abstraction A B Ann` names `Ann` in its own type, so two stages of a pipeline have *different*
types and cannot be put in a list. `OneCell` packages the family with the morphism, which is what
makes `Abstraction/Chain.lean` possible.

It is also the 1-cell of the bicategory, and it lives here rather than in `Abstraction/Bicat.lean`
for the reason `Iso` lives here rather than being `Equiv`: `Bicat.lean` imports Mathlib, `Chain.lean`
is in the executables' import cone, and one Mathlib import there is about 1300 modules. Nothing
below needs `CategoryTheory`; only the 2-cells do. -/

/-- A 1-cell `A ⇝ B`: an abstraction with its annotation family packaged in. -/
structure OneCell (A B : Type) where
  /-- The annotation family, no longer an index. -/
  Ann : B → Type
  /-- The morphism itself. -/
  hom : Abstraction A B Ann

/-- The identity 1-cell `A ⇝ A` — the `Unit`-annotated `Abstraction.id`. Its `realize` is
definitionally the index, which is what keeps the bicategory's unitors transport-free. -/
def OneCell.id (A : Type) : OneCell A A where
  Ann := fun _ => Unit
  hom := Abstraction.id A

/-- Horizontal composition of 1-cells: `Abstraction.comp` with the `Σ`-nest it produces bundled
back in as the composite's family. -/
def OneCell.hcomp {A B C : Type} (f : OneCell A B) (g : OneCell B C) : OneCell A C where
  Ann := fun c => Σ β : g.Ann c, f.Ann (g.hom.realize β)
  hom := f.hom.comp g.hom

/-- The forward map of a composite, unbundled. -/
@[simp] theorem OneCell.hcomp_abstract (f : OneCell A B) (g : OneCell B C) (a : A) :
    (f.hcomp g).hom.abstract a = Abstraction.compAbstract f.hom g.hom a := rfl

end Abstraction

end LambdaLab
