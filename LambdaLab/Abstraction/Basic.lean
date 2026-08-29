/-!
# Abstraction

The indexed abstraction structure, shaped by the pipeline it has to host:
tokenize → parse → elaborate.

Two decisions, both forced by that pipeline:

* **`abstract` is partial** (`Option`). A parser rejects `["(", "("]`, a type checker
  rejects ill-typed terms — the total version cannot host either stage. (`Except ε`
  for diagnostics is a compatible upgrade; the theory is unchanged. Undecided.)

* **Soundness is the only structure law.** Completeness — every accepted concrete is
  `realize` of some annotation — is demoted to the per-morphism predicate `Lossless`.
  It cannot be a structure law: for a Hindley–Milner elaborator the fiber over a typed
  term is every combination of written-vs-omitted annotations *jointly constrained by
  unification* — one written type propagates globally, so no node-local annotation
  family covers the fiber; only the tautological `{c // abstract c = some a}` does,
  vacuously. Syntactic stages (tokenizer, parser) prove `Lossless`; elaboration stages
  simply don't claim it. `Lossless` is closed under `comp` and `reindex`, so a
  pipeline tracks exactly how far source reconstruction extends.

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

namespace LambdaLab

/-- A bijection, with both round-trips as fields.

This is Mathlib's `Equiv`, and this file used `Equiv` until the cost was measured: everything
the executables import is linked into them, and one Mathlib import — any Mathlib import — puts
about 1300 modules into that closure. Four fields are not worth 1300 modules; removing this one
and `Nat.digits` in `Parser/Numeral` took `stlc` from 129 MB to 2.8 MB. The seventeen modules
outside the executables' import cone still use Mathlib freely; this is not a policy against
Mathlib, only against Mathlib *below* `Stlc` and `Arith`. -/
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

/-- A lossy-but-annotated map from `Concrete` to `Abstract`: `abstract` (partial —
not every concrete is meaningful) together with, for each abstract value, a family
`Ann a` of concrete *re-presentations* and their realization back into `Concrete`.
`Ann a` is a structured account of (part of) the fiber of `abstract` over `a`; when
it covers the fiber the abstraction is `Lossless`, but that is a property of
individual morphisms, not a law. -/
structure Abstraction (Concrete Abstract : Type) (Ann : Abstract → Type) where
  /-- The forward (lossy, partial) direction — the algorithm: tokenize, parse, elaborate. -/
  abstract : Concrete → Option Abstract
  /-- Realize an annotated abstract value as a concrete one — the printer family. -/
  realize : ∀ {a : Abstract}, Ann a → Concrete
  /-- A canonical annotation: `realize default` is the pretty-printer. -/
  default : ∀ {a : Abstract}, Ann a
  /-- Soundness: anything realized re-abstracts to exactly its index. At `default`
  this is the canonical-print round trip. -/
  abstract_realize : ∀ (a : Abstract) (ann : Ann a), abstract (realize ann) = some a
  /-- Completeness: every accepted concrete is `realize` of some annotation — `Ann`
  covers the fibers of `abstract`, so the source can always be reconstructed. -/
  complete : ∀ (c : Concrete) (a : Abstract), abstract c = some a → ∃ ann : Ann a, realize ann = c

namespace Abstraction

variable {A B C : Type} {F : B → Type} {G : C → Type} {F' : B → Type}

/-- The identity abstraction: nothing forgotten, `Unit` annotation. -/
def id (A : Type) : Abstraction A A (fun _ => Unit) where
  abstract := some
  realize {a} _ := a
  default := ()
  abstract_realize _ _ := rfl
  complete _ _ h := ⟨(), (Option.some.inj h).symm⟩

/-- Composition (diagrammatic: first `f`, then `g`). The composite annotation is the
dependent sum: an outer `G`-annotation `β` picks the intermediate `g.realize β : B`,
and an inner `F`-annotation of *that* recovers the concrete. -/
def comp (f : Abstraction A B F) (g : Abstraction B C G) :
    Abstraction A C (fun c => Σ β : G c, F (g.realize β)) where
  abstract a := (f.abstract a).bind g.abstract
  realize γ := f.realize γ.2
  default := ⟨g.default, f.default⟩
  abstract_realize c γ := by
    show (f.abstract (f.realize γ.2)).bind g.abstract = some c
    rw [f.abstract_realize (g.realize γ.1) γ.2]
    exact g.abstract_realize c γ.1
  complete a c h := by
    have h' : (f.abstract a).bind g.abstract = some c := h
    cases hfa : f.abstract a with
    | none => rw [hfa] at h'; simp at h'
    | some b =>
        have hgb : g.abstract b = some c := by rw [hfa] at h'; exact h'
        obtain ⟨β, hβ⟩ := g.complete b c hgb
        subst hβ
        obtain ⟨α, hα⟩ := f.complete a (g.realize β) hfa
        exact ⟨⟨β, α⟩, hα⟩

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
  realize {b} ann' := f.realize ((e b).symm ann')
  default {b} := e b f.default
  abstract_realize b ann' := f.abstract_realize b ((e b).symm ann')
  complete c b h := by
    obtain ⟨ann, hann⟩ := f.complete c b h
    exact ⟨e b ann, by
      show f.realize ((e b).invFun ((e b).toFun ann)) = c
      rw [(e b).left_inv]; exact hann⟩

/-! ## Losslessness — completeness as a per-morphism property -/

/-- `f` forgets nothing: every concrete that `f` accepts is `realize` of some
annotation, so `Ann` covers the fibers and the source can be reconstructed exactly.
Tokenizers and parsers have this; a Hindley–Milner elaborator does not (its fibers
are globally constrained by unification). -/
def Lossless (f : Abstraction A B F) : Prop :=
  ∀ (c : A) (b : B), f.abstract c = some b → ∃ ann : F b, f.realize ann = c

theorem id_lossless (A : Type) : (id A).Lossless :=
  fun _ _ h => ⟨(), (Option.some.inj h).symm⟩

/-- Losslessness is about `realize`, not `default`, so it survives re-defaulting: the two
morphisms have the same `abstract` and the same `realize`, and `Lossless` mentions only those. -/
theorem withDefault_lossless {f : Abstraction A B F} (d : ∀ {b : B}, F b) (h : f.Lossless) :
    (f.withDefault d).Lossless := h

theorem Lossless.comp {f : Abstraction A B F} {g : Abstraction B C G}
    (hf : f.Lossless) (hg : g.Lossless) : (f.comp g).Lossless := by
  intro x z h
  have h' : (f.abstract x).bind g.abstract = some z := h
  cases hfx : f.abstract x with
  | none => rw [hfx] at h'; simp at h'
  | some y =>
      have hgy : g.abstract y = some z := by rw [hfx] at h'; exact h'
      obtain ⟨β, hβ⟩ := hg y z hgy
      subst hβ
      obtain ⟨α, hα⟩ := hf x (g.realize β) hfx
      exact ⟨⟨β, α⟩, hα⟩

theorem Lossless.reindex {f : Abstraction A B F} (e : ∀ b, Iso (F b) (F' b))
    (hf : f.Lossless) : (f.reindex e).Lossless := by
  intro c b h
  obtain ⟨ann, hann⟩ := hf c b h
  -- `(e b).symm.toFun` is `(e b).invFun` by definition but not syntactically, so `show` states
  -- the goal in the form `left_inv` can rewrite.
  exact ⟨e b ann, by
    show f.realize ((e b).invFun ((e b).toFun ann)) = c
    rw [(e b).left_inv]; exact hann⟩

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
    (f.hcomp g).hom.abstract a = (f.hom.abstract a).bind g.hom.abstract := rfl

end Abstraction

end LambdaLab
