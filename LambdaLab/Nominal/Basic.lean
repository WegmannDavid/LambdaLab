import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Action.Defs
import LambdaLab.Nominal.Atom

/-!
# Nominal types

A *nominal type* over an atom supply `A` is a type `X` carrying an action of the finitely
supported permutations of `A`, in which every element is *finitely supported* — moved by only
finitely many atoms. That is the whole definition, and `NominalType` below is it.

The class is `NominalType`, not `Nominal`: this namespace is already `LambdaLab.Nominal`, and
`LambdaLab.Nominal.Nominal` trips Mathlib's `dupNamespace` linter, which would put a warning in
a build that is otherwise warning-clean.

## Why permutations are bundled

`Perm A` is a bijection `A ≃ A` bundled with a proof that it moves only finitely many atoms.
The finiteness is in the type rather than beside it because *every* `Perm` in the development
must have it — there is no useful unsupported permutation — and because it is what makes the
group operations total: composing two finitely supported bijections is finitely supported, so
`Group (Perm A)` needs no side conditions and `MulAction` applies unchanged.

The alternative considered was a free monoid of transpositions, `List (A × A)`, which is cheaper
to define and computes. It was rejected: it is a monoid, not a group, so every lemma that wants
`π • x = y ↔ x = π⁻¹ • y` gets hand-rolled against `List.reverse`. `Perm.swap` gives back the
computational entry point without giving up the group.

## Why this file may import Mathlib and `Atom.lean` may not

`Finset`, `Set.Finite`, `Group` and `MulAction` all come from Mathlib, and taking them means
every downstream fact about composing and inverting permutations is already proved. `Atom.lean`
cannot make that trade — the `stlc` and `arith` executables' import cone runs through it, and
Mathlib in that cone cost 129 MB the last time it was measured. Nothing in `Nominal/` below the
atoms is in that cone, so the constraint stops here.

## What is deliberately absent

*Sorts.* Atoms are unsorted, so a `Perm` is any finitely supported bijection. STLC binds term
variables and nothing else, so one sort covers the repo today; sorts can arrive later as fields
on `Atom` without changing a single `[Atom N]` signature.

*`support`.* The *least* supporting set exists — two finite supporting sets intersect to a
supporting set, which is provable precisely because atoms do not run out — but that argument
wants a `Finset`-level freshness lemma that is not written yet. `NominalType` asserts only that
*some* finite support exists, which is what the definition requires.
-/

namespace LambdaLab.Nominal

variable {A X : Type} [Atom A]

/-! ## Finitely supported permutations -/

/-- A permutation of the atoms `A` that moves only finitely many of them. -/
structure Perm (A : Type) [Atom A] where
  /-- The underlying bijection. -/
  toEquiv : A ≃ A
  /-- Only finitely many atoms are moved. -/
  moved_finite : {a : A | toEquiv a ≠ a}.Finite

instance : CoeFun (Perm A) (fun _ => A → A) := ⟨fun π => π.toEquiv⟩

/-- The atoms a permutation moves. -/
def Perm.moved (π : Perm A) : Set A := {a : A | π a ≠ a}

@[ext] theorem Perm.ext {π σ : Perm A} (h : ∀ a, π a = σ a) : π = σ := by
  cases π; cases σ; simp only [Perm.mk.injEq]; exact Equiv.ext h

@[simp] theorem Perm.coe_mk (e : A ≃ A) (h) : (Perm.mk e h : A → A) = e := rfl

/-! ### The group structure

Each operation carries the finiteness proof along: the identity moves nothing, a composite moves
at most what its factors move, and an inverse moves *exactly* what it inverts. -/

instance : One (Perm A) where
  one := ⟨Equiv.refl A, by
    have : {a : A | (Equiv.refl A) a ≠ a} = ∅ := by ext a; simp
    rw [this]; exact Set.finite_empty⟩

instance : Mul (Perm A) where
  mul π σ := ⟨σ.toEquiv.trans π.toEquiv, by
    refine (π.moved_finite.union σ.moved_finite).subset ?_
    intro a ha
    simp only [Set.mem_setOf_eq, Equiv.trans_apply] at ha
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra h
    obtain ⟨h₁, h₂⟩ := not_or.mp h
    exact ha (by rw [not_not.mp h₂, not_not.mp h₁])⟩

instance : Inv (Perm A) where
  inv π := ⟨π.toEquiv.symm, by
    have : {a : A | π.toEquiv.symm a ≠ a} = {a : A | π.toEquiv a ≠ a} := by
      ext a
      simp only [Set.mem_setOf_eq, ne_eq, not_iff_not, Equiv.symm_apply_eq]
      exact eq_comm
    rw [this]; exact π.moved_finite⟩

@[simp] theorem Perm.one_apply (a : A) : (1 : Perm A) a = a := rfl

@[simp] theorem Perm.mul_apply (π σ : Perm A) (a : A) : (π * σ) a = π (σ a) := rfl

@[simp] theorem Perm.inv_apply (π : Perm A) (a : A) : π⁻¹ a = π.toEquiv.symm a := rfl

instance : Group (Perm A) where
  mul_assoc _ _ _ := by ext a; simp
  one_mul _ := by ext a; simp
  mul_one _ := by ext a; simp
  inv_mul_cancel π := by ext a; simp

/-! ### Transpositions

`swap a b` is the computational entry point: every finitely supported permutation is a product
of transpositions, and nominal proofs that want to *exhibit* a permutation reach for this. -/

/-- The transposition exchanging `a` and `b`. -/
def Perm.swap (a b : A) : Perm A :=
  ⟨Equiv.swap a b, Set.Finite.subset ((Set.finite_singleton b).insert a) (by
    intro c hc
    simp only [Set.mem_setOf_eq] at hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra h
    obtain ⟨h₁, h₂⟩ := not_or.mp h
    exact hc (Equiv.swap_apply_of_ne_of_ne h₁ h₂))⟩

@[simp] theorem Perm.swap_apply_left (a b : A) : Perm.swap a b a = b := Equiv.swap_apply_left a b

@[simp] theorem Perm.swap_apply_right (a b : A) : Perm.swap a b b = a := Equiv.swap_apply_right a b

theorem Perm.swap_apply_of_ne_of_ne {a b c : A} (h₁ : c ≠ a) (h₂ : c ≠ b) :
    Perm.swap a b c = c := Equiv.swap_apply_of_ne_of_ne h₁ h₂

@[simp] theorem Perm.swap_self (a : A) : Perm.swap a a = 1 := by
  ext c; by_cases h : c = a <;> simp [h, Perm.swap]

/-! ## Nominal types -/

/-- A *nominal type* over the atoms `A`: a `Perm A`-set in which every element is moved by only
finitely many atoms.

The support condition is stated as "some finite set of atoms suffices", where *suffices* means
that any permutation fixing all of them fixes the element. It is an existential rather than a
chosen `support` function on purpose — a least support does exist, but deriving it needs a
freshness lemma at `Finset` level, and nothing about being nominal depends on having picked it. -/
class NominalType (A X : Type) [Atom A] extends MulAction (Perm A) X where
  /-- Every element is supported by some finite set of atoms. -/
  finitely_supported :
    ∀ x : X, ∃ s : Finset A, ∀ π : Perm A, (∀ a ∈ s, π a = a) → π • x = x

/-- `s` *supports* `x` when every permutation fixing all of `s` fixes `x`. -/
def Supports [NominalType A X] (s : Finset A) (x : X) : Prop :=
  ∀ π : Perm A, (∀ a ∈ s, π a = a) → π • x = x

theorem exists_supports [NominalType A X] (x : X) : ∃ s : Finset A, Supports (A := A) s x :=
  NominalType.finitely_supported x

/-! ## The atoms are nominal

The base case, and the one that fixes the meaning of the definition: an atom is supported by
itself. That `{a}` is also its *least* support is true but not proved here — it needs an atom
outside a given finite set, which is the freshness lemma this file does not yet have. -/

instance : MulAction (Perm A) A where
  smul π a := π a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem Perm.smul_atom (π : Perm A) (a : A) : π • a = π a := rfl

instance : NominalType A A where
  finitely_supported a := ⟨{a}, fun _ h => h a (Finset.mem_singleton_self a)⟩

end LambdaLab.Nominal
