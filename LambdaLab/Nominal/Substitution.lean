import LambdaLab.Nominal.Basic

/-!
# Substitution, nominally — the specification

The nominal statement of the substitution interface: the same operations and laws the repo runs
on, but with the support structure taken from `Nominal/Basic.lean` — `Perm`, `Supports`,
equivariance — instead of hand-rolled.

**What runs is `Nominal/Unification/Subst.lean`**, the Mathlib-free realization of this, carrying
support as a `List A`. The whole repo migrated onto it and the old `Substitution/` was deleted.
This file is what that one is to be checked against: the bridge proving its `pSubst` equivariant
and its carriers nominal is the piece still owed. The table below records what changed on the way.

Nothing here is instantiated. Like the file it specifies, it defines classes, the operations they
carry, and the laws that constrain them; the object languages supply the instances.

## Correspondence

| the old `Substitution/Basic.lean` | here | why it changed |
|---|---|---|
| `HasVars.isFree : 𝕋 → Nat → Prop` | `Supports` (from `Nominal/Basic.lean`) | support is already defined nominally |
| `HasVars.fresh : 𝕋 → Nat` | `HasSupp.supp : 𝕋 → Finset A` | a bound in an order is not available for atoms |
| `fresh_gt_free` | `supp_supports` | "everything free is below the bound" becomes "this finite set supports it" |
| `HasVars.Ground x` | `Ground x := Supports ∅ x` | equivariant, and one definition instead of a quantified negation |
| `Subst 𝕊 = HashMap Nat 𝕊` | the parameter `Θ` | the representation is no longer fixed by the interface |
| `HasSubst.pSubst` | `HasSubst.pSubst` + `pSubst_equivariant` | the missing law; everything in §4 follows from it |
| `Subst.comp`, `LawfulComp` | `LawfulComp` (data + law) | `comp` cannot be defined without knowing `Θ` |
| `Subst.restrictBelow`, `LawfulRestrict` | `LawfulRestrict` over a `Finset` | "below `n`" is an order; "outside `s`" is not |
| `MoreGeneral`, `MoreGeneralBelow n` | `MoreGeneral`, `MoreGeneralOn s` | same |

## Three decisions worth arguing with

**The substitution type is a parameter, not a definition.** The old `Substitution/Basic.lean` fixed
`Subst 𝕊 = Std.HashMap Nat 𝕊` in the interface, so every law is a law about hashmaps. Here `Θ` is
any nominal type, and `pSubst : 𝕋 → Θ → 𝕋`. That is what lets one interface carry both the
executable representation (a hashmap, which is what should stay in the cone the executables build)
and the mathematical one (§7), related by a homomorphism rather than by being the same type. It
also sidesteps the fact that `Std.HashMap` is not extensional, which would otherwise make even
`1 • σ = σ` false on the nose.

**Support is chosen, not least.** `HasSupp.supp` is a *some* finite supporting set, exactly as
`HasVars.fresh` was only ever required to be an upper bound and was free to over-approximate.
Least support exists, but deriving it needs machinery `Nominal/Basic.lean` does not have yet, and
nothing below depends on minimality. The price is recorded in §4: a *bound on the chosen* `supp`
of a result is not derivable and stays a per-instance obligation, which is what `Signature`
already does for `fresh`.

**Equivariance is the one new law, and it pays for itself.** `HasSubst` in the old file states no
laws at all. Adding just `π • pSubst x σ = pSubst (π • x) (π • σ)` turns the support bounds in §4
from assumptions into theorems — and those bounds are what the elaborator's pruning arguments and
the unifier's termination measure are built on.

## The one fragile choice: `A` is an `outParam`

`pSubst : 𝕋 → Θ → 𝕋` does not mention `A`, so the atom type cannot be inferred from a use site
and something has to determine it. It is an `outParam`, so instance search keys on the pair
`(𝕋, Θ)`.

That is the same mechanism that bit once already (`735d1e6`, patched with `priority := low`) when
two `HasSubst` instances shared a carrier, so it deserves the warning: **it is safe here only
because `Θ` is per-atom-type.** A term type that is substituted into by both its own variables and
by metavariables gets `HasSubst N (Term N) Θ₁` and `HasSubst Nat (Term N) Θ₂` — distinct in `Θ`,
so search can separate them, which it could not have done when the old interface fixed
`Subst 𝕊` and left only `𝕋` to key on. If a carrier ever needs two atom types at the *same* `Θ`,
this must become an explicit parameter and every use site gains an `(A := ·)`.

## What this file does not do

It imports `Nominal/Basic.lean`, so it takes Mathlib, so **it must not enter the `stlc`/`arith`
import cone** — measured at 129 MB the last time Mathlib was in there. That is exactly why
`Nominal/Unification/Subst.lean` exists as a separate, Mathlib-free module depending on
`Nominal/Atom.lean` alone: the executables carry that one, and this one states what it means.
Keeping the two apart is deliberate, not an accident of layering — and it is why the equivariance
law below appears here and not there.
-/

namespace LambdaLab.Nominal

variable {A 𝕋 Θ : Type} [Atom A]

/-! ## 1. Atoms do not run out, at `Finset` level

`Atom.freshFor` is stated for lists because `Nominal/Atom.lean` may not mention `Finset`. This is
the same fact where the rest of the development wants it, and it is the brick `Nominal/Basic.lean`
records as missing. -/

theorem exists_fresh (s : Finset A) : ∃ a : A, a ∉ s :=
  ⟨freshFor s.toList, fun h => freshFor_not_in s.toList (Finset.mem_toList.mpr h)⟩

/-! ## 2. Chosen support

`HasSupp` is to `NominalType` what `Atom.freshFor` is to "atoms are infinite": the existential the
class already guarantees, made into data so that it computes. -/

/-- A chosen finite supporting set for every element. Replaces `HasVars.fresh`. -/
class HasSupp (A X : Type) [Atom A] [NominalType A X] where
  /-- Some finite set of atoms supporting `x`. Not required to be least. -/
  supp : X → Finset A
  supp_supports : ∀ x : X, Supports (supp x) x

export HasSupp (supp)

/-- **Ground**: no atom matters, i.e. the empty set supports it. Replaces `HasVars.Ground`, and
unlike it this is manifestly equivariant. -/
def Ground (A : Type) [Atom A] [NominalType A 𝕋] (x : 𝕋) : Prop := Supports (∅ : Finset A) x

theorem ground_iff [NominalType A 𝕋] {x : 𝕋} :
    Ground A x ↔ ∀ π : Perm A, π • x = x :=
  ⟨fun h π => h π (fun a ha => absurd ha (Finset.notMem_empty a)), fun h π _ => h π⟩

/-- An atom is supported by itself and nothing smaller is needed. -/
instance : HasSupp A A where
  supp a := {a}
  supp_supports a := fun _ h => h a (Finset.mem_singleton_self a)

/-- Sanity check on the definitions, and the first use of `exists_fresh`: an atom is never ground,
because a swap with a fresh atom moves it. -/
theorem atom_not_ground (a : A) : ¬ Ground A a := by
  intro h
  obtain ⟨b, hb⟩ := exists_fresh ({a} : Finset A)
  have hne : b ≠ a := fun hEq => hb (hEq ▸ Finset.mem_singleton_self a)
  have hswap := ground_iff.mp h (Perm.swap a b)
  rw [Perm.smul_atom, Perm.swap_apply_left] at hswap
  exact hne hswap

/-! ## 3. Substitution

`Θ` is the substitution representation: any nominal type at all. The interface says what it does,
not what it is. -/

/-- Applying a substitution `σ : Θ` to an object `x : 𝕋`. Replaces `HasSubst`, with the law the
old class did without. -/
class HasSubst (A : outParam Type) (𝕋 Θ : Type)
    [Atom A] [NominalType A 𝕋] [NominalType A Θ] where
  pSubst : 𝕋 → Θ → 𝕋
  /-- Renaming the atoms of the inputs renames the atoms of the result. -/
  pSubst_equivariant :
    ∀ (π : Perm A) (x : 𝕋) (σ : Θ), π • pSubst x σ = pSubst (π • x) (π • σ)

export HasSubst (pSubst pSubst_equivariant)

/-! ## 4. What equivariance buys

These are the statements `HasVars.fresh_gt_free` was assumed for. Here they are proved. -/

variable [NominalType A 𝕋] [NominalType A Θ]

/-- **Substitution introduces no atoms.** Whatever supports the inputs supports the result. -/
theorem supports_pSubst [HasSubst A 𝕋 Θ] {s t : Finset A} {x : 𝕋} {σ : Θ}
    (hx : Supports s x) (hσ : Supports t σ) : Supports (s ∪ t) (pSubst x σ) := by
  intro π hπ
  rw [pSubst_equivariant, hx π (fun a ha => hπ a (Finset.mem_union_left _ ha)),
    hσ π (fun a ha => hπ a (Finset.mem_union_right _ ha))]

/-- Substituting a ground substitution into a ground object gives a ground result. -/
theorem ground_pSubst [HasSubst A 𝕋 Θ] {x : 𝕋} {σ : Θ}
    (hx : Ground A x) (hσ : Ground A σ) : Ground A (pSubst x σ) := by
  have h := supports_pSubst hx hσ
  rwa [Finset.union_empty] at h

/-! ## 5. The laws that stay laws

Equivariance says how substitution interacts with *renaming*. It says nothing about what a
substitution does or leaves alone, so these three do not follow from it and remain assumptions,
one per instance — exactly as in `Nominal/Unification/Subst.lean`. -/

/-- **Substitution does nothing to a ground object.** A mixin over `[HasSubst]`, not an `extends`,
for the reason the old file gives: a class extending `HasSubst` carries its own copy of `pSubst`,
and a caller wanting two such classes gets two unrelated ones. -/
class GroundStable (A : outParam Type) (𝕋 Θ : Type)
    [Atom A] [NominalType A 𝕋] [NominalType A Θ] [HasSubst A 𝕋 Θ] : Prop where
  pSubst_ground : ∀ {x : 𝕋} (σ : Θ), Ground A x → pSubst x σ = x

/-- **Substituting twice is substituting once, through the composite.** `comp σ τ` applies `τ`
first, then `σ`. The composite cannot be *defined* here — that needs the representation — so this
class carries it as data together with its law. -/
class LawfulComp (A : outParam Type) (𝕋 Θ : Type)
    [Atom A] [NominalType A 𝕋] [NominalType A Θ] [HasSubst A 𝕋 Θ] where
  comp : Θ → Θ → Θ
  comp_equivariant : ∀ (π : Perm A) (σ τ : Θ), π • comp σ τ = comp (π • σ) (π • τ)
  pSubst_comp : ∀ (x : 𝕋) (σ τ : Θ), pSubst x (comp σ τ) = pSubst (pSubst x τ) σ

/-- **Bindings on atoms an object does not care about are invisible to it.** The order-free form
of `LawfulRestrict`: `restrict s σ` keeps only what `σ` says about atoms in `s`, and an object
supported by `s` cannot tell the difference. -/
class LawfulRestrict (A : outParam Type) (𝕋 Θ : Type)
    [Atom A] [NominalType A 𝕋] [NominalType A Θ] [HasSubst A 𝕋 Θ] where
  restrict : Finset A → Θ → Θ
  restrict_equivariant : ∀ (π : Perm A) (s : Finset A) (σ : Θ),
    π • restrict s σ = restrict (s.image (fun a => π a)) (π • σ)
  pSubst_restrict : ∀ (s : Finset A) (x : 𝕋) (σ : Θ),
    Supports s x → pSubst x (restrict s σ) = pSubst x σ

/-! ## 6. Generality

`MoreGeneral σ σ'` says `σ` is at least as general as `σ'`: some `τ` factors `σ'` through `σ`. -/

/-- Generality on every object. -/
def MoreGeneral (𝕋 : Type) [NominalType A 𝕋] [HasSubst A 𝕋 Θ] (σ σ' : Θ) : Prop :=
  ∃ τ : Θ, ∀ x : 𝕋, pSubst x σ' = pSubst (pSubst x σ) τ

/-- Generality restricted to the objects supported by `s` — the order-free `MoreGeneralBelow`.

The restriction is not a convenience. An elaborator draws atoms its source never mentioned and may
legitimately mention them in its answer; a competing `σ'` says nothing about those, so no `τ` can
factor it at those atoms, and the unrestricted form is false. `s` is the source's support. -/
def MoreGeneralOn (𝕋 : Type) [NominalType A 𝕋] [HasSubst A 𝕋 Θ]
    (s : Finset A) (σ σ' : Θ) : Prop :=
  ∃ τ : Θ, ∀ x : 𝕋, Supports s x → pSubst x σ' = pSubst (pSubst x σ) τ

/-- Generality everywhere is generality on any support. -/
theorem MoreGeneral.on [HasSubst A 𝕋 Θ] {σ σ' : Θ}
    (h : MoreGeneral 𝕋 σ σ') (s : Finset A) : MoreGeneralOn 𝕋 s σ σ' :=
  ⟨h.choose, fun x _ => h.choose_spec x⟩

/-! ## 7. Deliberately not here

**A canonical substitution type.** The obvious one is a finitely supported map — `A → 𝕊` differing
from `var` at finitely many atoms — with `π • σ := fun a => π • σ (π⁻¹ • a)`. It is the natural
next file: it needs `HasVar`, the `MulAction` laws, and a `NominalType` instance whose support is
the domain together with the supports of the values. It is not here because `Θ` being a parameter
is the point of the interface, and a representation shipped alongside tends to become *the*
representation by gravity. The executable one is a hashmap and lives on the other side of the
Mathlib boundary.

**The pointwise lifts.** `Nominal/Unification/Subst.lean` lifts `HasSubst` over pairs, lists and
hashmaps; they carried across unchanged in shape, with support a concatenation instead of a `max`.
Their equivariance is componentwise and belongs to the bridge, not here.

**Fresh-atom generation.** `Atom.freshFor` produces one atom against an avoid-list, at the cost of
a pass over it. An elaborator drawing metavariables wants a counter: O(1), monotone, no list. That
belongs with the elaborator and stays at `Nat`; nothing in this interface needs to generate an
atom, which is the point — `freshFor` is not equivariant, and a nominal interface that mentioned
it would not stay one. -/

end LambdaLab.Nominal
