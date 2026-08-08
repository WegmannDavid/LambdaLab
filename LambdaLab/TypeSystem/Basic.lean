import LambdaLab.TypeSystem.Context
import LambdaLab.Substitution.Basic

/-!
# `TypeSystem` — a named object language bundled with its metatheory

Where `NameAlphabet` fixes what a *name* is and `Context` what a *context* is, this fixes what a
*type system over them* is: terms, types, a typing judgement, a reduction relation, and the
theorem tying the two together.

The point of the bundle is that `Preservation` is a **field**. A `TypeSystem` cannot be built
without discharging it, so the structure is not a signature that implementations may or may not
satisfy — it is the theorem-carrying record, and anything downstream may use preservation without
re-proving or re-assuming it.

## The name parameter is a field, not a parameter

`N` is bundled, with its `NameAlphabet` instance alongside it:

```lean
structure TypeSystem where
  N : Type
  [nameAlphabet : NameAlphabet N]
  ...
```

rather than `structure TypeSystem (N : Type) [NameAlphabet N]`. This matches `Tm` and `Ty`, which
are already fields, and it is what lets a `TypeSystem` be passed around as one value — a family
indexed by `N` would force every consumer to carry `N` and its instance too. The cost is the
`attribute [instance]` line below, without which `Context S.N S.Ty` cannot elaborate.

## Scope

Deliberately minimal. Normalization, confluence and the elaboration side are *not* fields: they
hold for STLC but not for every system worth describing this way, and a field no instance can
discharge is a field that keeps instances from existing. Preservation is the one property general
enough to demand of everything here.
-/

namespace LambdaLab.TypeSystem

class Step (Tm : Type) where
  /-- Single-step reduction. -/
  Step : Tm → Tm → Prop

/-- A named object language together with the metatheory that makes it well-behaved: typing,
reduction, and a proof that reduction preserves types. -/
class HasType (N Tm Ty : Type) [nameAlphabet : NameAlphabet N] where
  /-- The typing judgement, over contexts keyed by `N`. -/
  HasType : Context N Ty → Tm → Ty → Prop

class TypeSystem (N Tm Ty : Type) [nameAlphabet : NameAlphabet N] extends HasType N Tm Ty, Step Tm where

class LawfulTypeSystem (N Tm Ty : Type) [nameAlphabet : NameAlphabet N] extends TypeSystem N Tm Ty where
  /-- A type system is a named object language together with the metatheory that makes it
  well-behaved: typing, reduction, and a proof that reduction preserves types. -/
  Preservation : ∀ {Γ t τ t'}, HasType Γ t τ → Step t t' → HasType Γ t' τ

/-- A type system whose types carry metavariables, so substitution acts on both levels:
`pSubst : Tm → Subst Ty → Tm` for the type annotations inside a term, and
`pSubst : Ty → Subst Ty → Ty` for types themselves.

**Fields, not parents.** `extends … HasSubst Tm Ty, HasSubst Ty Ty` does not work: Lean
deduplicates parent structures by class *head*, so the second is dropped with only a
`Duplicate parent structure` warning, leaving the class with no type-level substitution at all.
Naming the parents (`extends tmSubst : HasSubst Tm Ty, …`) makes no difference. Fields plus the
`attribute` line below are the way to carry two instances of one class.

**On filling them in.** Both instances usually exist already — `HasSubst (Term N) Ty`, and
`HasSubst Ty Ty` via `Signature` — so fill the fields with `inferInstance` rather than fresh
definitions. Then the bundled copies are *definitionally* the canonical ones and lemmas proved
about either apply to both. Two independent `pSubst`s for the same type would typecheck and then
fail to talk to each other somewhere far away. -/
class MVars (N Tm Ty : Type) [nameAlphabet : NameAlphabet N] extends TypeSystem N Tm Ty where
  /-- Substitution of types into a term's annotations. Fill with `inferInstance` where possible. -/
  tmSubst : HasSubst Tm Ty
  /-- Substitution of types into types. Fill with `inferInstance` where possible. -/
  tySubst : HasSubst Ty Ty

/-! `reducible` is required of instance-valued projections; `low` is not cosmetic. At default
priority `MVars.tySubst` *displaces* the canonical `Signature.instHasSubst` as the instance found
for `HasSubst Ty Ty` — it wins by being declared later, and it resolves the undetermined `N` and
`Tm` by picking whatever single `MVars` instance is in scope. `low` puts the real instance back in
front and leaves the projections as the fallback they should be. -/
attribute [reducible, instance low] MVars.tmSubst MVars.tySubst

/-- A decision about `P` over substitutions, carrying evidence either way: the **most general** σ
satisfying it, or a proof that none does. `MoreGeneral σ σ'` says every competing solution factors
through σ — there is a τ with `pSubst t σ' = pSubst (pSubst t σ) τ` for all `t`.

Both constructors name *what is the case*, never how it was established. That is deliberate:
`Subst 𝕊` is infinite, so `impossible` can never come from enumeration — it comes from unification
failing structurally, on an occurs check or a rigid-rigid clash. Any name suggesting an exhaustive
search would be wrong in exactly the case this type exists for. `impossible` is likewise a *proof
of absence*, not a failure to find one; that distinction is the whole content of this type over
`Option`.

Strictly stronger than `Decidable (∃ σ, P σ)`, which is why it is worth writing down: the map
`MGUProp P → Decidable (∃ σ, P σ)` is definable, the converse is not, because `∃` lives in `Prop`
and `isTrue` therefore carries no extractable σ. `𝕊` is implicit, being determined by `P`.

This is `Stlc/Named/Typing/Target.lean`'s `elaborationResult` with the type system abstracted out;
that one is the same pair of conjuncts as a subtype, over the STLC `Ty`. Its most-generality
conjunct is one of the open sorries, so expect `mgu` to be the expensive constructor. -/
inductive MGUProp {𝕊 : Type} [HasSubst 𝕊 𝕊] (P : Subst 𝕊 → Prop) where
  /-- A σ satisfying `P` that every other solution factors through. -/
  | mgu (σ : Subst 𝕊) (hσ : P σ) (hmgu : ∀ σ', P σ' → MoreGeneral σ σ') : MGUProp P
  /-- No σ satisfies `P`. -/
  | impossible (h : ∀ σ, ¬ P σ) : MGUProp P

class DecideableElaborate (N Tm Ty : Type) [nameAlphabet : NameAlphabet N] extends MVars N Tm Ty where
  /-- Decideable typing judgement. -/
  elaborate : (Γ : Context N Ty) → (t : Tm) → (τ : Ty) →
      MGUProp (fun σ : Subst Ty =>
        HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ))

end LambdaLab.TypeSystem
