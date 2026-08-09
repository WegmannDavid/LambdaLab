import LambdaLab.TypeSystem.Context
import LambdaLab.Substitution.Unification.MGU

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

/-- `MVars` supplies two substitution operations and demands nothing of them. This adds the one
law that makes them mean something: **typing is stable under substitution**.

Without it an `MVars` instance may pair a perfectly good `HasType` with a `pSubst` that has no
relation to it, and `DecideableElaborate` below would still typecheck — its `MGUProp` predicate is
built entirely out of `pSubst`, so a nonsense `pSubst` yields a nonsense specification that an
implementation could satisfy vacuously. Stability is what ties the algorithmic side back to the
judgement.

Same reasoning as `Preservation` being a field of `LawfulTypeSystem`: put the law where an
instance cannot be built without discharging it, and keep the bare class instanceable so
`pSubst` is usable before anyone proves anything about it. -/
class LawfulMVars (N Tm Ty : Type) [nameAlphabet : NameAlphabet N] extends MVars N Tm Ty where
  /-- Applying a substitution to context, term and type at once preserves the typing derivation.
  For a system whose types carry metavariables this is the workhorse: it is what lets a solved
  constraint set be *applied* and still describe a typing. -/
  Stability : ∀ {Γ : Context N Ty} {t : Tm} {τ : Ty} (σ : Subst Ty),
    HasType Γ t τ → HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ)

class DecideableElaborate (N Tm Ty : Type) [nameAlphabet : NameAlphabet N] extends LawfulMVars N Tm Ty where
  /-- Decideable typing judgement. -/
  elaborate : (Γ : Context N Ty) → (t : Tm) → (τ : Ty) →
      MGUProp (fun σ : Subst Ty =>
        HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ))

end LambdaLab.TypeSystem
