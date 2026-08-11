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

/-- **Typing sees a context only through lookup.** Two contexts agreeing at every name type the
same terms.

True of any judgement worth the name — a context is a finite map, and a rule can only consult it
by looking a variable up — but `HasType` is an arbitrary relation, so nothing may assume it. STLC
proves it as `HasType.cong`, which is exactly this field.

A **mixin** over `[HasType N Tm Ty]`, not an `extends`. Extending would create a second
`HasType`, and a caller wanting this alongside `PrincipalElaborate` would then hold two unrelated
judgements — the diamond `LawfulMVars` was restructured to flatten. A `Prop`-valued class over the
instance already in scope cannot open one.

It is what makes a substituted context usable: `Std.HashMap` has no `getElem?` extensionality, so
`pSubst Γ σ = Γ` is not provable even when Γ is ground, and the keywise fact
(`Context.pSubst_get?_of_ground`) is all there is. This law is what turns that into a statement
about typing. -/
class LawfulContext (N Tm Ty : Type) [nameAlphabet : NameAlphabet N] [HasType N Tm Ty] : Prop where
  /-- Typing transports along keywise agreement of contexts. -/
  cong : ∀ {Γ Γ' : Context N Ty} {t : Tm} {τ : Ty},
    (∀ x, Γ.get? x = Γ'.get? x) → HasType.HasType Γ t τ → HasType.HasType Γ' t τ

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
relation to it, and `PrincipalElaborate` below would still typecheck — its `MGUProp`
predicate is built entirely out of `pSubst`, so a nonsense `pSubst` yields a nonsense
specification that an implementation could satisfy vacuously. Stability is what ties the algorithmic side back to the
judgement.

Same reasoning as `Preservation` being a field of `LawfulTypeSystem`: put the law where an
instance cannot be built without discharging it, and keep the bare class instanceable so
`pSubst` is usable before anyone proves anything about it.

**Extending both parents is what joins the hierarchy back together, and it is load-bearing.**
`MVars` and `LawfulTypeSystem` each extend `TypeSystem`, so taken separately they carry *different*
`toTypeSystem` fields — `[LawfulTypeSystem …] [MVars …]` as two binders gives two unrelated
judgements, and feeding an elaboration result to `Preservation` is then a type error, which is the
one thing this interface exists to make possible. Extending both here makes Lean flatten the
diamond: `#print` shows the constructor taking `[toMVars]` plus the two proofs, with
`toLawfulTypeSystem` derived rather than stored, so there is exactly one `HasType` and one `Step`.
Checked: `L.toMVars.toTypeSystem = L.toLawfulTypeSystem.toTypeSystem` by `rfl`, and the
elaborate-then-preserve example that failed before now compiles.

The consequence for callers is that the joint class is the one to ask for. Requesting
`LawfulTypeSystem` and `MVars` as separate parameters reintroduces the split. -/
class LawfulMVars (N Tm Ty : Type) [nameAlphabet : NameAlphabet N] extends MVars N Tm Ty, LawfulTypeSystem N Tm Ty where
  /-- Applying a substitution to context, term and type at once preserves the typing derivation.
  For a system whose types carry metavariables this is the workhorse: it is what lets a solved
  constraint set be *applied* and still describe a typing. -/
  Stability : ∀ {Γ : Context N Ty} {t : Tm} {τ : Ty} (σ : Subst Ty),
    HasType Γ t τ → HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ)

/-- **The elaboration problem, solved principally.** Given a context, a term and a declared type —
any of which may still hold metavariables — produce a substitution making the triple a real typing
*that every other solution factors through*, or a proof that no substitution does.

`MGUProp`, not `Option`, on both counts. The negative case is a *proof of absence*, so an instance
cannot be built by an algorithm that merely fails to find something; and the positive case carries
most-generality, so a caller may commit to the answer without fear that a later constraint would
have preferred a different one. Both are fields for the reason `Preservation` is a field of
`LawfulTypeSystem`: put the law where an instance cannot be built without discharging it.

## One class, not two, and no `elaborateMGU`

This used to be a `SolutionProp`-valued `DecideableElaborate` with most-generality bolted on
afterwards as a separate `PrincipalElaborate.Principal` field, plus an `elaborateMGU` that glued
the two back into the `MGUProp` they should have been. The split bought instances that exist
before their hard law is proved, and cost a three-way spread of one idea — with the reassembly
written out by hand, and its converse only asserted in prose.

`MGUProp` was already the right type; `Substitution/Unification/MGU.lean` defines it, so nothing
new is introduced here. A caller that does not want most-generality does not need a weaker class
either — `MGUProp.toSolution` forgets it, and everything proved about `SolutionProp` applies.

**What it costs, stated plainly.** Deciding typeability is settled for STLC; most-generality is
not, and an instance therefore cannot be built today without a `sorry` somewhere. That is a real
price, and the reason the split existed. It is paid in one named theorem at the plug-in
(`Stlc/Named/Typing/JComplete.lean`), where the obligation is visible, rather than hidden behind a
class nobody instantiates. -/
class PrincipalElaborate (N Tm Ty : Type) [nameAlphabet : NameAlphabet N] extends LawfulMVars N Tm Ty where
  /-- Decidable typing judgement, with a principal witness. -/
  elaborate : (Γ : Context N Ty) → (t : Tm) → (τ : Ty) →
      MGUProp (fun σ : Subst Ty =>
        HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ))

end LambdaLab.TypeSystem
