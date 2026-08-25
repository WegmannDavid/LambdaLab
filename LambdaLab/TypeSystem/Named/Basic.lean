import LambdaLab.Relation.Closure
import LambdaLab.Relation.Normalization
import LambdaLab.TypeSystem.Named.Context
import LambdaLab.Nominal.Unification.MGU
import LambdaLab.Nominal.Instances

/-!
# `TypeSystem` — a named object language and its metatheory, one obligation per class

Where `Atom` fixes what a *name* is and `Context` what a *context* is, this fixes what a
*type system over them* is: a typing judgement, a reduction relation, and the theorems tying the
two together.

## One class per obligation, and every law is a field

Nothing here is a single bundle. `HasType` and `Step` each carry one operation and demand nothing
of it; `TypeSystem` is their composite and is lawless too; and each law lives in a class above that
cannot be instantiated without discharging it — `Preservation` and `cong` in `LawfulTypeSystem`,
`Stability` in `LawfulMVars`, principality in `PrincipalElaborate`, and the reduction side in
`StronglyNormalizing`, `Confluent` and `LawfulHasEval`.

A law in a field is what makes a class theorem-carrying: an implementation cannot claim the
interface without proving it, and anything downstream may use it without re-proving or re-assuming
it. Splitting the tower is what keeps that affordable — a bare `Step` is usable before anyone
proves anything about reduction, and a system that normalizes but does not elaborate instantiates
the classes it satisfies and no more. A field no instance can discharge is a field that keeps
instances from existing.

## `N`, `Tm` and `Ty` are parameters

All three are class parameters, with `Atom N` as an instance binder alongside, so a
consumer names the three types it works over and leaves the rest to instance search. The classes
compose by `extends`, which is what makes the diamonds flatten to exactly one `HasType` and one
`Step` — spelled out at `LawfulMVars`, where it is load-bearing, and again at `LawfulHasEval`.

## Scope

Normalization, confluence and elaboration are **not** fields of `TypeSystem` or
`LawfulTypeSystem`. They hold for STLC but not for every system worth describing this way, so each
is a class of its own that a language opts into. Preservation is the one property general enough to
demand of everything with a reduction relation, which is why it — and only it — sits in the first
lawful class.

## The notation lives here

`⟶`, `⟶*` and `Γ ⊢ t : τ` are declared once each, on the class that owns the field they abbreviate,
and the concrete languages supply *instances* rather than notation of their own. Where a local
notation and the class one are both in scope they both elaborate and are defeq, so every use
becomes `Ambiguous term`; the local ones were removed for that reason. Argument levels are pinned
so that `Γ ⊢ t : τ → P` splits at the arrow.
-/

namespace LambdaLab.TypeSystem.Named

open LambdaLab.Nominal (Atom)

/-- **Reduction.** One relation and no law; `LawfulTypeSystem` is where it acquires one. -/
class Step (Tm : Type) where
  /-- Single-step reduction. -/
  Step : Tm → Tm → Prop

@[inherit_doc] infix:50 " ⟶ " => Step.Step

/-- Multi-step reduction: the reflexive-transitive closure of `Step`. -/
infix:50 " ⟶* " => RTC Step.Step

/-- **`t` is in normal form**: no reduction applies to it.

Spelled `∀ t', ¬ t ⟶ t'` rather than `¬ ∃ t', t ⟶ t'` — the two are equivalent, but this form
applies directly to a candidate reduct, so discharging it is `intro t' h` and refuting `h`,
with no `push_neg` in between.

This is what makes a normalizer's output an *answer* rather than merely some term reachable from
the input; `LawfulHasEval` demands it of `eval`, and it is the only place the framework says what
"done reducing" means. -/
def NormalForm {Tm : Type} [Step Tm] (t : Tm) : Prop := ∀ t', ¬ t ⟶ t'

/-- **The typing judgement, and nothing else.** One field, no laws, so a language may supply it
long before it can prove anything about it — `LawfulTypeSystem` below is where the properties
live. -/
class HasType (N Tm Ty : Type) [atom : Atom N] where
  /-- The typing judgement, over contexts keyed by `N`. -/
  HasType : Context N Ty → Tm → Ty → Prop

/-- **The typing judgement**: `Γ ⊢ t : τ` — under `Γ`, the term `t` has type `τ`.

Precedence and spelling are the concrete judgements', so a generic statement reads exactly like
the instance it will be applied to. `Stlc/Named/Typing/Basic.lean` dropped its own copy when this
one arrived, and had to: both elaborate wherever the instance is in scope, and being defeq they
make every use `Ambiguous term`. `Stlc/DeBruijn/Typing.lean` keeps a local one and may — its
context is a `List Ty`, which cannot instantiate `HasType`, so there is no second reading to
collide with and the elaborator tells the two apart by the type of `Γ`.

Argument levels are pinned at 41 so that `Γ ⊢ t : τ → P` splits at the arrow; unpinned, the
trailing slot parses at level 0, swallows it, and the statement fails to elaborate. -/
notation:40 Γ:41 " ⊢ " t:41 " : " τ:41 => HasType.HasType Γ t τ

/-- **Judgement and reduction together**, and still no law. It exists so that everything above has
one class to extend, and therefore one `HasType` and one `Step` to talk about. -/
class TypeSystem (N Tm Ty : Type) [atom : Atom N] extends HasType N Tm Ty, Step Tm where

/-- **A judgement that is well-behaved**: reduction preserves it, and it reads a context only
through lookup.

Both are properties of the *judgement alone* — neither mentions substitution, elaboration or any
consumer — which is why they sit together here and not further down the tower. `TypeSystem` says
what the pieces are; this says they behave. -/
class LawfulTypeSystem (N Tm Ty : Type) [atom : Atom N] extends TypeSystem N Tm Ty where
  /-- Reduction preserves types. -/
  Preservation : ∀ {Γ : Context N Ty} {t : Tm} {τ : Ty} {t' : Tm}, Γ ⊢ t : τ → t ⟶ t' → Γ ⊢ t' : τ
  /-- **Typing sees a context only through lookup**: two contexts agreeing at every name type the
  same terms.

  True of any judgement worth the name — a context is a finite map, and a rule can only consult it
  by looking a variable up — but `HasType` is an arbitrary relation, so nothing may assume it. STLC
  proves it as `HasType.cong`, which is exactly this field.

  It is what makes a *substituted* context usable: `Std.HashMap` has no `getElem?` extensionality,
  so `pSubst Γ σ = Γ` is not provable even when `Γ` is ground, and the keywise fact
  (`Context.pSubst_get?_of_ground`) is all there is. This law turns that into a statement about
  typing. -/
  cong : ∀ {Γ Γ' : Context N Ty} {t : Tm} {τ : Ty},
    (∀ x, Γ.get? x = Γ'.get? x) → Γ ⊢ t : τ → Γ' ⊢ t : τ

/-- A type system whose types carry metavariables, so substitution acts on both levels:
`pSubst : Tm → Subst Nat Ty → Tm` for the type annotations inside a term, and
`pSubst : Ty → Subst Nat Ty → Ty` for types themselves.

**Fields, not parents.** `extends … HasSubst Nat Tm Ty, HasSubst Nat Ty Ty` does not work: Lean
deduplicates parent structures by class *head*, so the second is dropped with only a
`Duplicate parent structure` warning, leaving the class with no type-level substitution at all.
Naming the parents (`extends tmSubst : HasSubst Nat Tm Ty, …`) makes no difference. Fields plus the
`attribute` line below are the way to carry two instances of one class.

**On filling them in.** Both instances usually exist already — `HasSubst Nat (Term N) Ty`, and
`HasSubst Nat Ty Ty` via `Signature` — so fill the fields with `inferInstance` rather than fresh
definitions. Then the bundled copies are *definitionally* the canonical ones and lemmas proved
about either apply to both. Two independent `pSubst`s for the same type would typecheck and then
fail to talk to each other somewhere far away. -/
class MVars (N Tm Ty : Type) [atom : Atom N] extends TypeSystem N Tm Ty where
  /-- Substitution of types into a term's annotations. Fill with `inferInstance` where possible. -/
  tmSubst : HasSubst Nat Tm Ty
  /-- Substitution of types into types. Fill with `inferInstance` where possible. -/
  tySubst : HasSubst Nat Ty Ty

/-! `reducible` is required of instance-valued projections; `low` is not cosmetic. At default
priority `MVars.tySubst` *displaces* the canonical `Signature.instHasSubst` as the instance found
for `HasSubst Nat Ty Ty` — it wins by being declared later, and it resolves the undetermined `N` and
`Tm` by picking whatever single `MVars` instance is in scope. `low` puts the real instance back in
front and leaves the projections as the fallback they should be. -/
attribute [reducible, instance low] MVars.tmSubst MVars.tySubst

/-- `MVars` supplies two substitution operations and demands nothing of them. This adds the one
law that makes them mean something: **typing is stable under substitution**.

Without it an `MVars` instance may pair a perfectly good `HasType` with a `pSubst` that has no
relation to it, and `PrincipalElaborate` below would still typecheck — its `PrincipalProp`
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
diamond: `#print` shows the constructor taking `[toMVars]` plus `LawfulTypeSystem`'s two proofs
and this class's own fields, with `toLawfulTypeSystem` derived rather than stored, so there is
exactly one `HasType` and one `Step`.
Checked: `L.toMVars.toTypeSystem = L.toLawfulTypeSystem.toTypeSystem` by `rfl`, and the
elaborate-then-preserve example that failed before now compiles.

The consequence for callers is that the joint class is the one to ask for. Requesting
`LawfulTypeSystem` and `MVars` as separate parameters reintroduces the split. -/
class LawfulMVars (N Tm Ty : Type) [atom : Atom N] extends MVars N Tm Ty, LawfulTypeSystem N Tm Ty where
  /-- Applying a substitution to context, term and type at once preserves the typing derivation.
  For a system whose types carry metavariables this is the workhorse: it is what lets a solved
  constraint set be *applied* and still describe a typing. -/
  Stability : ∀ {Γ : Context N Ty} {t : Tm} {τ : Ty} (σ : Subst Nat Ty),
    Γ ⊢ t : τ → HasSubst.pSubst Γ σ ⊢ HasSubst.pSubst t σ : HasSubst.pSubst τ σ
  /-- Substitution fixes a ground type. -/
  tyGroundStable : GroundStable Nat Ty Ty
  /-- …and a term whose annotations are all solved. -/
  tmGroundStable : GroundStable Nat Tm Ty
  /-- Substituting twice is substituting once, through the composite — at the type level… -/
  tyLawfulComp : LawfulComp Nat Ty Ty
  /-- …and at the term level. -/
  tmLawfulComp : LawfulComp Nat Tm Ty
  /-- Bindings above a type's threshold do not act on it… -/
  tyLawfulRestrict : LawfulRestrict Nat Ty Ty
  /-- …nor on a term's. Together these are what let the vernacular hand back a solution pruned to
  the source's own metavariables instead of the elaborator's internal scaffolding. -/
  tmLawfulRestrict : LawfulRestrict Nat Tm Ty

/-! The six laws above are `Prop` mixins over the `HasSubst` instances `MVars` carries, so
gathering them here mints no new operation and reopens no diamond. `low`, like the `MVars`
projections above and for the same reason: a free-standing instance must keep winning where one applies. It
always does apply for a concrete language, and it is *definitionally* the field, since the field
was filled from it.

They cannot replace the free-standing instances, and are not meant to. `Nominal/Unification/Subst.lean`
derives `GroundStable`/`LawfulComp` for pairs and lists from their components, and `Bridge.lean`
for any `Signature` — derivations that resolve by ordinary search, and which are what make a whole
`Vernacular.Program` substitutable. What the fields buy is that a *generic* consumer, working at an
abstract `Tm`/`Ty` where no such instance applies, needs one binder instead of six. -/
attribute [instance low] LawfulMVars.tyGroundStable LawfulMVars.tmGroundStable
  LawfulMVars.tyLawfulComp LawfulMVars.tmLawfulComp
  LawfulMVars.tyLawfulRestrict LawfulMVars.tmLawfulRestrict

/-- **The elaboration problem, solved principally.** Given a context, a term and a declared type —
any of which may still hold metavariables — produce a substitution making the triple a real typing
*that every other solution factors through*, or a proof that no substitution does.

`PrincipalProp`, not `Option`, on both counts. The negative case is a *proof of absence*, so an instance
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

`PrincipalProp` was already the right type; `Nominal/Unification/MGU.lean` defines it, so
nothing new is introduced here. A caller that does not want most-generality does not need a weaker
class either — `PrincipalProp.toSolution` forgets it, and everything proved about `SolutionProp`
applies.

## Which most-generality, and why not the obvious one

`elaborate` is compared at `MoreGeneralOn`, not `MoreGeneral`. That is forced, not chosen:
an elaborator draws metavariables the source never mentioned, and its answer may legitimately
mention them — `f (g b)` with `f, g` unknown elaborates to `?0 ↦ ?2 ⇒ ⋆`, `?1 ↦ ⋆ ⇒ ?2`, where
`?2` names the intermediate type. A competing solution says nothing about `?2`, so no witness can
factor it through the answer *at the type `?2` itself*, which is what `MoreGeneral`'s `∀ t` demands.
`Stlc/Named/Typing/Principality.lean` proves that statement false for the STLC elaborator; the
restricted one is `JComplete.elabSubst_principal_below`, and it is a theorem.

`sourceSupp` is the threshold, supplied by the language rather than computed here. `Context N Ty`
has two `HasVars` instances — the generic `HashMap` one, which counts keys, and the `Context` one,
which does not — and a threshold computed in this file would be read against the first while a
language's own lemmas are stated against the second. A field sidesteps the question: the language
says what its source threshold is, and proves its principality against that. -/
class PrincipalElaborate (N Tm Ty : Type) [atom : Atom N] extends LawfulMVars N Tm Ty where
  /-- The metavariables that belong to the *source* triple rather than to the elaborator — the
  atom set `elaborate`'s principality is stated on below. A language that draws no metavariables
  of its own can say `[]`, and then the claim is unrestricted. -/
  sourceSupp : Context N Ty → Tm → Ty → List Nat
  /-- Decidable typing judgement, with a principal witness — principal on the source, in the sense
  of `MoreGeneralOn` and for the reason set out above. -/
  elaborate : (Γ : Context N Ty) → (t : Tm) → (τ : Ty) →
      PrincipalProp (MoreGeneralOn (sourceSupp Γ t τ))
        (fun σ : Subst Nat Ty =>
          HasSubst.pSubst Γ σ ⊢ HasSubst.pSubst t σ : HasSubst.pSubst τ σ)
  /-- **Groundness of a type is decidable.** `HasVars.Ground` is `∀ n, ¬ isFree x n`, which no
  instance decides by unfolding, so a language routes it to its own structural check.

  Data rather than a law, and the one field here that is arguably a consumer's concern rather than
  a type system's — anything that *checks* elaboration output needs it, and nothing else does. It
  is here because `Ground` is `HasVars` vocabulary, not vernacular vocabulary: a class promising
  that its types carry metavariables and that it solves them principally may as well promise that
  you can tell when they are gone.

  It should eventually not be a field at all, and the case is now stronger than it was. The old
  argument went through `fresh_gt_free`, which made groundness a *bounded* quantifier
  (`Ground x ↔ ∀ n < fresh x, ¬ isFree x n`). Since the port, `supp` is exact and
  `HasVars.ground_iff_supp_nil` says `Ground x ↔ supp x = []` — decidable outright, with no
  quantifier to bound and no `Decidable (isFree x n)` needed. Removing the field still touches
  every consumer, so it is deliberately not done here. -/
  tyGroundDec : DecidablePred (HasVars.Ground (A := Nat) : Ty → Prop)
  /-- The same for terms. -/
  tmGroundDec : DecidablePred (HasVars.Ground (A := Nat) : Tm → Prop)

/-! `reducible` besides `low`, so that a `Ground` check written against these is definitionally the
language's own structural check rather than something merely propositionally equal to it. -/
attribute [reducible, instance low] PrincipalElaborate.tyGroundDec PrincipalElaborate.tmGroundDec

/-- **Well-typed terms cannot reduce forever.** A class of its own rather than a field of
`LawfulTypeSystem`, because it fails for any system with general recursion. STLC proves it at
`String` (`Stlc.Named.sn_of_hasType`, from `HasType.sn`) and instantiates the class there
(`instStronglyNormalizing`), pinned at `String` like everything that detours through de Bruijn. -/
class StronglyNormalizing (N Tm Ty : Type) [atom : Atom N] extends LawfulMVars N Tm Ty where
  /-- **The term at hand admits no infinite reduction sequence.**

  `SN` is `Relation/Normalization.lean`'s, so the direction question is settled there rather than
  here: `SN (· ⟶ ·) t` means every reduction sequence *out of* `t` is finite, and the reversal an
  `Acc` formulation would need is exactly what that file's inductive avoids.

  It says `SN` of **this** term, not well-foundedness of `⟶`. The latter would assert termination
  for every term of `Tm`, which no language can discharge: a term type holds the untypable
  divergent terms too, and `Γ ⊢ t : τ` says nothing about them — `Stlc.Named.omega_not_sn` is the
  witness. `SN` restricts the claim to the term the derivation is about, which is what
  `Stlc.Named.HasType.sn` proves. -/
  StronglyNormalizing : ∀ {Γ : Context N Ty} {t : Tm} {τ : Ty}, Γ ⊢ t : τ → SN (· ⟶ ·) t

/-- **A normalizer.** Data only — `LawfulHasEval` below is where the answer acquires meaning.

`eval` takes the typing derivation rather than the bare term, so it is total on exactly the terms
the judgement accepts, with no error case to invent for input it cannot reduce, and an
implementation may recurse on the derivation. -/
class HasEval (N Tm Ty : Type) [atom : Atom N] extends LawfulMVars N Tm Ty where
  eval (Γ : Context N Ty) (t : Tm) (τ : Ty) : Γ ⊢ t : τ → Tm

/-- **Reduction is confluent on well-typed terms**: whatever a term reduces to can be brought back
together.

Opt-in, for the reason `StronglyNormalizing` is. `TypeSystem` is the parent because that is all the
statement mentions — the judgement and the relation — and the substitution laws are irrelevant to
it. The typing hypothesis makes the field *weaker* than the fact STLC proves
(`Stlc.DeBruijn.MStep.confluent` needs no typing at all), which is deliberate: a system whose
confluence does depend on typing can still instantiate this, and one whose does not just ignores
the hypothesis.

What it buys, together with `LawfulHasEval`'s two fields: `eval`'s answer is not merely *a* normal
form of its input but *the* one, since a reachable normal form is unique once reduction is
confluent. -/
class Confluent (N Tm Ty : Type) [atom : Atom N] extends TypeSystem N Tm Ty where
  /-- **Confluence of reduction**: if a term reduces to two others, they have a common reduct. -/
  Confluent : ∀ {Γ : Context N Ty} {t t₁ t₂ : Tm} {τ : Ty},
    Γ ⊢ t : τ → t ⟶* t₁ → t ⟶* t₂ → ∃ t', t₁ ⟶* t' ∧ t₂ ⟶* t'

/-- **`eval` is a normalizer for real**: its answer admits no further reduction, and it is a normal
form *of the input*.

Three parents, and the diamond flattens as it must. `HasEval` and `StronglyNormalizing` reach
`TypeSystem` through `LawfulMVars` while `Confluent` extends it directly; `#print` shows the
constructor taking `[toHasEval]` plus proofs, with the other two parents derived rather than
stored, and `toHasEval.toLawfulMVars.toTypeSystem = toConfluent.toTypeSystem` holds by `rfl`. See
`LawfulMVars` for what goes wrong when it does not. -/
class LawfulHasEval (N Tm Ty : Type) [atom : Atom N] extends
    HasEval N Tm Ty,
    StronglyNormalizing N Tm Ty,
    Confluent N Tm Ty where
  /-- **`eval` finishes the job**: its result admits no further reduction. -/
  evalNormal {Γ : Context N Ty} {t : Tm} {τ : Ty} (h : Γ ⊢ t : τ) :
    NormalForm (eval Γ t τ h)
  /-- **`eval` answers the question asked**: its result is reachable from the input, so it is a
  normal form *of `t`* and not merely some normal form. Neither field implies the other —
  the first alone is satisfied by any constant normal term, the second by `eval = id`. -/
  evalReachable {Γ : Context N Ty} {t : Tm} {τ : Ty} (h : Γ ⊢ t : τ) :
    t ⟶* eval Γ t τ h

end LambdaLab.TypeSystem.Named
