import LambdaLab.TypeSystem.Named.Basic
import LambdaLab.TypeSystem.DeBruijn.Context

/-!
# `TypeSystem` for a de Bruijn object language — the named tower, minus the names

The mirror of `TypeSystem/Named/Basic.lean` over positional contexts: the same
one-class-per-obligation tower — judgement, reduction, substitution stability, principal
elaboration, normalization, evaluation, term substitution — with every `N` and `Atom N` gone,
because a variable *is* its index and there is no name type to be parametric in.

## What is reused rather than mirrored

`Step`, `NormalForm` and the arrows `⟶`/`⟶*` come from the named file unchanged, by `open`:
they never mentioned a name or a context, and the arrows are declared once in the whole library,
on the class that owns the field (`fee773c` made that a rule; a second declaration here would
un-make it). The `⊢` notation *is* redeclared — its named twin elaborates only at a
`Std.HashMap` context, this one only at a `List`, so every use is disambiguated by the type of
`Γ` and the two never both succeed (the situation `Named/Basic.lean`'s notation docstring
describes for `Stlc/DeBruijn`'s local turnstile, made systematic).

## What is *not* here, and why it is not a loss

`HasAlphaEq` and `LawfulAlphaEq` have no counterpart: a de Bruijn index is its binding, two
α-equivalent terms are the same term, and the language's "when are two terms the same" is `Eq`.
Everything the named tower threads through `≈α` lands here on the nose — `Confluent` joins its
reducts with equality, which is the textbook diamond the named docstring says `Stlc.DeBruijn`
already has (`Stlc.DeBruijn.MStep.confluent`), and `LawfulHasEval`'s uniqueness-of-answer story
needs no quotient.

`cong` is demoted from field to theorem for the same structural reason, in the other direction:
the named side demands it of every judgement because hashmaps have no extensionality, so
keywise-equal contexts are all a consumer can produce. Lists agreeing at every index are *equal*
(`List.ext_getElem?`), so the law holds of every judgement whatsoever and demanding it would be
a field no instance could fail to discharge.

## Scope — this tower is for metatheory, not for the front end

`FreeName.lean` has no mirror (nothing to reserve — there are no names to collide with
keywords), and the `Vernacular/` layer is not mirrored **and will not be**: the compiler front
end only ever consumes the named tower. This one exists for the division of labour the two
STLCs already practice — properties are *proved* where binding is positional and α-noise
cannot arise (`Stlc/Named` discharges its `Confluent` and `StronglyNormalizing` by detouring
through `Stlc/DeBruijn`), then carried across the translation to the named system the pipeline
runs on. A de Bruijn language instantiates this interface to *host* that metatheory, not to be
compiled.
-/

namespace LambdaLab.TypeSystem.DeBruijn

open LambdaLab.TypeSystem.Named (Step NormalForm)

/-- **The typing judgement, and nothing else** — one field, no laws, over positional contexts.
The de Bruijn `HasType` has two parameters where the named one has three: no name type, no
`Atom`. -/
class HasType (Tm Ty : Type) where
  /-- The typing judgement, over contexts indexed by position. -/
  HasType : Context Ty → Tm → Ty → Prop

/-- **The typing judgement**: `Γ ⊢ t : τ` — under `Γ`, the term `t` has type `τ`.

The same spelling as the named turnstile, and deliberately: the two elaborate at different
context types (`List` here, `Std.HashMap` there), so any use is resolved by the type of `Γ` and
at most one reading survives. Argument levels are pinned at 41 for the reason the named one
pins them: `Γ ⊢ t : τ → P` must split at the arrow. -/
notation:40 Γ:41 " ⊢ " t:41 " : " τ:41 => HasType.HasType Γ t τ

/-- **Judgement and reduction together**, and still no law — one class for everything above to
extend, so there is one `HasType` and one `Step` in the tower. -/
class TypeSystem (Tm Ty : Type) extends HasType Tm Ty, Step Tm where

/-- **A judgement that is well-behaved**: reduction preserves it.

One field where the named class has two. `cong` — typing sees a context only through lookup —
is not an obligation here, because it is not one a de Bruijn judgement could fail: contexts
agreeing at every index are equal outright. It is `LawfulTypeSystem.cong` below, a theorem. -/
class LawfulTypeSystem (Tm Ty : Type) extends TypeSystem Tm Ty where
  /-- Reduction preserves types. -/
  Preservation : ∀ {Γ : Context Ty} {t : Tm} {τ : Ty} {t' : Tm},
    Γ ⊢ t : τ → t ⟶ t' → Γ ⊢ t' : τ

/-- **Typing sees a context only through lookup** — the named tower's `cong` field, free here:
two contexts agreeing at every index are equal (`List.ext_getElem?`), so the judgement never
gets to tell them apart. This is the first dividend of positional contexts, and why the class
above has one field instead of two. -/
theorem LawfulTypeSystem.cong {Tm Ty : Type} [LawfulTypeSystem Tm Ty]
    {Γ Γ' : Context Ty} {t : Tm} {τ : Ty}
    (h : ∀ i : Nat, Γ[i]? = Γ'[i]?) (ht : Γ ⊢ t : τ) : Γ' ⊢ t : τ :=
  List.ext_getElem? h ▸ ht

/-- A type system whose types carry metavariables, so substitution acts on both levels —
exactly the named `MVars`, which never looked at a name: metavariables are `Nat`-indexed
whatever the binding discipline.

**Fields, not parents**, for the named class's reason: Lean deduplicates parent structures by
class head, so `extends HasSubst Nat Tm Ty, HasSubst Nat Ty Ty` silently drops the second.
Fill both with `inferInstance` where the canonical instances exist, so the bundled copies are
definitionally the canonical ones. -/
class MVars (Tm Ty : Type) extends TypeSystem Tm Ty where
  /-- Substitution of types into a term's annotations. Fill with `inferInstance` where possible. -/
  tmSubst : HasSubst Nat Tm Ty
  /-- Substitution of types into types. Fill with `inferInstance` where possible. -/
  tySubst : HasSubst Nat Ty Ty

/-! `reducible` + `low`, as on the named projections and for the same reason: at default
priority these displace the canonical instances they were filled from. -/
attribute [reducible, instance low] MVars.tmSubst MVars.tySubst

/-- The law that makes `MVars` mean something: **typing is stable under substitution**, plus the
six `Prop` mixins over the two `HasSubst` instances. Extending both parents joins the hierarchy
back together — see the named docstring for the diamond this flattens; the guard at the bottom
of this file pins it. -/
class LawfulMVars (Tm Ty : Type) extends MVars Tm Ty, LawfulTypeSystem Tm Ty where
  /-- Applying a substitution to context, term and type at once preserves the typing
  derivation. -/
  Stability : ∀ {Γ : Context Ty} {t : Tm} {τ : Ty} (σ : Subst Nat Ty),
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
  /-- …nor on a term's. -/
  tmLawfulRestrict : LawfulRestrict Nat Tm Ty

attribute [instance low] LawfulMVars.tyGroundStable LawfulMVars.tmGroundStable
  LawfulMVars.tyLawfulComp LawfulMVars.tmLawfulComp
  LawfulMVars.tyLawfulRestrict LawfulMVars.tmLawfulRestrict

/-- **The elaboration problem, solved principally** — the named class with the name parameter
gone. `PrincipalProp` on both counts for the named reasons: the negative case is a proof of
absence, the positive carries most-generality at `MoreGeneralOn (sourceSupp …)`, principal on
the *source's* metavariables because an elaborator legitimately draws its own. -/
class PrincipalElaborate (Tm Ty : Type) extends LawfulMVars Tm Ty where
  /-- The metavariables that belong to the *source* triple rather than to the elaborator. A
  language that draws no metavariables of its own can say `[]`, and then the claim is
  unrestricted. -/
  sourceSupp : Context Ty → Tm → Ty → List Nat
  /-- Decidable typing judgement, with a principal witness. -/
  elaborate : (Γ : Context Ty) → (t : Tm) → (τ : Ty) →
      PrincipalProp (MoreGeneralOn (sourceSupp Γ t τ))
        (fun σ : Subst Nat Ty =>
          HasSubst.pSubst Γ σ ⊢ HasSubst.pSubst t σ : HasSubst.pSubst τ σ)
  /-- Groundness of a type is decidable — see the named field for why this is (still) a field. -/
  tyGroundDec : DecidablePred (HasVars.Ground (A := Nat) : Ty → Prop)
  /-- The same for terms. -/
  tmGroundDec : DecidablePred (HasVars.Ground (A := Nat) : Tm → Prop)

attribute [reducible, instance low] PrincipalElaborate.tyGroundDec PrincipalElaborate.tmGroundDec

/-- **Well-typed terms cannot reduce forever.** Opt-in, as the named one is and for its reason:
false for any system with general recursion. `SN` of *this* term, not well-foundedness of `⟶` —
the term type also holds the untypable divergent terms. -/
class StronglyNormalizing (Tm Ty : Type) extends LawfulMVars Tm Ty where
  /-- The term at hand admits no infinite reduction sequence. -/
  StronglyNormalizing : ∀ {Γ : Context Ty} {t : Tm} {τ : Ty}, Γ ⊢ t : τ → SN (· ⟶ ·) t

/-- **A normalizer.** Data only; `LawfulHasEval` is where the answer acquires meaning. `eval`
takes the derivation, so it is total on exactly the terms the judgement accepts. -/
class HasEval (Tm Ty : Type) extends LawfulMVars Tm Ty where
  eval (Γ : Context Ty) (t : Tm) (τ : Ty) : Γ ⊢ t : τ → Tm

/-- **Reduction is confluent on well-typed terms** — and the reducts join **on the nose**.

This is where dropping α-equivalence pays: the named `Confluent` joins up to `≈α` because a
named β-rule renames binders and two reduction paths reach syntactically different terms, and it
must extend `LawfulAlphaEq` to keep that joining from being satisfiable vacuously. A de Bruijn
reduct has no names to differ in — `Stlc.DeBruijn.MStep.confluent` is already on the nose — so
the field is the textbook diamond, the parent is bare `TypeSystem`, and there is no vacuity to
legislate against: equality cannot be weakened by a language.

The typing hypothesis is kept, as it is kept there: a system whose confluence needs typing can
instantiate this, and one whose does not ignores it. -/
class Confluent (Tm Ty : Type) extends TypeSystem Tm Ty where
  /-- **Confluence of reduction**: two reducts of one term have a common reduct. -/
  Confluent : ∀ {Γ : Context Ty} {t t₁ t₂ : Tm} {τ : Ty},
    Γ ⊢ t : τ → t ⟶* t₁ → t ⟶* t₂ → ∃ u, t₁ ⟶* u ∧ t₂ ⟶* u

/-- **`eval` is a normalizer for real**: its answer admits no further reduction, is reachable
from the input, and invents no metavariables. With `Confluent` on the nose, the answer is not
merely *a* normal form of the input but *the* normal form — no "up to `≈α`" to carry. The
diamond flattens as the named one does; the guard below pins it. -/
class LawfulHasEval (Tm Ty : Type) extends
    HasEval Tm Ty,
    StronglyNormalizing Tm Ty,
    Confluent Tm Ty where
  /-- **`eval` finishes the job**: its result admits no further reduction. -/
  evalNormal {Γ : Context Ty} {t : Tm} {τ : Ty} (h : Γ ⊢ t : τ) :
    NormalForm (eval Γ t τ h)
  /-- **`eval` answers the question asked**: its result is reachable from the input. Neither
  field implies the other — the first alone is satisfied by any constant normal term, the
  second by `eval = id`. -/
  evalReachable {Γ : Context Ty} {t : Tm} {τ : Ty} (h : Γ ⊢ t : τ) :
    t ⟶* eval Γ t τ h
  /-- **`eval` does not invent metavariables**: a ground term's normal form is ground. -/
  evalGround {Γ : Context Ty} {t : Tm} {τ : Ty} (h : Γ ⊢ t : τ) :
    HasVars.Ground (A := Nat) t → HasVars.Ground (A := Nat) (eval Γ t τ h)

/-- **Substituting a term for the variable most recently bound** — index `0` — with the laws a
stage that inlines definitions needs.

The named `tsubst` takes the name being substituted; here the position says which variable, so
the operation drops an argument. And the named docstring's warning at `tsubst_closed` — that a
capture-avoiding substitution renames binders whether or not it had anything to do, so the
identity law genuinely needs `v` closed — describes a failure mode this representation cannot
have: there is no capture and nothing to rename. The hypothesis is kept because every caller
has it and the weaker demand is the easier instantiation, but here it is parity, not
necessity. -/
class HasTermSubst (Tm Ty : Type) extends LawfulMVars Tm Ty where
  /-- Substitute `v` for the variable at index `0`. -/
  tsubst : Tm → Tm → Tm
  /-- **Substitution preserves typing** — the substitution lemma, in cons form. -/
  tsubst_typing {Γ : Context Ty} {σ τ : Ty} {t v : Tm} :
    Γ.cons σ ⊢ t : τ → (Context.empty : Context Ty) ⊢ v : σ → Γ ⊢ tsubst t v : τ
  /-- **Substitution introduces no metavariable.** -/
  tsubst_ground {t v : Tm} :
    HasVars.Ground (A := Nat) t → HasVars.Ground (A := Nat) v →
      HasVars.Ground (A := Nat) (tsubst t v)
  /-- **Substituting into a closed term does nothing** — inlining is idempotent. -/
  tsubst_closed {σ τ : Ty} {t v : Tm} :
    (Context.empty : Context Ty) ⊢ t : τ → (Context.empty : Context Ty) ⊢ v : σ →
      tsubst t v = t
  /-- **A closed term types anywhere.** Not an instance of `cong`, which needs agreement at
  every index; here the contexts agree nowhere. -/
  weaken_closed {Γ : Context Ty} {t : Tm} {τ : Ty} :
    (Context.empty : Context Ty) ⊢ t : τ → Γ ⊢ t : τ

/-- **A language whose programs can be elaborated and then run** — the conjunction is the
content, as it is for the named class: taken separately, the parents carry unrelated judgements
and the derivation elaboration hands over is not the one `eval` accepts. -/
class Runnable (Tm Ty : Type) extends
    PrincipalElaborate Tm Ty,
    LawfulHasEval Tm Ty,
    HasTermSubst Tm Ty

/-! ## Two consequences, used by anything that runs a program -/

/-- **Preservation, along a whole reduction sequence.** -/
theorem preservation_mstep {Tm Ty : Type} [LawfulTypeSystem Tm Ty]
    {Γ : Context Ty} {t t' : Tm} {τ : Ty} (h : Γ ⊢ t : τ) (hs : t ⟶* t') : Γ ⊢ t' : τ := by
  induction hs with
  | refl => exact h
  | tail _ s ih => exact LawfulTypeSystem.Preservation ih s

/-- **`eval` depends only on the term** — proof irrelevance on the derivation argument. -/
theorem eval_congr {Tm Ty : Type} [HasEval Tm Ty]
    {Γ : Context Ty} {t u : Tm} {τ : Ty} (hu : t = u) (h : Γ ⊢ t : τ) (h' : Γ ⊢ u : τ) :
    HasEval.eval Γ t τ h = HasEval.eval Γ u τ h' := by
  subst hu; rfl

/-- **`eval` is the identity on normal forms** — its answer is reachable, and nothing is
reachable from a term that does not step. -/
theorem eval_of_normalForm {Tm Ty : Type} [LawfulHasEval Tm Ty]
    {Γ : Context Ty} {t : Tm} {τ : Ty} (h : Γ ⊢ t : τ) (hn : NormalForm t) :
    HasEval.eval Γ t τ h = t := by
  rcases RTC.cases_head (LawfulHasEval.evalReachable h) with heq | ⟨c, hc, _⟩
  · exact heq.symm
  · exact absurd hc (hn c)

/-! ## The diamonds, pinned

As in the named file, and for its reason: they cost nothing and fail loudly the day a parent is
added or reordered. Do not delete them. -/

/-- One `TypeSystem` in `LawfulMVars`. -/
example {Tm Ty : Type} (L : LawfulMVars Tm Ty) :
    L.toMVars.toTypeSystem = L.toLawfulTypeSystem.toTypeSystem := rfl

/-- One `TypeSystem` in `LawfulHasEval`, reached by two different routes. -/
example {Tm Ty : Type} (L : LawfulHasEval Tm Ty) :
    L.toHasEval.toLawfulMVars.toTypeSystem = L.toConfluent.toTypeSystem := rfl

/-- One `LawfulMVars` in `Runnable` — all three parents reach it, and all three must reach the
same one. -/
example {Tm Ty : Type} (R : Runnable Tm Ty) :
    R.toPrincipalElaborate.toLawfulMVars = R.toLawfulHasEval.toHasEval.toLawfulMVars := rfl

example {Tm Ty : Type} (R : Runnable Tm Ty) :
    R.toPrincipalElaborate.toLawfulMVars = R.toHasTermSubst.toLawfulMVars := rfl

end LambdaLab.TypeSystem.DeBruijn
