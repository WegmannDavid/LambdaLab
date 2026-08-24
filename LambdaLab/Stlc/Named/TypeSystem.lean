import LambdaLab.TypeSystem.Named.Basic
import LambdaLab.Stlc.Named.Typing.Preservation
import LambdaLab.Stlc.Named.Typing.Normalization
import LambdaLab.Stlc.Named.Typing.Unification
import LambdaLab.Stlc.Named.Typing.JComplete
import LambdaLab.TypeSystem.Named.Vernacular.Elaborate

/-!
# STLC against the `TypeSystem` interface

The named STLC plugged into the classes of `TypeSystem/Named/Basic.lean`, as `Pipeline.lean` plugs it
into `Pipeline.Language`. Every field is an existing declaration under its own name; nothing is
proved here, which is the point — the interface asks for what the development already has.

## Every instance is generic in `N`

* `HasType` is **generic in `N`**. The typing judgement never inspects a name beyond equality and
  context lookup, so `Term N` is typeable for any atoms.
* `Step` is generic too — and this was not always so. It was declared at `Term String`, and that
  pinned `TypeSystem`, `LawfulTypeSystem`, `MVars` and `LawfulMVars` at `String` with it. The pin
  was never necessary: the β-rule's capture-avoiding substitution draws fresh names from
  `Atom.freshFor`, which every `Atom` instance has, and the de Bruijn translation carrying
  subject reduction only ever compares names. Generalising `Step`, `MStep`, `Translation` and
  `HasType.preservation` changed signatures and **not one proof**.
  That matters practically, not just aesthetically: `Pipeline.lean` names terms by `VName`, so
  with the instances pinned at `String` it could not use this interface at all and had to call
  `Target.elabSubst` directly. Now it goes through `PrincipalElaborate`.
* `MVars` needs no new work at all: `HasSubst Nat (Term N) Ty` and `HasSubst Nat Ty Ty` already exist, so
  both fields are `inferInstance` and the bundled copies are definitionally the canonical ones,
  which is what `MVars`' own docstring asks for.
* `LawfulMVars` is discharged by `HasType.subst`, which was proved generic in `N` long before the
  interface asked for it. Both laws the interface demands — subject reduction and stability under
  substitution — were already theorems here; neither needed a line of new proof.

* `PrincipalElaborate` is discharged by `elabMGU`. Its negative branch is
  `no_typing_of_elabSubst_none`, the one that took work: `none` has to mean *there is no typing*,
  not *this algorithm found none*. Its positive branch pairs `elabSubst_sound` with
  `elabSubst_principal_below`.

## Most-generality, and the shape it takes

`elaborate` returns a `PrincipalProp`, so filling it demands most-generality as well as the
decision. It is discharged by `Typing/JComplete.lean`'s **`elabSubst_principal_below`, a theorem** —
principality *on the source*, which is what the claim can be: the elaborator draws metavariables of
its own, and `Typing/Principality.lean` proves the unrestricted `MoreGeneral` form false for this
very elaborator. The threshold is `sourceSupp`, the same one `elabSubst` prunes to, handed to the
class through its own field.

Nothing in this file is claimed on credit any more, and nothing downstream reports `sorryAx`.

So the honest report is: STLC satisfies the metatheory unconditionally, decides elaboration
unconditionally (`elabSolution` is proved and still exported), and claims principality on credit.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Nominal (Atom)

/-! ## The judgement — any atoms

`instHasType` is not here: it lives beside the inductive in `Typing/Basic.lean`, so that the `⊢`
notation the class owns is available from the judgement's own file onwards. -/

/-! ## Reduction and above — every atoms instance too

`Step` was declared at `Term String` and everything above it inherited the pin. It did not have
to be: `Term.subst` is capture-avoiding via `Atom.freshFor`, which every `Atom` instance
supplies, and the de Bruijn translation that carries subject reduction only ever compares names.
Generalising `Step`, `MStep`, `Translation` and `HasType.preservation` to an arbitrary `N` cost no
proof changes at all — only signatures — and it is what lets `Pipeline.lean` reach these instances
at its own name type `VName` instead of calling the elaborator directly.

`[HasVars Nat N]` appears from `LawfulTypeSystem` on: preservation needs it (through
`HasType.freeVars_in_ctx`), and the substitution the classes above it talk about is defined by it.
-/

variable {N : Type} [Atom N]

instance instTypeSystem : TypeSystem.Named.TypeSystem N (Term N) Ty := {}

/-- The metatheory field, discharged by the unconditional subject-reduction theorem. This is the
one instance with content: building it *is* the claim that STLC is well-behaved in the framework's
sense, since `Preservation` cannot be filled without a proof. -/
instance instLawfulTypeSystem : TypeSystem.Named.LawfulTypeSystem N (Term N) Ty where
  Preservation := HasType.preservation
  cong h ht := HasType.cong h ht

/-- Both substitution instances already exist, so fill from them rather than defining new ones —
the copies are then definitionally canonical and lemmas about either apply to both. -/
instance instMVars : TypeSystem.Named.MVars N (Term N) Ty where
  tmSubst := inferInstance
  tySubst := inferInstance

/-- The second instance with content: stability of typing under substitution, discharged by
`HasType.subst`. Like `Preservation` this is a field, so it cannot be skipped — and like it, the
proof already existed, generic in `N`, before the interface asked for it. -/
instance instLawfulMVars : TypeSystem.Named.LawfulMVars N (Term N) Ty where
  Stability σ h := HasType.subst h σ
  tyGroundStable := inferInstance
  tmGroundStable := inferInstance
  tyLawfulComp := inferInstance
  tmLawfulComp := inferInstance
  tyLawfulRestrict := inferInstance
  tmLawfulRestrict := inferInstance

/-! ## Groundness, decided

`PrincipalElaborate` asks for these, and they are the reason it does: `HasVars.Ground` quantifies
over every index, so no instance decides it by unfolding. Both were here long before the interface
wanted them. Declared ahead of the instance that consumes them. -/

/-- Groundness of a type, by the structural check — `Ty.ground_iff` routes it to `Ty.isGround`. -/
instance : DecidablePred (HasVars.Ground : Ty → Prop) :=
  fun _ => decidable_of_iff _ Ty.ground_iff

/-- The same for terms, via `Term.AnnotsGround`. -/
instance : DecidablePred (HasVars.Ground : Term N → Prop) :=
  fun _ => decidable_of_iff _ Term.annotsGround_iff_ground

/-- The third instance with content, and the first that is algorithmic rather than metatheoretic.
`elabMGU`'s negative branch is `no_typing_of_elabSubst_none` — a proof that nothing types the
triple, not a report that nothing was found — and its positive branch is `elabSubst_sound` paired
with `elabSubst_principal_below`. Both are theorems, so this instance is discharged in full.

`sourceSupp` is `Target.sourceSupp`, the threshold `elabSubst` prunes its answer to; the
principality the class asks for is stated below it, which is the only place it can hold
(`Typing/Principality.lean`). The plain decision remains available on its own as `elabSolution`. -/
instance instPrincipalElaborate : TypeSystem.Named.PrincipalElaborate N (Term N) Ty where
  sourceSupp := sourceSupp
  elaborate := elabMGU
  tyGroundDec := inferInstance
  tmGroundDec := inferInstance

/-! ## Normalization — `String` only, and only this one of the reduction classes

`StronglyNormalizing` is discharged; `Confluent` and `HasEval`/`LawfulHasEval` are not, and the
reasons differ:

* **`Confluent` is not available for this variant at all.** `Named.MStep.confluent` does not claim
  joint convergence on named terms and says so: two reduction paths pick different fresh binder
  names, so they converge only up to α-equivalence, and the theorem states convergence *after*
  translation to de Bruijn. The class asks for a common reduct in `Tm` itself. De Bruijn has that
  unconditionally (`Stlc.DeBruijn.MStep.confluent`) but cannot instantiate anything here — its
  context is a `List Ty`, not a `Context N Ty`. An instance needs α-equivalence on named terms, or
  a class stated up to a congruence.
* **`HasEval` is open by choice** — the evaluator exists (`Step/Eval.lean`, on `SNTerm`) but what
  it should be at the interface has not been settled. -/

/-- **Strong normalization**, pinned at `String` like everything that detours through de Bruijn
binder lists. The field is `HasType.sn` outright — `Named.SN` *is* `LambdaLab.SN` at this `Step`,
so there is nothing to convert.

The field could not ask for well-foundedness of `⟶`: `omega_not_sn` refutes that. -/
instance instStronglyNormalizing :
    TypeSystem.Named.StronglyNormalizing String (Term String) Ty where
  StronglyNormalizing h := HasType.sn h

/-! ## The fields are definitionally what they came from

Each is `rfl`. They are stated so that a later change to the interface — reordering fields,
wrapping a component, adding a parameter — fails here, at the plug-in, rather than silently
rebinding one of STLC's notions to something else. -/

@[simp] theorem hasType_eq :
    TypeSystem.Named.HasType.HasType (N := N) (Tm := Term N) (Ty := Ty) = HasType := rfl

@[simp] theorem step_eq : TypeSystem.Named.Step.Step (Tm := Term N) = Step := rfl

@[simp] theorem elaborate_eq :
    TypeSystem.Named.PrincipalElaborate.elaborate (N := N) (Tm := Term N) (Ty := Ty)
      = elabMGU := rfl

/-! ## Beyond the interface

STLC satisfies strictly more than `LawfulTypeSystem` asks. Recorded next to the instance so the
gap is documented where someone comparing the two will look — `TypeSystem/Named/Basic.lean` argues at
length for keeping normalization *out* of the interface, and that argument reads better with the
thing it excludes in view. -/

/-- STLC is strongly normalizing — a property the interface does not require. -/
theorem sn_of_hasType {Γ : Ctx String} {e : Term String} {τ : Ty} :
    Γ ⊢ e : τ → SN e :=
  HasType.sn

end LambdaLab.Stlc.Named
