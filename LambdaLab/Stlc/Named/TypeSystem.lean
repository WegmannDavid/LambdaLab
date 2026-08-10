import LambdaLab.TypeSystem.Basic
import LambdaLab.Stlc.Named.Typing.Preservation
import LambdaLab.Stlc.Named.Typing.Normalization
import LambdaLab.Stlc.Named.Typing.Unification
import LambdaLab.Stlc.Named.Typing.JComplete

/-!
# STLC against the `TypeSystem` interface

The named STLC plugged into the classes of `TypeSystem/Basic.lean`, as `Pipeline.lean` plugs it
into `Pipeline.Language`. Every field is an existing declaration under its own name; nothing is
proved here, which is the point — the interface asks for what the development already has.

## Where each instance can live

The classes split by how much of `N` they need, and the instances land at different generality
because of it:

* `HasType` is **generic in `N`**. The typing judgement never inspects a name beyond equality and
  context lookup, so `Term N` is typeable for any name alphabet.
* `Step` is **`String`-only**, and so is everything above it. `Stlc.Named.Step` is declared at
  `Term String`, because the reduction relation goes through capture-avoiding substitution, which
  needs the fresh-name generator. That pins `TypeSystem`, `LawfulTypeSystem`, `MVars` and
  `LawfulMVars` at `N := String` too — not a choice, just the narrowest field showing through.
* `MVars` needs no new work at all: `HasSubst (Term N) Ty` and `HasSubst Ty Ty` already exist, so
  both fields are `inferInstance` and the bundled copies are definitionally the canonical ones,
  which is what `MVars`' own docstring asks for.
* `LawfulMVars` is discharged by `HasType.subst`, which was proved generic in `N` long before the
  interface asked for it. Both laws the interface demands — subject reduction and stability under
  substitution — were already theorems here; neither needed a line of new proof.

* `DecideableElaborate` is discharged by `elabSolution`, whose two branches are `elabSubst_sound`
  and `no_typing_of_elabSubst_none`. The second is the one that took work: `none` has to mean
  *there is no typing*, not *this algorithm found none*.

## `PrincipalElaborate` is deliberately absent

The one class still unfilled, and it cannot be filled today. Its single field asks that the
returned substitution be at least as general as every other typing substitution — the open
conjunct in `Target.elaborate`, and the same wall `W_principal` hits from the other side.

`DecideableElaborate` used to carry that demand too, in an `MGUProp`-valued field, which is why
this file once reported the whole algorithmic half as missing. It was not: deciding typeability
and finding a *principal* solution are separate claims, and only the second is open. Splitting the
class along that line — the same split `LawfulTypeSystem` makes against `TypeSystem` — is what let
the decision be recorded as soon as it was proved instead of waiting on principality.

So the honest report is now: STLC satisfies the metatheory half of the interface unconditionally,
decides elaboration unconditionally, and does not yet claim principality.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.TypeSystem (NameAlphabet)

/-! ## The judgement — any name alphabet -/

/-- Typing is parametric in the name alphabet: nothing in the judgement inspects a name. -/
instance instHasType {N : Type} [NameAlphabet N] : TypeSystem.HasType N (Term N) Ty where
  HasType := HasType

/-! ## Reduction and above — pinned at `String` -/

/-- `Stlc.Named.Step` is declared at `Term String`, so this and everything extending it is too. -/
instance instStep : TypeSystem.Step (Term String) where
  Step := Step

instance instTypeSystem : TypeSystem.TypeSystem String (Term String) Ty := {}

/-- The metatheory field, discharged by the unconditional subject-reduction theorem. This is the
one instance with content: building it *is* the claim that STLC is well-behaved in the framework's
sense, since `Preservation` cannot be filled without a proof. -/
instance instLawfulTypeSystem : TypeSystem.LawfulTypeSystem String (Term String) Ty where
  Preservation := HasType.preservation

/-- Both substitution instances already exist, so fill from them rather than defining new ones —
the copies are then definitionally canonical and lemmas about either apply to both. -/
instance instMVars : TypeSystem.MVars String (Term String) Ty where
  tmSubst := inferInstance
  tySubst := inferInstance

/-- The second instance with content: stability of typing under substitution, discharged by
`HasType.subst`. Like `Preservation` this is a field, so it cannot be skipped — and like it, the
proof already existed, generic in `N`, before the interface asked for it. -/
instance instLawfulMVars : TypeSystem.LawfulMVars String (Term String) Ty where
  Stability σ h := HasType.subst h σ

/-- The third instance with content, and the first that is algorithmic rather than metatheoretic:
elaboration *decides* typeability. `elabSolution` bundles `elabSubst_sound` with
`no_typing_of_elabSubst_none`, so both halves are discharged by existing theorems — the `none`
branch is a proof that nothing types the triple, not a report that nothing was found.

Generic in `N` like the judgement, but declared at `String` to sit under `LawfulMVars`. -/
instance instDecideableElaborate : TypeSystem.DecideableElaborate String (Term String) Ty where
  elaborate := elabSolution

/-! ## The fields are definitionally what they came from

Each is `rfl`. They are stated so that a later change to the interface — reordering fields,
wrapping a component, adding a parameter — fails here, at the plug-in, rather than silently
rebinding one of STLC's notions to something else. -/

@[simp] theorem hasType_eq {N : Type} [NameAlphabet N] :
    TypeSystem.HasType.HasType (N := N) (Tm := Term N) (Ty := Ty) = HasType := rfl

@[simp] theorem step_eq : TypeSystem.Step.Step (Tm := Term String) = Step := rfl

@[simp] theorem elaborate_eq :
    TypeSystem.DecideableElaborate.elaborate (N := String) (Tm := Term String) (Ty := Ty)
      = elabSolution := rfl

/-! ## Beyond the interface

STLC satisfies strictly more than `LawfulTypeSystem` asks. Recorded next to the instance so the
gap is documented where someone comparing the two will look — `TypeSystem/Basic.lean` argues at
length for keeping normalization *out* of the interface, and that argument reads better with the
thing it excludes in view. -/

/-- STLC is strongly normalizing — a property the interface does not require. -/
theorem sn_of_hasType {Γ : Ctx String} {e : Term String} {τ : Ty} :
    TypeSystem.HasType.HasType Γ e τ → SN e :=
  HasType.sn

end LambdaLab.Stlc.Named
