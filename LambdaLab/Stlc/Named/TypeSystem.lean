import LambdaLab.TypeSystem.Basic
import LambdaLab.Stlc.Named.Typing.Preservation
import LambdaLab.Stlc.Named.Typing.Normalization
import LambdaLab.Stlc.Named.Typing.Unification

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
  needs the fresh-name generator. That pins `TypeSystem`, `LawfulTypeSystem` and `MVars` at
  `N := String` too — not a choice, just the narrowest field showing through.
* `MVars` needs no new work at all: `HasSubst (Term N) Ty` and `HasSubst Ty Ty` already exist, so
  both fields are `inferInstance` and the bundled copies are definitionally the canonical ones,
  which is what `MVars`' own docstring asks for.

## `DecideableElaborate` is deliberately absent

It cannot be filled today, and sorrying it would be worse than leaving it out. Its `elaborate`
returns `MGUProp`, whose two constructors are exactly the two open problems in this development:

* `mgu` needs the most-generality conjunct — `Target.elaborate`'s single `sorry`;
* `impossible` needs *completeness*, a proof that no substitution types the term. The existing
  elaborator returns `Option` and answers `none` on failure, which is the weaker claim "I found
  nothing", not "there is nothing".

So the honest report is that STLC satisfies the metatheory half of the interface unconditionally
and the algorithmic half not yet. `Target.elaborate` is the thing to promote once those close.
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

/-! ## The fields are definitionally what they came from

Each is `rfl`. They are stated so that a later change to the interface — reordering fields,
wrapping a component, adding a parameter — fails here, at the plug-in, rather than silently
rebinding one of STLC's notions to something else. -/

@[simp] theorem hasType_eq {N : Type} [NameAlphabet N] :
    TypeSystem.HasType.HasType (N := N) (Tm := Term N) (Ty := Ty) = HasType := rfl

@[simp] theorem step_eq : TypeSystem.Step.Step (Tm := Term String) = Step := rfl

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
