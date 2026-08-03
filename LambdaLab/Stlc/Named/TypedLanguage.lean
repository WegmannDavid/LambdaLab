import LambdaLab.TypedLanguage.Basic
import LambdaLab.Stlc.Named.Typing.Preservation
import LambdaLab.Stlc.Named.Typing.Normalization

/-!
# STLC as a `TypeSystem`

The named STLC plugged into `TypedLanguage.TypeSystem`, exactly as `Pipeline.lean` plugs it into
`Pipeline.Language`. Every field is an existing declaration under its own name; there is nothing
to prove here, which is the point — the interface asks for what the development already has.

## Why `N := String`

Not a design choice: `Step` is declared at `Term String`, so reduction — and therefore subject
reduction — exists only there, while `Term`, `Ctx` and `HasType` are parametric in `N`. The
witness is pinned wherever the narrowest field is. Generalizing `Step` (and the translation it
leans on, which builds a de Bruijn context from a `List String` of binders) would let this become
a family `∀ N, TypeSystem`.

## What is deliberately not here

`HasType.sn` — strong normalization — holds for this system and is *not* a `TypeSystem` field.
That asymmetry is intentional and is argued in `TypedLanguage/Basic.lean`: a field no instance can
discharge is a field that stops instances from existing, and preservation is the one property
general enough to demand of everything. It is recorded below as a plain theorem instead, so the
fact that STLC exceeds the interface is visible rather than lost.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.TypedLanguage

/-- **The named STLC as a `TypeSystem`.**

Building this value *is* the claim that STLC is well-behaved in the framework's sense: the
`Preservation` field cannot be filled without a subject-reduction proof, and `HasType.preservation`
supplies it unconditionally. -/
def stlcSystem : TypeSystem where
  N := String
  Tm := Term String
  Ty := LambdaLab.Stlc.Named.Ty
  HasType := HasType
  Step := Step
  Preservation := HasType.preservation

/-! ## The fields are definitionally what they came from

Each of these is `rfl`. They are stated so that a later change to `TypeSystem` — reordering
fields, wrapping a component, adding a parameter — fails here, at the plug-in, rather than
silently rebinding one of STLC's notions to something else. -/

@[simp] theorem stlcSystem_N : stlcSystem.N = String := rfl
@[simp] theorem stlcSystem_Tm : stlcSystem.Tm = Term String := rfl
@[simp] theorem stlcSystem_Ty : stlcSystem.Ty = Ty := rfl
@[simp] theorem stlcSystem_HasType : stlcSystem.HasType = @HasType String _ := rfl
@[simp] theorem stlcSystem_Step : stlcSystem.Step = Step := rfl

/-! ## Beyond the interface

STLC satisfies strictly more than `TypeSystem` asks. Recorded here, next to the instance, so the
gap between the two is documented where someone comparing them will look. -/

/-- STLC is strongly normalizing — a property `TypeSystem` does not require. -/
theorem stlcSystem_sn {Γ : Ctx String} {e : Term String} {τ : Ty} :
    stlcSystem.HasType Γ e τ → SN e :=
  HasType.sn

end LambdaLab.Stlc.Named
