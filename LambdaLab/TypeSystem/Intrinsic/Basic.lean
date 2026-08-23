import LambdaLab.Relation.Normalization

/-!
# An intrinsically-typed alternative to `TypeSystem/Named/`

Terms are indexed by their context and type — `Tm : Con → Ty → Type` — rather than being a bare
type with a judgement `HasType : Context → Tm → Ty → Prop` beside them. Ill-typed terms are not
merely unprovable, they are unwritable.

That moves two things out of the interface. **Preservation is free**: `Step` relates `Tm Γ τ` to
`Tm Γ τ`, so a reduct has the type of its redex by construction and there is nothing to demand.
And a normalization or confluence field needs **no typing hypothesis**: every inhabitant of
`Tm Γ τ` is well typed, so a claim about all of them is already restricted to the ones the
extrinsic version had to guard with `Γ ⊢ t : τ`.

Experimental, and nothing depends on it yet — but it is a real module (`LambdaLab.TypeSystem.
Intrinsic.Basic`), imported by the root so that `lake build` typechecks it and it cannot rot.
-/

namespace LambdaLab.TypeSystem.Intrinsic

class TypeSystem (Con Ty : Type) (Tm : Con → Ty → Type) where
  Step : {Γ : Con} → {τ : Ty} → Tm Γ τ → Tm Γ τ → Prop

class StronglyNormalizing Con Ty Tm extends TypeSystem Con Ty Tm where
  /-- **Every term is strongly normalizing.** Unconditional, and that is the intrinsic version's
  dividend: extrinsically the field has to read `Γ ⊢ t : τ → SN (· ⟶ ·) t`, because `Tm` there also
  holds the divergent terms no judgement accepts (`Stlc.Named.omega_not_sn` refutes the
  unconditional form). Here `Tm Γ τ` holds only well-typed terms, so `Ω` cannot be written and the
  quantifier can range over the whole type.

  `SN` is `LambdaLab.SN` from `Relation/Normalization.lean`, at `Step` for this `Γ` and `τ`: the
  relation stays inside one indexed family, so no reduct escapes the type it is stated at. -/
  StronglyNormalizing : ∀ {Γ : Con} {τ : Ty} (t : Tm Γ τ), SN Step t

class HasEval Con Ty Tm extends TypeSystem Con Ty Tm where
  eval : (Tm Γ τ) → (Tm Γ τ) → Prop

end LambdaLab.TypeSystem.Intrinsic
