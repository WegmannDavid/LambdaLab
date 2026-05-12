import LambdaLab.Stlc.Named.Typing
import LambdaLab.Stlc.Named.Unification
import LambdaLab.Stlc.Named.Properties
import LambdaLab.Language.Basic

/-!
# Verified type inference

`Term.infer Γ e` returns either a `TypeError` or a type `τ` *together with*
a derivation `Γ ⊢ e : τ`. Because every `lam` carries its annotation,
well-typed terms have a unique type, so inference and checking coincide —
no bidirectional split, no unification.

The kernel checker uses `σ = ∅` in the `CheckResult.ok` payload: ground
terms have no metavariables, so the empty substitution suffices. A
`HasType.pSubst_empty` bridge lets us package the existing kernel
derivation into the new `(σ-pSubst-everything) HasType` shape.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Language (ElaborateResult TypeError)

/-- Apply the empty substitution everywhere — vacuous, but needed to
match the `CheckResult.ok` constructor's expected shape. -/
theorem HasType.pSubst_empty {Γ : Ctx} {e : Term} {τ : Ty}
    (h : HasType Γ e τ) :
    HasType (HasSubst.pSubst Γ (∅ : Subst Ty))
            (HasSubst.pSubst e (∅ : Subst Ty))
            (HasSubst.pSubst τ (∅ : Subst Ty)) := by
  show HasType _ (Term.tyPSubst e ∅) (Signature.pSubst τ ∅)
  rw [Term.tyPSubst_empty, Signature.pSubst_empty]
  exact HasType.cong (fun x => (HashMap.pSubst_empty_get? Γ x).symm) h

/-- Bare-bones inference returning either a `TypeError` or the raw
`HasType` derivation. Kept as a separate function so the algorithm
stays simple; the public `Term.infer` wraps the result into a
`CheckResult` with `σ = ∅`. -/
def Term.inferRaw (Γ : Ctx) :
    (e : Term) → TypeError Ty ⊕ (Σ' τ, HasType Γ e τ)
  | .var x =>
      match h : Γ.get? x with
      | none   => .inl (.unbound x)
      | some τ => .inr ⟨τ, .var h⟩
  | .lam x τ₁ body =>
      match Term.inferRaw (Γ.cons x τ₁) body with
      | .inl err     => .inl err
      | .inr ⟨τ₂, h⟩ => .inr ⟨τ₁ ⇒ τ₂, .lam h⟩
  | .app e₁ e₂ =>
      match Term.inferRaw Γ e₁ with
      | .inl err              => .inl err
      | .inr ⟨.base, _⟩       => .inl (.notArrow .base)
      | .inr ⟨.mvar n, _⟩     => .inl (.notArrow (.mvar n))
      | .inr ⟨(τ₁ ⇒ τ₂), hf⟩  =>
          match Term.inferRaw Γ e₂ with
          | .inl err     => .inl err
          | .inr ⟨τa, ha⟩ =>
              if h : τa = τ₁ then
                .inr ⟨τ₂, .app hf (h ▸ ha)⟩
              else
                .inl (.mismatch τ₁ τa)

def Term.infer (Γ : Ctx) (e : Term) : ElaborateResult HasType Γ e :=
  match Term.inferRaw Γ e with
  | .inl err     => .error err
  | .inr ⟨τ, h⟩  =>
      .ok τ ∅ (HasType.pSubst_empty h)
        (fun σ' _ => ⟨σ', fun t => by
          show HasSubst.pSubst t σ' = HasSubst.pSubst (Signature.pSubst t ∅) σ'
          rw [Signature.pSubst_empty]⟩)

/-- Closed-term entry point: infer in the empty context. -/
def Term.inferClosed (e : Term) : ElaborateResult HasType Ctx.empty e :=
  e.infer Ctx.empty

end LambdaLab.Stlc.Named
