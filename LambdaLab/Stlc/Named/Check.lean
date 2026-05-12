import LambdaLab.Stlc.Named.Typing
import LambdaLab.Language.Basic

/-!
# Verified type inference

`Term.infer Γ e` returns either a `TypeError` or a type `τ` *together with*
a derivation `Γ ⊢ e : τ`. Because every `lam` carries its annotation,
well-typed terms have a unique type, so inference and checking coincide —
no bidirectional split, no unification.

The result is intrinsically sound: any `ok` branch carries its own proof.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Language (CheckResult TypeError)

def Term.infer (Γ : Ctx) : (e : Term) → CheckResult HasType Γ e
  | .var x =>
      match h : Γ.get? x with
      | none   => .error (.unbound x)
      | some τ => .ok τ (.var h)
  | .lam x τ₁ body =>
      match Term.infer (Γ.cons x τ₁) body with
      | .error err => .error err
      | .ok τ₂ h   => .ok (τ₁ ⇒ τ₂) (.lam h)
  | .app e₁ e₂ =>
      match Term.infer Γ e₁ with
      | .error err   => .error err
      | .ok .base _  => .error (.notArrow .base)
      | .ok .inf _   => .error (.notArrow .inf)
      | .ok (.mvar n) _ => .error (.notArrow (.mvar n))
      | .ok (τ₁ ⇒ τ₂) hf =>
          match Term.infer Γ e₂ with
          | .error err => .error err
          | .ok τa ha  =>
              if h : τa = τ₁ then
                .ok τ₂ (.app hf (h ▸ ha))
              else
                .error (.mismatch τ₁ τa)

/-- Closed-term entry point: infer in the empty context. -/
def Term.inferClosed (e : Term) : CheckResult HasType Ctx.empty e :=
  e.infer Ctx.empty

end LambdaLab.Stlc.Named
