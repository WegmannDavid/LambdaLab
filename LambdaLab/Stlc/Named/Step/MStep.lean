import LambdaLab.Stlc.Named.Step

/-!
# Multi-step reduction (named)

Reflexive-transitive closure of `Step`, with congruence rules for
lambda and application — same shape as the de Bruijn `MStep`.
-/

namespace LambdaLab.Stlc.Named

inductive MStep : Term → Term → Prop where
  | refl : MStep e e
  | head : e ⟶ e' → MStep e' e'' → MStep e e''

infix:50 " ⟶* " => MStep

theorem MStep.lift : e ⟶ e' → e ⟶* e' :=
  fun s => .head s .refl

theorem MStep.trans : MStep e e' → MStep e' e'' → MStep e e''
  | .refl, h => h
  | .head s rest, h => .head s (rest.trans h)

theorem MStep.lam : MStep e e' → MStep (.lam x τ e) (.lam x τ e')
  | .refl => .refl
  | .head s rest => .head (Step.lam s) (MStep.lam rest)

theorem MStep.appL : MStep e₁ e₁' → MStep (.app e₁ e₂) (.app e₁' e₂)
  | .refl => .refl
  | .head s rest => .head (Step.appL s) (MStep.appL rest)

theorem MStep.appR : MStep e₂ e₂' → MStep (.app e₁ e₂) (.app e₁ e₂')
  | .refl => .refl
  | .head s rest => .head (Step.appR s) (MStep.appR rest)

theorem MStep.app (h₁ : MStep e₁ e₁') (h₂ : MStep e₂ e₂') :
    MStep (.app e₁ e₂) (.app e₁' e₂') :=
  (MStep.appL h₁).trans (MStep.appR h₂)

end LambdaLab.Stlc.Named
