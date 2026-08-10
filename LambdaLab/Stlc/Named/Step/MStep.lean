import LambdaLab.Stlc.Named.Step.Basic

/-!
# Multi-step reduction (named)

Reflexive-transitive closure of `Step`, with congruence rules for
lambda and application — same shape as the de Bruijn `MStep`.
-/

namespace LambdaLab.Stlc.Named

variable {N : Type} [LambdaLab.TypeSystem.NameAlphabet N]

inductive MStep {N : Type} [LambdaLab.TypeSystem.NameAlphabet N] : Term N → Term N → Prop where
  | refl {e : Term N} : MStep e e
  | head {e e' e'' : Term N} : e ⟶ e' → MStep e' e'' → MStep e e''

infix:50 " ⟶* " => MStep

theorem MStep.lift {e e' : Term N} : e ⟶ e' → e ⟶* e' :=
  fun s => .head s .refl

theorem MStep.trans {e e' e'' : Term N} : MStep e e' → MStep e' e'' → MStep e e''
  | .refl, h => h
  | .head s rest, h => .head s (rest.trans h)

theorem MStep.lam {e e' : Term N} {x : N} {τ : Ty} :
    MStep e e' → MStep (.lam x τ e) (.lam x τ e')
  | .refl => .refl
  | .head s rest => .head (Step.lam s) (MStep.lam rest)

theorem MStep.appL {e₁ e₁' e₂ : Term N} : MStep e₁ e₁' → MStep (.app e₁ e₂) (.app e₁' e₂)
  | .refl => .refl
  | .head s rest => .head (Step.appL s) (MStep.appL rest)

theorem MStep.appR {e₁ e₂ e₂' : Term N} : MStep e₂ e₂' → MStep (.app e₁ e₂) (.app e₁ e₂')
  | .refl => .refl
  | .head s rest => .head (Step.appR s) (MStep.appR rest)

theorem MStep.app {e₁ e₁' e₂ e₂' : Term N} (h₁ : MStep e₁ e₁') (h₂ : MStep e₂ e₂') :
    MStep (.app e₁ e₂) (.app e₁' e₂') :=
  (MStep.appL h₁).trans (MStep.appR h₂)

end LambdaLab.Stlc.Named
