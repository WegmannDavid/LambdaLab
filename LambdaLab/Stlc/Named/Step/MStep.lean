import LambdaLab.Stlc.Named.Step.Basic
import LambdaLab.Relation.Closure

/-!
# Multi-step reduction (named)

Reflexive-transitive closure of `Step`, with congruence rules for
lambda and application — same shape as the de Bruijn `MStep`, and, like it,
the shared `RTC` rather than a bespoke inductive. See
`LambdaLab/Stlc/DeBruijn/MStep.lean` for the note on `head` vs `tail`.
-/

namespace LambdaLab.Stlc.Named

variable {N : Type} [LambdaLab.Nominal.NameAlphabet N]

/-- Multi-step (full-beta) reduction: the reflexive-transitive closure of `Step`. -/
abbrev MStep {N : Type} [LambdaLab.Nominal.NameAlphabet N] : Term N → Term N → Prop :=
  RTC Step

theorem MStep.lift {e e' : Term N} : e ⟶ e' → e ⟶* e' := RTC.single

theorem MStep.lam {e e' : Term N} {x : N} {τ : Ty} :
    MStep e e' → MStep (.lam x τ e) (.lam x τ e') := by
  intro h
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (Step.lam s)

theorem MStep.appL {e₁ e₁' e₂ : Term N} : MStep e₁ e₁' → MStep (.app e₁ e₂) (.app e₁' e₂) := by
  intro h
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (Step.appL s)

theorem MStep.appR {e₁ e₂ e₂' : Term N} : MStep e₂ e₂' → MStep (.app e₁ e₂) (.app e₁ e₂') := by
  intro h
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (Step.appR s)

theorem MStep.app {e₁ e₁' e₂ e₂' : Term N} (h₁ : MStep e₁ e₁') (h₂ : MStep e₂ e₂') :
    MStep (.app e₁ e₂) (.app e₁' e₂') :=
  (MStep.appL h₁).trans (MStep.appR h₂)

end LambdaLab.Stlc.Named
