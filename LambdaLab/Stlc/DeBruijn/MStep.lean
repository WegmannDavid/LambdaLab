import LambdaLab.Stlc.DeBruijn.Step
import LambdaLab.Relation.Basic

/-!
# Multi-step reduction

Reflexive-transitive closure of `Step`, with congruence rules for
lambda and application.

`MStep` is `RTC Step` — the shared closure from `LambdaLab/Relation/Basic.lean`, not a
bespoke inductive. Its constructors are `refl`/`tail` (snoc-shaped); the head-shaped view
this development is written against comes from `RTC.head` and, for proofs that genuinely
consume a reduction from the front, `RTC.head_induction_on`. The congruence lemmas below
need neither: they map over the chain in either orientation, so they go by the default
`tail` recursion.
-/

namespace LambdaLab.Stlc.DeBruijn

/-- Multi-step (full-beta) reduction: the reflexive-transitive closure of `Step`. -/
abbrev MStep : Term → Term → Prop := RTC Step

infix:50 " ⟶* " => MStep

theorem MStep.lift : e ⟶ e' → e ⟶* e' := RTC.single

theorem MStep.lam : MStep e e' → MStep (.lam τ e) (.lam τ e') := by
  intro h
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (Step.lam s)

theorem MStep.appL : MStep e₁ e₁' → MStep (.app e₁ e₂) (.app e₁' e₂) := by
  intro h
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (Step.appL s)

theorem MStep.appR : MStep e₂ e₂' → MStep (.app e₁ e₂) (.app e₁ e₂') := by
  intro h
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (Step.appR s)

theorem MStep.app (h₁ : MStep e₁ e₁') (h₂ : MStep e₂ e₂') :
    MStep (.app e₁ e₂) (.app e₁' e₂') :=
  (MStep.appL h₁).trans (MStep.appR h₂)

end LambdaLab.Stlc.DeBruijn
