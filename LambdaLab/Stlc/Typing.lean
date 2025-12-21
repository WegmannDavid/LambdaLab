import LambdaLab.Stlc.Tm
import LambdaLab.Stlc.Vernacular
import LambdaLab.Nominal.Context


inductive Typing : Context Ty → Tm → Ty → Prop where
| var :

  Contains Γ x α →
  ------------------------------------------
  Typing Γ (# x) α

| app :

  Typing Γ t (α ⟶ β) →
  Typing Γ s α →
  ---------------------
  Typing Γ (t ⬝ s) β

| abs :

  Typing (push Γ x α) t β →
  --------------------------------
  Typing Γ (ƛ x : α => t) (α ⟶ β)

notation:50 Γ "⊢" t ":" α => Typing Γ t α

open Subst Nominal

theorem Typing_subst {α : Ty} (σ : Substitution Nat Ty) : (Γ ⊢ t : α) → (subst σ Γ ⊢ subst σ t : subst σ α) := by
  intro H
  cases H with
  | var CΓcα  =>
    simp
    sorry
  | app Ht Hs =>
    simp; constructor
    . apply (Typing_subst _ Ht)
    . apply (Typing_subst _ Hs)
  | abs Ht    =>
    simp; constructor
    rw[<-push_subst]
    apply (Typing_subst _ Ht)

inductive TypingVernacular : Context Ty → Vernacular → Prop where
| eof :

  ---------------------
  TypingVernacular Γ []

| dec :

  fresh Γ = 0 →
  fresh α = 0 →
  (Γ ⊢ t : α) →
  TypingVernacular (push Γ x α) ds →
  ------------------------------------
  TypingVernacular Γ (⟨ x, α, t ⟩::ds)
