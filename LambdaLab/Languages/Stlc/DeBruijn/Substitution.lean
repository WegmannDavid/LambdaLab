import LambdaLab.Stlc.DeBruijn.Basic

/-!
# de Bruijn substitution algebra

Commutation lemmas for `Term.shift` and `Term.subst`. These are pure
calculations on terms; no typing or reduction relations involved.
-/

namespace LambdaLab.Stlc.DeBruijn

theorem Term.shift_shift_swap :
    ∀ (e : Term) {c₁ c₂ : Nat}, c₁ ≤ c₂ →
    (e.shift c₁).shift (c₂ + 1) = (e.shift c₂).shift c₁ := by
  intro e
  induction e with
  | var n =>
      intro c₁ c₂ hle
      grind [Term.shift]
  | lam τ body ih =>
      intro c₁ c₂ hle
      simp only [Term.shift]
      congr 1
      exact ih (Nat.succ_le_succ hle)
  | app e₁ e₂ ih₁ ih₂ =>
      intro c₁ c₂ hle
      simp only [Term.shift]
      rw [ih₁ hle, ih₂ hle]

-- (e.subst k v).shift c = (e.shift (c+1)).subst k (v.shift c) when k ≤ c
theorem Term.shift_subst_ge :
    ∀ (e : Term) {k c : Nat} (v : Term), k ≤ c →
    (e.subst k v).shift c = (e.shift (c+1)).subst k (v.shift c) := by
  intro e
  induction e with
  | var n =>
      intro k c v hle
      grind [Term.shift, Term.subst]
  | lam τ body ih =>
      intro k c v hle
      simp only [Term.subst, Term.shift]
      congr 1
      have ih' := ih (v := v.shift 0) (k := k+1) (c := c+1) (by omega)
      rw [Term.shift_shift_swap v (Nat.zero_le c)] at ih'
      exact ih'
  | app e₁ e₂ ih₁ ih₂ =>
      intro k c v hle
      simp only [Term.subst, Term.shift]
      rw [ih₁ v hle, ih₂ v hle]

-- (e.subst k v).shift c = (e.shift c).subst (k+1) (v.shift c) when c ≤ k
theorem Term.shift_subst_le :
    ∀ (e : Term) {k c : Nat} (v : Term), c ≤ k →
    (e.subst k v).shift c = (e.shift c).subst (k+1) (v.shift c) := by
  intro e
  induction e with
  | var n =>
      intro k c v hle
      grind [Term.shift, Term.subst]
  | lam τ body ih =>
      intro k c v hle
      simp only [Term.subst, Term.shift]
      congr 1
      have ih' := ih (v := v.shift 0) (k := k+1) (c := c+1) (by omega)
      rw [Term.shift_shift_swap v (Nat.zero_le c)] at ih'
      exact ih'
  | app e₁ e₂ ih₁ ih₂ =>
      intro k c v hle
      simp only [Term.subst, Term.shift]
      rw [ih₁ v hle, ih₂ v hle]

-- (e.shift c).subst c x = e (shifting then substituting at the same cutoff cancels)
theorem Term.shift_subst_cancel : ∀ (e : Term) (c : Nat) (x : Term),
    (e.shift c).subst c x = e := by
  intro e
  induction e with
  | var n =>
      intro c x
      grind [Term.shift, Term.subst]
  | lam τ body ih =>
      intro c x
      simp only [Term.shift, Term.subst]
      congr 1
      exact ih (c+1) (x.shift 0)
  | app e₁ e₂ ih₁ ih₂ =>
      intro c x
      simp only [Term.shift, Term.subst]
      rw [ih₁, ih₂]

-- Substitution composition: (e.subst i a).subst j v = (e.subst (j+1) (v.shift i)).subst i (a.subst j v)
theorem Term.subst_subst_distrib :
    ∀ (e : Term) {i j : Nat} (a v : Term), i ≤ j →
    (e.subst i a).subst j v = (e.subst (j+1) (v.shift i)).subst i (a.subst j v) := by
  intro e
  induction e with
  | var n =>
      intro i j a v hle
      grind [Term.shift, Term.subst, Term.shift_subst_cancel]
  | lam τ body ih =>
      intro i j a v hle
      simp only [Term.subst]
      congr 1
      have ih' := ih (a := a.shift 0) (v := v.shift 0) (i := i+1) (j := j+1) (by omega)
      rw [Term.shift_shift_swap v (Nat.zero_le i)] at ih'
      rw [← Term.shift_subst_le a v (Nat.zero_le j)] at ih'
      exact ih'
  | app e₁ e₂ ih₁ ih₂ =>
      intro i j a v hle
      simp only [Term.subst]
      rw [ih₁ a v hle, ih₂ a v hle]

end LambdaLab.Stlc.DeBruijn
