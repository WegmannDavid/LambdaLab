import LambdaLab.Stlc.DeBruijn.Step.Basic
import LambdaLab.Stlc.DeBruijn.Step.MStep
import LambdaLab.Stlc.DeBruijn.Substitution

/-!
# Confluence (Church-Rosser) via parallel reduction

Proof outline (Tait-Martin-Löf, Takahashi):
1. Parallel reduction `PStep` allows reducing multiple redexes simultaneously.
2. A complete-development `Term.dev` reduces every redex in a term once.
3. Triangle: every parallel reduct `e ⇉ e'` satisfies `e' ⇉ e.dev`.
4. Diamond for `PStep` is then immediate.
5. Confluence of multi-step reduction follows by a strip lemma.
-/

namespace LambdaLab.Stlc.DeBruijn

/-! ## Parallel reduction -/

inductive PStep : Term → Term → Prop where
  | var  : PStep (.var n) (.var n)
  | lam  : PStep e e' → PStep (.lam τ e) (.lam τ e')
  | app  : PStep e₁ e₁' → PStep e₂ e₂' →
           PStep (.app e₁ e₂) (.app e₁' e₂')
  | beta : PStep e₁ e₁' → PStep e₂ e₂' →
           PStep (.app (.lam τ e₁) e₂) (e₁'.subst 0 e₂')

infix:50 " ⇉ " => PStep

theorem PStep.refl : ∀ e : Term, e ⇉ e
  | .var _     => .var
  | .lam _ e   => .lam (PStep.refl e)
  | .app e₁ e₂ => .app (PStep.refl e₁) (PStep.refl e₂)

theorem Step.toPStep : e ⟶ e' → e ⇉ e'
  | .beta   => .beta (PStep.refl _) (PStep.refl _)
  | .lam s  => .lam s.toPStep
  | .appL s => .app s.toPStep (PStep.refl _)
  | .appR s => .app (PStep.refl _) s.toPStep

/-! ## Parallel reduction respects shifting and substitution -/

theorem PStep.shift : ∀ {e e' : Term}, e ⇉ e' → ∀ c, e.shift c ⇉ e'.shift c := by
  intro e e' h
  induction h with
  | var =>
      intro c
      grind [Term.shift, PStep.var]
  | lam _ ih =>
      intro c
      simp only [Term.shift]
      exact .lam (ih (c+1))
  | app _ _ ih₁ ih₂ =>
      intro c
      simp only [Term.shift]
      exact .app (ih₁ c) (ih₂ c)
  | @beta e₁ e₁' e₂ e₂' τ _ _ ih₁ ih₂ =>
      intro c
      simp only [Term.shift]
      have hb : (Term.app (.lam τ (e₁.shift (c+1))) (e₂.shift c)) ⇉
                ((e₁'.shift (c+1)).subst 0 (e₂'.shift c)) :=
        PStep.beta (ih₁ (c+1)) (ih₂ c)
      have heq : (e₁'.shift (c+1)).subst 0 (e₂'.shift c) = (e₁'.subst 0 e₂').shift c :=
        (Term.shift_subst_ge e₁' e₂' (Nat.zero_le c)).symm
      rw [heq] at hb
      exact hb

theorem PStep.subst : ∀ {e e' v v' : Term},
    e ⇉ e' → v ⇉ v' → ∀ k, e.subst k v ⇉ e'.subst k v' := by
  intro e e' v v' he hv
  induction he generalizing v v' with
  | @var n =>
      intro k
      grind [Term.subst, PStep.var]
  | @lam e₀ e₀' τ _ ih =>
      intro k
      simp only [Term.subst]
      exact .lam (ih (hv.shift 0) (k+1))
  | @app _ _ _ _ _ _ ih₁ ih₂ =>
      intro k
      simp only [Term.subst]
      exact .app (ih₁ hv k) (ih₂ hv k)
  | @beta e₁ e₁' e₂ e₂' τ _ _ ih₁ ih₂ =>
      intro k
      simp only [Term.subst]
      have hb : (Term.app (.lam τ (e₁.subst (k+1) (v.shift 0))) (e₂.subst k v)) ⇉
                ((e₁'.subst (k+1) (v'.shift 0)).subst 0 (e₂'.subst k v')) :=
        PStep.beta (ih₁ (hv.shift 0) (k+1)) (ih₂ hv k)
      rw [Term.subst_subst_distrib e₁' e₂' v' (Nat.zero_le k)]
      exact hb

theorem PStep.toMStep : ∀ {e e' : Term}, e ⇉ e' → e ⟶* e' := by
  intro e e' h
  induction h with
  | var => exact .refl
  | lam _ ih => exact MStep.lam ih
  | app _ _ ih₁ ih₂ => exact MStep.app ih₁ ih₂
  | @beta e₁ e₁' e₂ e₂' τ _ _ ih₁ ih₂ =>
      have m1 : MStep (Term.app (.lam τ e₁) e₂) (Term.app (.lam τ e₁') e₂) :=
        MStep.appL (MStep.lam ih₁)
      have m2 : MStep (Term.app (.lam τ e₁') e₂) (Term.app (.lam τ e₁') e₂') :=
        MStep.appR ih₂
      have m3 : MStep (Term.app (.lam τ e₁') e₂') (e₁'.subst 0 e₂') :=
        MStep.lift Step.beta
      exact (m1.trans m2).trans m3

/-! ## Takahashi's complete development -/

def Term.dev : Term → Term
  | .var n => .var n
  | .lam τ e => .lam τ e.dev
  | .app (.lam _ e₁) e₂ => e₁.dev.subst 0 e₂.dev
  | .app e₁ e₂ => .app e₁.dev e₂.dev

/-- Triangle lemma: every parallel reduct of `e` parallel-reduces to `e.dev`. -/
theorem PStep.triangle : ∀ {e e' : Term}, e ⇉ e' → e' ⇉ e.dev := by
  intro e e' h
  induction h with
  | var => exact PStep.var
  | lam _ ih =>
      simp only [Term.dev]
      exact .lam ih
  | @app e₁ e₁' e₂ e₂' h₁ _ ih₁ ih₂ =>
      cases h₁ with
      | var =>
          simp only [Term.dev]
          exact .app .var ih₂
      | lam hb =>
          simp only [Term.dev] at ih₁ ⊢
          cases ih₁ with
          | lam hbd => exact PStep.beta hbd ih₂
      | app _ _ =>
          simp only [Term.dev]
          exact .app ih₁ ih₂
      | beta _ _ =>
          simp only [Term.dev]
          exact .app ih₁ ih₂
  | beta _ _ ih₁ ih₂ =>
      simp only [Term.dev]
      exact PStep.subst ih₁ ih₂ 0

/-! ## Diamond and confluence -/

theorem PStep.diamond : ∀ {e e₁ e₂}, e ⇉ e₁ → e ⇉ e₂ → ∃ e', e₁ ⇉ e' ∧ e₂ ⇉ e' := by
  intro e e₁ e₂ h₁ h₂
  exact ⟨e.dev, h₁.triangle, h₂.triangle⟩

/-- Strip lemma: a single parallel step lifts past a multi-step. -/
theorem MStep.strip : ∀ {e e₁ e₂},
    e ⇉ e₁ → e ⟶* e₂ → ∃ e', e₁ ⟶* e' ∧ e₂ ⇉ e' := by
  intro e e₁ e₂ hp hm
  induction hm using RTC.head_induction_on generalizing e₁ with
  | refl => exact ⟨e₁, .refl, hp⟩
  | head s rest ih =>
      have hp' := s.toPStep
      have ⟨e_d, h_e1d, h_emd⟩ := hp.diamond hp'
      have ⟨e_f, h_de_f, h_e2e_f⟩ := ih h_emd
      exact ⟨e_f, h_e1d.toMStep.trans h_de_f, h_e2e_f⟩

/-- Confluence (Church-Rosser) of full-beta reduction. -/
theorem MStep.confluent : ∀ {e e₁ e₂ : Term},
    e ⟶* e₁ → e ⟶* e₂ → ∃ e', e₁ ⟶* e' ∧ e₂ ⟶* e' := by
  intro e e₁ e₂ h₁ h₂
  induction h₁ using RTC.head_induction_on generalizing e₂ with
  | refl => exact ⟨e₂, h₂, .refl⟩
  | head s rest ih =>
      have hp := s.toPStep
      have ⟨e_d, h_emd, h_e2d⟩ := MStep.strip hp h₂
      have ⟨e', h_e1e', h_de'⟩ := ih h_emd
      exact ⟨e', h_e1e', h_e2d.toMStep.trans h_de'⟩

end LambdaLab.Stlc.DeBruijn
