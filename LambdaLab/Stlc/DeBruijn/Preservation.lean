import LambdaLab.Stlc.DeBruijn.Typing
import LambdaLab.Stlc.DeBruijn.Step

/-!
# Preservation

Subject reduction for full beta: `Γ ⊢ e : τ` and `e ⟶ e'` ⇒ `Γ ⊢ e' : τ`.

Built up via:
1. `Lookup.weaken` / `HasType.weaken` — inserting a binding shifts terms.
2. Lookup helpers covering the three positions of `Δ ++ τ' :: Γ`.
3. `HasType.subst_lemma` — substituting a well-typed value preserves typing.
4. `HasType.preservation` — induction on the step.
-/

namespace LambdaLab.Stlc.DeBruijn

/-! ## Weakening -/

theorem Lookup.weaken {Γ : Ctx} {τ' : Ty} :
    ∀ (Δ : Ctx) {n τ},
    Lookup (Δ ++ Γ) n τ →
    Lookup (Δ ++ τ' :: Γ) (if n < Δ.length then n else n + 1) τ := by
  intro Δ
  induction Δ with
  | nil => intro n τ h; grind [Lookup.there]
  | cons σ Δ ih =>
      intro n τ h
      cases h with
      | here => grind [Lookup.here]
      | there h' => have ih' := ih h'; grind [Lookup.there]

theorem HasType.weaken {Γ : Ctx} {τ' : Ty} :
    ∀ {e τ} (Δ : Ctx),
    HasType (Δ ++ Γ) e τ → HasType (Δ ++ τ' :: Γ) (e.shift Δ.length) τ := by
  intro e
  induction e with
  | var n =>
      intro τ Δ h
      cases h with
      | var hl =>
          have hw := Lookup.weaken (τ' := τ') Δ hl
          grind [Term.shift, HasType.var]
  | lam σ body ih =>
      intro τ Δ h
      cases h with
      | lam hb =>
          simp only [Term.shift]
          apply HasType.lam
          have := ih (σ :: Δ) hb
          simp only [List.length_cons] at this
          exact this
  | app e₁ e₂ ih₁ ih₂ =>
      intro τ Δ h
      cases h with
      | app hf ha =>
          simp only [Term.shift]
          exact .app (ih₁ Δ hf) (ih₂ Δ ha)

/-! ## Lookup behaviour at a substitution position -/

theorem Lookup.eq_middle {Γ : Ctx} {τ' τ : Ty} :
    ∀ (Δ : Ctx), Lookup (Δ ++ τ' :: Γ) Δ.length τ → τ = τ' := by
  intro Δ
  induction Δ with
  | nil => intro h; grind [Lookup]
  | cons σ Δ ih => intro h; cases h with | there h' => exact ih h'

theorem Lookup.shrink_lt {Γ : Ctx} {τ' : Ty} :
    ∀ (Δ : Ctx) {n τ}, n < Δ.length →
    Lookup (Δ ++ τ' :: Γ) n τ → Lookup (Δ ++ Γ) n τ := by
  intro Δ
  induction Δ with
  | nil => intro n τ h _; simp at h
  | cons σ Δ ih =>
      intro n τ hlt h
      cases h with
      | here => exact .here
      | there h' =>
          rename_i m
          exact .there (ih (Nat.lt_of_succ_lt_succ hlt) h')

theorem Lookup.shrink_gt {Γ : Ctx} {τ' : Ty} :
    ∀ (Δ : Ctx) {n τ}, n > Δ.length →
    Lookup (Δ ++ τ' :: Γ) n τ → Lookup (Δ ++ Γ) (n - 1) τ := by
  intro Δ
  induction Δ with
  | nil => intro n τ hgt h; cases h <;> grind
  | cons σ Δ ih =>
      intro n τ hgt h
      cases h with
      | here => omega
      | there h' =>
          rename_i m
          have hmgt : m > Δ.length := Nat.lt_of_succ_lt_succ hgt
          have ih' := ih hmgt h'
          show Lookup (σ :: Δ ++ Γ) (m + 1 - 1) τ
          have heq : m + 1 - 1 = (m - 1) + 1 := by omega
          rw [heq]
          exact .there ih'

/-! ## Substitution lemma -/

theorem HasType.subst_lemma {Γ : Ctx} {τ' : Ty} :
    ∀ {e τ v} (Δ : Ctx),
    HasType (Δ ++ τ' :: Γ) e τ →
    HasType (Δ ++ Γ) v τ' →
    HasType (Δ ++ Γ) (e.subst Δ.length v) τ := by
  intro e
  induction e with
  | var m =>
      intro τ v Δ he hv
      cases he with
      | var hl =>
          grind [Term.subst, Lookup.eq_middle, Lookup.shrink_gt, Lookup.shrink_lt, HasType.var]
  | lam σ body ih =>
      intro τ v Δ he hv
      cases he with
      | lam hb =>
          simp only [Term.subst]
          apply HasType.lam
          have hv' : HasType (σ :: (Δ ++ Γ)) (v.shift 0) τ' := by
            have := HasType.weaken (Γ := Δ ++ Γ) (τ' := σ) [] hv
            simpa using this
          have := ih (σ :: Δ) hb hv'
          simp only [List.length_cons] at this
          exact this
  | app e₁ e₂ ih₁ ih₂ =>
      intro τ v Δ he hv
      cases he with
      | app hf ha =>
          simp only [Term.subst]
          exact .app (ih₁ Δ hf hv) (ih₂ Δ ha hv)

/-! ## Preservation -/

theorem HasType.preservation :
    HasType Γ e τ → e ⟶ e' → HasType Γ e' τ := by
  intro he hs
  induction hs generalizing Γ τ with
  | beta =>
      cases he with
      | app hf ha =>
          cases hf with
          | lam hb =>
              have := HasType.subst_lemma (Δ := []) hb ha
              simpa using this
  | lam _ ih =>
      cases he with
      | lam hb => exact .lam (ih hb)
  | appL _ ih =>
      cases he with
      | app hf ha => exact .app (ih hf) ha
  | appR _ ih =>
      cases he with
      | app hf ha => exact .app hf (ih ha)

end LambdaLab.Stlc.DeBruijn
