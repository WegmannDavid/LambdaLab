import LambdaLab.Stlc.Named.Typing.Basic
import LambdaLab.Stlc.Named.Typing.Unification

/-!
# Generic properties of named-variable typing

These are utilities about `HasType` that don't depend on reduction or
translation. They mirror similar facts on the de Bruijn side.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.TypeSystem (NameAlphabet)

variable {N : Type} [NameAlphabet N] [HasVars N]

/-- Two named contexts that agree on every key induce the same typing
judgements. -/
theorem HasType.cong : ∀ {Γ Γ' : Ctx N} {e τ},
    (∀ x, Γ.get? x = Γ'.get? x) → HasType Γ e τ → HasType Γ' e τ := by
  intro Γ Γ' e τ hcong h
  induction h generalizing Γ' with
  | var heq => exact HasType.var (by rw [← hcong]; exact heq)
  | lam _ ih =>
      apply HasType.lam
      apply ih
      intro y
      rw [Ctx.get?_cons, Ctx.get?_cons]
      split
      · rfl
      · exact hcong _
  | app _ _ ih₁ ih₂ => exact HasType.app (ih₁ hcong) (ih₂ hcong)

/-- Every free variable of a typed term is bound in the context. -/
theorem HasType.freeVars_in_ctx : ∀ (e : (Term N)) {Γ τ},
    HasType Γ e τ → ∀ x, x ∈ e.freeVars → ∃ σ, Γ.get? x = some σ := by
  intro e
  induction e with
  | var y =>
      intro Γ τ h x hx
      cases h with
      | var heq => simp [Term.freeVars] at hx; cases hx; exact ⟨τ, heq⟩
  | lam y σ body ih =>
      intro Γ τ h x hx
      cases h with
      | lam hb =>
          simp [Term.freeVars, List.mem_filter] at hx
          obtain ⟨hxb, hxy⟩ := hx
          have ⟨σ', heq⟩ := ih hb x hxb
          rw [Ctx.get?_cons] at heq
          split at heq
          · rename_i h_eq; exact absurd h_eq.symm hxy
          · exact ⟨σ', heq⟩
  | app e₁ e₂ ih₁ ih₂ =>
      intro Γ τ h x hx
      cases h with
      | app h₁ h₂ =>
          simp [Term.freeVars] at hx
          cases hx with
          | inl hh => exact ih₁ h₁ x hh
          | inr hh => exact ih₂ h₂ x hh

/-- A closed term has no free variables. -/
theorem HasType.closed_no_free {e : Term N} {τ} (h : HasType Ctx.empty e τ) :
    ∀ x, x ∉ e.freeVars := by
  intro x hx
  obtain ⟨τ', heq⟩ := HasType.freeVars_in_ctx e h x hx
  rw [Ctx.get?_empty] at heq
  cases heq

/-- Typing only depends on `Γ`'s value at the term's free variables. -/
theorem HasType.relevant : ∀ (e : (Term N)) {Γ Γ' : Ctx N} {τ},
    HasType Γ e τ → (∀ x ∈ e.freeVars, Γ.get? x = Γ'.get? x) → HasType Γ' e τ := by
  intro e
  induction e with
  | var y =>
      intro Γ Γ' τ h hag
      cases h with
      | var heq =>
          apply HasType.var
          rw [← hag y (by simp [Term.freeVars])]
          exact heq
  | lam y σ body ih =>
      intro Γ Γ' τ h hag
      cases h with
      | lam hb =>
          apply HasType.lam
          apply ih hb
          intro z hz
          rw [Ctx.get?_cons, Ctx.get?_cons]
          by_cases h_yz : y = z
          · simp [h_yz]
          · simp [h_yz]
            apply hag z
            simp [Term.freeVars, List.mem_filter]
            refine ⟨hz, ?_⟩
            intro h
            exact h_yz h.symm
  | app e₁ e₂ ih₁ ih₂ =>
      intro Γ Γ' τ h hag
      cases h with
      | app h₁ h₂ =>
          apply HasType.app
          · exact ih₁ h₁ (fun z hz => hag z (by simp [Term.freeVars]; exact Or.inl hz))
          · exact ih₂ h₂ (fun z hz => hag z (by simp [Term.freeVars]; exact Or.inr hz))

/-- A closed term is typed under any context. -/
theorem HasType.weaken_closed {v τ} (Γ : Ctx N) (hv : HasType Ctx.empty v τ) :
    HasType Γ v τ :=
  HasType.relevant v hv (fun x hx => absurd hx (HasType.closed_no_free hv x))

/-! ## Stability of `HasType` under type substitution. -/

/-- `cons` and `pSubst` commute under `get?` — substituting an extended
context agrees, key-by-key, with extending a substituted context. Used
via `HasType.cong` to bridge `pSubst (Γ.cons x τ) σ` and
`(pSubst Γ σ).cons x (pSubst τ σ)`. -/
theorem Ctx.pSubst_cons_get? (Γ : Ctx N) (σ : Subst Ty)
    (x : N) (τ : Ty) (y : N) :
    (HasSubst.pSubst (Γ.cons x τ) σ).get? y =
      ((HasSubst.pSubst Γ σ).cons x (HasSubst.pSubst τ σ)).get? y := by
  rw [HashMap.pSubst_get?, Ctx.get?_cons, Ctx.get?_cons]
  rw [HashMap.pSubst_get?]
  by_cases hxy : x = y
  · subst hxy; simp
  · simp [hxy]

/-- **Stability of `HasType` under type substitution.** Applying any
substitution to all three of context, term, and type preserves the
typing derivation. Proved by structural induction on the derivation. -/
theorem HasType.subst {Γ : Ctx N} {e : (Term N)} {τ : Ty}
    (h : HasType Γ e τ) (ρ : Subst Ty) :
    HasType (HasSubst.pSubst Γ ρ)
            (HasSubst.pSubst e ρ)
            (HasSubst.pSubst τ ρ) := by
  induction h with
  | var h_get =>
      apply HasType.var
      rw [HashMap.pSubst_get?, h_get]
      rfl
  | lam _ ih =>
      simp only [Ty.pSubst_arrow]
      apply HasType.lam
      apply HasType.cong _ ih
      intro y
      apply Ctx.pSubst_cons_get?
  | app _ _ ih₁ ih₂ =>
      rw [Ty.pSubst_arrow] at ih₁
      exact HasType.app ih₁ ih₂

/-! ## Inversion lemmas.

These let a `HasType` derivation be peeled apart by syntactic case
analysis on the term: each constructor of `Term` admits exactly one
shape of derivation. -/

theorem HasType.var_inv {Γ : Ctx N} {x : N} {τ : Ty}
    (h : HasType Γ (.var x) τ) : Γ.get? x = some τ := by
  cases h with | var h_get => exact h_get

theorem HasType.lam_inv {Γ : Ctx N} {x : N} {α : Ty} {body : (Term N)} {τ : Ty}
    (h : HasType Γ (.lam x α body) τ) :
    ∃ β : Ty, τ = (α ⇒ β) ∧ HasType (Γ.cons x α) body β := by
  cases h with | lam h_body => exact ⟨_, rfl, h_body⟩

theorem HasType.app_inv {Γ : Ctx N} {e₁ e₂ : (Term N)} {τ : Ty}
    (h : HasType Γ (.app e₁ e₂) τ) :
    ∃ α : Ty, HasType Γ e₁ (α ⇒ τ) ∧ HasType Γ e₂ α := by
  cases h with | app h₁ h₂ => exact ⟨_, h₁, h₂⟩

/-- **Types are unique.** One term has at most one type in a given context — the three rules are
syntax-directed and the binder carries its own annotation, so nothing is ever chosen. -/
theorem HasType.det {Γ : Ctx N} {e : Term N} {τ₁ τ₂ : Ty}
    (h₁ : HasType Γ e τ₁) (h₂ : HasType Γ e τ₂) : τ₁ = τ₂ := by
  induction h₁ generalizing τ₂ with
  | var hget => cases h₂ with | var hget₂ => rw [hget] at hget₂; exact Option.some.inj hget₂
  | lam _ ih => cases h₂ with | lam hb₂ => rw [ih hb₂]
  | app _ _ ih₁ _ => cases h₂ with | app hf₂ _ => injection ih₁ hf₂

end LambdaLab.Stlc.Named
