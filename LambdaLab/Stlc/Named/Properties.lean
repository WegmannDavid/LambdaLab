import LambdaLab.Stlc.Named.Typing

/-!
# Generic properties of named-variable typing

These are utilities about `HasType` that don't depend on reduction or
translation. They mirror similar facts on the de Bruijn side.
-/

namespace LambdaLab.Stlc.Named

/-- Two named contexts that agree on every key induce the same typing
judgements. -/
theorem HasType.cong : ∀ {Γ Γ' : Ctx} {e τ},
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
theorem HasType.freeVars_in_ctx : ∀ (e : Term) {Γ τ},
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
theorem HasType.closed_no_free {e τ} (h : HasType Ctx.empty e τ) :
    ∀ x, x ∉ e.freeVars := by
  intro x hx
  obtain ⟨τ', heq⟩ := HasType.freeVars_in_ctx e h x hx
  rw [Ctx.get?_empty] at heq
  cases heq

/-- Typing only depends on `Γ`'s value at the term's free variables. -/
theorem HasType.relevant : ∀ (e : Term) {Γ Γ' : Ctx} {τ},
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
theorem HasType.weaken_closed {v τ} (Γ : Ctx) (hv : HasType Ctx.empty v τ) :
    HasType Γ v τ :=
  HasType.relevant v hv (fun x hx => absurd hx (HasType.closed_no_free hv x))

end LambdaLab.Stlc.Named
