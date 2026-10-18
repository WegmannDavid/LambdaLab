import LambdaLab.Languages.ECC.DeBruijn.Inversion

/-!
# ECC — subject reduction

**Subject reduction** (`HasType.preservation`): in a valid context, a reduct of a well-typed term
has the same type. By induction on the derivation, inverting the step:

* a step inside a domain or annotation changes a context entry, and the head of a context may be
  converted (`HasType.ctx_conv`);
* a step inside an argument changes the result type `B[0 := u]` to a convertible one, which is
  well-sorted by correctness of types;
* a β-step `(λ A₀ . b) u ⟶ b[0 := u]` is where the work is: the abstraction's type `Π A₀ . B₀`
  is a subtype of the `Π A . B` it was used at, so by **Π-inversion** (`Sub.pi_inv`) the domains
  are convertible — its argument may be taken at `A₀` — and `B₀[0 := u] ≼ B[0 := u]`.

Types are no longer unique up to conversion — `Prop` has type `Type 0` and also `Type 1` — but a
well-typed term has a least type, which the checker computes (`Check.lean`).
-/

namespace LambdaLab.Languages.ECC.DeBruijn

/-- The result type of an application is well-sorted. -/
theorem HasType.inst_sorted {Γ : Ctx} {t u A B : Tm} (ht : HasType Γ t (.pi A B))
    (hu : HasType Γ u A) (hΓ : Wf Γ) : ∃ s, HasType Γ (B.inst u) (.sort s) := by
  obtain ⟨s, hs⟩ := ht.correct hΓ
  obtain ⟨_, s₂, _, hB, _⟩ := hs.gen_pi
  exact ⟨s₂, hB.inst hu⟩

/-- **Subject reduction.** -/
theorem HasType.preservation {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) :
    Wf Γ → ∀ {t' : Tm}, Step t t' → HasType Γ t' T := by
  induction h with
  | sort => intro _ _ hs; cases hs
  | var => intro _ _ hs; cases hs
  | pi hA hB ihA ihB =>
      intro hΓ _ hs
      cases hs with
      | piA h' => exact .pi (ihA hΓ h') (hB.ctx_conv hA (Conv.ofStep h'))
      | piB h' => exact .pi hA (ihB (hΓ.cons hA) h')
  | lam hA ht hB ihA iht _ =>
      intro hΓ _ hs
      cases hs with
      | lamA h' =>
          have hc := Conv.ofStep h'
          exact .cumul (.lam (ihA hΓ h') (ht.ctx_conv hA hc) (hB.ctx_conv hA hc)) (.pi hA hB)
            (Conv.pi hc.symm (Conv.refl _)).toSub
      | lamB h' => exact .lam hA (iht (hΓ.cons hA) h') hB
  | app ht hu iht ihu =>
      intro hΓ _ hs
      obtain ⟨s, hBu⟩ := ht.inst_sorted hu hΓ
      cases hs with
      | appL h' => exact .app (iht hΓ h') hu
      | appR h' =>
          exact .cumul (.app ht (ihu hΓ h')) hBu
            (Conv.inst (Conv.refl _) (Conv.ofStep h').symm).toSub
      | beta =>
          obtain ⟨B₀, s₁, _, hA₀, hb, _, hc⟩ := ht.gen_lam
          obtain ⟨hAA, hBB⟩ := Sub.pi_inv hc
          exact .cumul (hb.inst (.cumul hu hA₀ hAA.symm.toSub)) hBu (hBB.subst _)
  | cumul _ hB hc iht _ => intro hΓ _ hs; exact .cumul (iht hΓ hs) hB hc

/-- Subject reduction along many steps. -/
theorem HasType.preservation_red {Γ : Ctx} {t t' T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hr : Red t t') : HasType Γ t' T := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.preservation hΓ hs

end LambdaLab.Languages.ECC.DeBruijn
