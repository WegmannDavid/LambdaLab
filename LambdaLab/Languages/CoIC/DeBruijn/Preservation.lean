import LambdaLab.Languages.CoIC.DeBruijn.Inversion

/-!
# CoC — subject reduction, and uniqueness of types

**Subject reduction** (`HasType.preservation`): in a valid context, a reduct of a well-typed term
has the same type. By induction on the derivation, inverting the step:

* a step inside a domain or annotation changes a context entry, and the head of a context may be
  converted (`HasType.ctx_conv`);
* a step inside an argument changes the result type `B[0 := u]` to a convertible one, which is
  well-sorted by correctness of types;
* a β-step `(λ A₀ . b) u ⟶ b[0 := u]` is where the work is: the abstraction's type `Π A₀ . B₀`
  is convertible to the `Π A . B` it was used at, so by **Π-injectivity** (`Conv.pi_inj`) its
  argument may be taken at `A₀` and its body's type `B₀[0 := u]` converted to `B[0 := u]`.

**Uniqueness of types** (`HasType.unique`): two types of one term are convertible — by induction
on the term, through the generation lemmas.

Together they pin `□` down: nothing well-typed reduces to it (`HasType.not_red_box`), so no
well-typed term is even convertible to it (`HasType.not_conv_box`).
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

/-- The result type of an application is well-sorted. -/
theorem HasType.inst_sorted {Γ : Ctx} {t u A B : Tm} (ht : HasType Γ t (.pi A B))
    (hu : HasType Γ u A) (hΓ : Wf Γ) : ∃ s, HasType Γ (B.inst u) (.sort s) := by
  rcases ht.correct hΓ with h | ⟨s, hs⟩
  · cases h
  · obtain ⟨_, s₂, _, hB, _⟩ := hs.gen_pi
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
          exact .conv (.lam (ihA hΓ h') (ht.ctx_conv hA hc) (hB.ctx_conv hA hc)) (.pi hA hB)
            (Conv.pi hc.symm (Conv.refl _))
      | lamB h' => exact .lam hA (iht (hΓ.cons hA) h') hB
  | app ht hu iht ihu =>
      intro hΓ _ hs
      obtain ⟨s, hBu⟩ := ht.inst_sorted hu hΓ
      cases hs with
      | appL h' => exact .app (iht hΓ h') hu
      | appR h' =>
          exact .conv (.app ht (ihu hΓ h')) hBu (Conv.inst (Conv.refl _) (Conv.ofStep h').symm)
      | beta =>
          obtain ⟨B₀, s₁, _, hA₀, hb, _, hc⟩ := ht.gen_lam
          obtain ⟨hAA, hBB⟩ := Conv.pi_inj hc
          exact .conv ((hb.inst (.conv hu hA₀ hAA.symm))) hBu (Conv.inst hBB (Conv.refl _))
  | conv _ hB hc iht _ => intro hΓ _ hs; exact .conv (iht hΓ hs) hB hc

/-- Subject reduction along many steps. -/
theorem HasType.preservation_red {Γ : Ctx} {t t' T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hr : Red t t') : HasType Γ t' T := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.preservation hΓ hs

/-- **Uniqueness of types**: two types of one term are convertible. -/
theorem HasType.unique : ∀ {Γ : Ctx} {t T₁ T₂ : Tm}, HasType Γ t T₁ → HasType Γ t T₂ → Conv T₁ T₂
  | _, .sort _, _, _, h₁, h₂ => (h₁.gen_sort.2.symm).trans h₂.gen_sort.2
  | _, .var _, _, _, h₁, h₂ => by
      obtain ⟨A₁, hA₁, c₁⟩ := h₁.gen_var
      obtain ⟨A₂, hA₂, c₂⟩ := h₂.gen_var
      rw [hA₁] at hA₂
      cases hA₂
      exact c₁.symm.trans c₂
  | _, .pi _ _, _, _, h₁, h₂ => by
      obtain ⟨_, _, _, hB₁, c₁⟩ := h₁.gen_pi
      obtain ⟨_, _, _, hB₂, c₂⟩ := h₂.gen_pi
      exact c₁.symm.trans ((HasType.unique hB₁ hB₂).trans c₂)
  | _, .lam _ _, _, _, h₁, h₂ => by
      obtain ⟨_, _, _, _, ht₁, _, c₁⟩ := h₁.gen_lam
      obtain ⟨_, _, _, _, ht₂, _, c₂⟩ := h₂.gen_lam
      exact c₁.symm.trans ((Conv.pi (Conv.refl _) (HasType.unique ht₁ ht₂)).trans c₂)
  | _, .app _ _, _, _, h₁, h₂ => by
      obtain ⟨_, _, ht₁, _, c₁⟩ := h₁.gen_app
      obtain ⟨_, _, ht₂, _, c₂⟩ := h₂.gen_app
      obtain ⟨_, hB⟩ := Conv.pi_inj (HasType.unique ht₁ ht₂)
      exact c₁.symm.trans ((Conv.inst hB (Conv.refl _)).trans c₂)

/-! ## Nothing well-typed is `□` -/

/-- No well-typed term reduces to `□`. -/
theorem HasType.not_red_box {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hr : Red t (.sort .box)) : False :=
  (h.preservation_red hΓ hr).ne_box rfl

/-- **No well-typed term is convertible to `□`.** -/
theorem HasType.not_conv_box {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hc : Conv t (.sort .box)) : False :=
  h.not_red_box hΓ hc.to_sort

/-- So a conversion never reaches `□` from a well-sorted type: a term typed by `□` is typed so
without conversion. -/
theorem HasType.conv_box_eq {Γ : Ctx} {A : Tm} {s : Srt} (hA : HasType Γ A (.sort s)) (hΓ : Wf Γ)
    (hc : Conv (.sort .box) A) : False :=
  hA.not_conv_box hΓ hc.symm

end LambdaLab.Languages.CoIC.DeBruijn
