import LambdaLab.Languages.CoC.DeBruijn.Typing

/-!
# CoC — inverting the typing rules

A derivation of `Γ ⊢ t : T` ends in the rule for `t`'s shape followed by any number of conversions,
so reading the premises back off it gives them **up to conversion of the type**
(`HasType.gen_lam`, …). Each is an induction on the derivation, the conversion case being
`Conv.trans`.

Two facts about `□` come out on the way: it has no type (`HasType.ne_box`), and every type that is
not `□` is itself typed by a sort (`HasType.correct` — *correctness of types*, which needs a valid
context because a variable's type is read off it).
-/

namespace LambdaLab.Languages.CoC.DeBruijn

/-- **`□` has no type.** -/
theorem HasType.ne_box {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) : t ≠ .sort .box := by
  induction h with
  | conv _ _ _ ih _ => exact ih
  | _ => exact nofun

/-! ## Generation -/

theorem HasType.gen_sort {Γ : Ctx} {s : Srt} {T : Tm} (h : HasType Γ (.sort s) T) :
    s = .star ∧ Conv (.sort .box) T := by
  generalize hx : Tm.sort s = x at h
  induction h with
  | sort => cases hx; exact ⟨rfl, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨hs, h'⟩ := ih hx
      exact ⟨hs, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_var {Γ : Ctx} {n : Nat} {T : Tm} (h : HasType Γ (.var n) T) :
    ∃ A, Γ.lookup n = some A ∧ Conv A T := by
  generalize hx : Tm.var n = x at h
  induction h with
  | var hn => cases hx; exact ⟨_, hn, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨A, hA, h'⟩ := ih hx
      exact ⟨A, hA, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_pi {Γ : Ctx} {A B T : Tm} (h : HasType Γ (.pi A B) T) :
    ∃ s₁ s₂, HasType Γ A (.sort s₁) ∧ HasType (A :: Γ) B (.sort s₂) ∧ Conv (.sort s₂) T := by
  generalize hx : Tm.pi A B = x at h
  induction h with
  | pi hA hB => cases hx; exact ⟨_, _, hA, hB, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨s₁, s₂, hA, hB, h'⟩ := ih hx
      exact ⟨s₁, s₂, hA, hB, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_lam {Γ : Ctx} {A t T : Tm} (h : HasType Γ (.lam A t) T) :
    ∃ B s₁ s₂, HasType Γ A (.sort s₁) ∧ HasType (A :: Γ) t B ∧ HasType (A :: Γ) B (.sort s₂) ∧
      Conv (.pi A B) T := by
  generalize hx : Tm.lam A t = x at h
  induction h with
  | lam hA ht hB => cases hx; exact ⟨_, _, _, hA, ht, hB, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨B, s₁, s₂, hA, ht, hB, h'⟩ := ih hx
      exact ⟨B, s₁, s₂, hA, ht, hB, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_app {Γ : Ctx} {t u T : Tm} (h : HasType Γ (.app t u) T) :
    ∃ A B, HasType Γ t (.pi A B) ∧ HasType Γ u A ∧ Conv (B.inst u) T := by
  generalize hx : Tm.app t u = x at h
  induction h with
  | app ht hu => cases hx; exact ⟨_, _, ht, hu, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨A, B, ht, hu, h'⟩ := ih hx
      exact ⟨A, B, ht, hu, h'.trans hc⟩
  | _ => cases hx

/-! ## Correctness of types -/

/-- **Every type is `□` or is itself typed by a sort.** -/
theorem HasType.correct {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ) :
    T = .sort .box ∨ ∃ s, HasType Γ T (.sort s) := by
  induction h with
  | sort => exact .inl rfl
  | var hn => exact .inr (hΓ.lookup hn)
  | @pi _ _ _ _ s₂ _ _ _ _ =>
      cases s₂ with
      | star => exact .inr ⟨_, .sort⟩
      | box => exact .inl rfl
  | lam hA _ hB _ _ _ => exact .inr ⟨_, .pi hA hB⟩
  | @app _ t u A B _ hu iht _ =>
      rcases iht hΓ with h | ⟨s, hs⟩
      · cases h
      · obtain ⟨_, s₂, _, hB, _⟩ := hs.gen_pi
        exact .inr ⟨s₂, hB.inst hu⟩
  | conv _ hB _ _ _ => exact .inr ⟨_, hB⟩

end LambdaLab.Languages.CoC.DeBruijn
