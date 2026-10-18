import LambdaLab.Languages.ECC.DeBruijn.Typing

/-!
# ECC — inverting the typing rules

A derivation of `Γ ⊢ t : T` ends in the rule for `t`'s shape followed by any number of
cumulativity steps, so reading the premises back off it gives them **up to subtyping of the type**
(`HasType.gen_lam`, …). Each is an induction on the derivation, the cumulativity case being
`Sub.trans`.

Unlike CoC there is no top sort — every universe has a universe above it — so **every type is
itself typed by a sort** (`HasType.correct`, correctness of types), with no exception; it needs a
valid context, because a variable's type is read off it.
-/

namespace LambdaLab.Languages.ECC.DeBruijn

/-! ## Generation -/

theorem HasType.gen_sort {Γ : Ctx} {s : Srt} {T : Tm} (h : HasType Γ (.sort s) T) :
    Sub (.sort s.succ) T := by
  generalize hx : Tm.sort s = x at h
  induction h with
  | sort => cases hx; exact Sub.refl _
  | cumul _ _ hc ih _ => exact (ih hx).trans hc
  | _ => cases hx

theorem HasType.gen_var {Γ : Ctx} {n : Nat} {T : Tm} (h : HasType Γ (.var n) T) :
    ∃ A, Γ.lookup n = some A ∧ Sub A T := by
  generalize hx : Tm.var n = x at h
  induction h with
  | var hn => cases hx; exact ⟨_, hn, Sub.refl _⟩
  | cumul _ _ hc ih _ =>
      obtain ⟨A, hA, h'⟩ := ih hx
      exact ⟨A, hA, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_pi {Γ : Ctx} {A B T : Tm} (h : HasType Γ (.pi A B) T) :
    ∃ s₁ s₂, HasType Γ A (.sort s₁) ∧ HasType (A :: Γ) B (.sort s₂) ∧
      Sub (.sort (s₁.pi s₂)) T := by
  generalize hx : Tm.pi A B = x at h
  induction h with
  | pi hA hB => cases hx; exact ⟨_, _, hA, hB, Sub.refl _⟩
  | cumul _ _ hc ih _ =>
      obtain ⟨s₁, s₂, hA, hB, h'⟩ := ih hx
      exact ⟨s₁, s₂, hA, hB, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_lam {Γ : Ctx} {A t T : Tm} (h : HasType Γ (.lam A t) T) :
    ∃ B s₁ s₂, HasType Γ A (.sort s₁) ∧ HasType (A :: Γ) t B ∧ HasType (A :: Γ) B (.sort s₂) ∧
      Sub (.pi A B) T := by
  generalize hx : Tm.lam A t = x at h
  induction h with
  | lam hA ht hB => cases hx; exact ⟨_, _, _, hA, ht, hB, Sub.refl _⟩
  | cumul _ _ hc ih _ =>
      obtain ⟨B, s₁, s₂, hA, ht, hB, h'⟩ := ih hx
      exact ⟨B, s₁, s₂, hA, ht, hB, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_app {Γ : Ctx} {t u T : Tm} (h : HasType Γ (.app t u) T) :
    ∃ A B, HasType Γ t (.pi A B) ∧ HasType Γ u A ∧ Sub (B.inst u) T := by
  generalize hx : Tm.app t u = x at h
  induction h with
  | app ht hu => cases hx; exact ⟨_, _, ht, hu, Sub.refl _⟩
  | cumul _ _ hc ih _ =>
      obtain ⟨A, B, ht, hu, h'⟩ := ih hx
      exact ⟨A, B, ht, hu, h'.trans hc⟩
  | _ => cases hx

/-! ## Correctness of types -/

/-- **Every type is typed by a sort.** -/
theorem HasType.correct {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ) :
    ∃ s, HasType Γ T (.sort s) := by
  induction h with
  | sort => exact ⟨_, .sort⟩
  | var hn => exact hΓ.lookup hn
  | pi => exact ⟨_, .sort⟩
  | lam hA _ hB _ _ _ => exact ⟨_, .pi hA hB⟩
  | @app _ t u A B _ hu iht _ =>
      obtain ⟨s, hs⟩ := iht hΓ
      obtain ⟨_, s₂, _, hB, _⟩ := hs.gen_pi
      exact ⟨s₂, hB.inst hu⟩
  | cumul _ hB _ _ _ => exact ⟨_, hB⟩

end LambdaLab.Languages.ECC.DeBruijn
