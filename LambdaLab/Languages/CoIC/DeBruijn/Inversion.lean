import LambdaLab.Languages.CoIC.DeBruijn.Typing

/-!
# CoC with inductive types — inverting the typing rules

A derivation of `Γ ⊢ t : T` ends in the rule for `t`'s shape followed by any number of conversions,
so reading the premises back off it gives them **up to conversion of the type**
(`HasType.gen_lam`, …). Each is an induction on the derivation, the conversion case being
`Conv.trans`.

Two facts about `□` come out on the way: it has no type (`HasType.ne_box`), and every type that is
not `□` is itself typed by a sort (`HasType.correct` — *correctness of types*, which needs a valid
context because a variable's type is read off it).
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

variable {sg : Sig}

/-- **`□` has no type.** -/
theorem HasType.ne_box {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) : t ≠ .sort .box := by
  induction h with
  | conv _ _ _ ih _ => exact ih
  | _ => exact nofun

/-! ## Generation -/

theorem HasType.gen_sort {Γ : Ctx} {s : Srt} {T : Tm} (h : HasType sg Γ (.sort s) T) :
    s = .star ∧ Conv (.sort .box) T := by
  generalize hx : Tm.sort s = x at h
  induction h with
  | sort => cases hx; exact ⟨rfl, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨hs, h'⟩ := ih hx
      exact ⟨hs, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_var {Γ : Ctx} {n : Nat} {T : Tm} (h : HasType sg Γ (.var n) T) :
    ∃ A, Γ.lookup n = some A ∧ Conv A T := by
  generalize hx : Tm.var n = x at h
  induction h with
  | var hn => cases hx; exact ⟨_, hn, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨A, hA, h'⟩ := ih hx
      exact ⟨A, hA, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_pi {Γ : Ctx} {A B T : Tm} (h : HasType sg Γ (.pi A B) T) :
    ∃ s₁ s₂, HasType sg Γ A (.sort s₁) ∧ HasType sg (A :: Γ) B (.sort s₂) ∧ Conv (.sort s₂) T := by
  generalize hx : Tm.pi A B = x at h
  induction h with
  | pi hA hB => cases hx; exact ⟨_, _, hA, hB, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨s₁, s₂, hA, hB, h'⟩ := ih hx
      exact ⟨s₁, s₂, hA, hB, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_lam {Γ : Ctx} {A t T : Tm} (h : HasType sg Γ (.lam A t) T) :
    ∃ B s₁ s₂, HasType sg Γ A (.sort s₁) ∧ HasType sg (A :: Γ) t B ∧
      HasType sg (A :: Γ) B (.sort s₂) ∧
      Conv (.pi A B) T := by
  generalize hx : Tm.lam A t = x at h
  induction h with
  | lam hA ht hB => cases hx; exact ⟨_, _, _, hA, ht, hB, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨B, s₁, s₂, hA, ht, hB, h'⟩ := ih hx
      exact ⟨B, s₁, s₂, hA, ht, hB, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_app {Γ : Ctx} {t u T : Tm} (h : HasType sg Γ (.app t u) T) :
    ∃ A B, HasType sg Γ t (.pi A B) ∧ HasType sg Γ u A ∧ Conv (B.inst u) T := by
  generalize hx : Tm.app t u = x at h
  induction h with
  | app ht hu => cases hx; exact ⟨_, _, ht, hu, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨A, B, ht, hu, h'⟩ := ih hx
      exact ⟨A, B, ht, hu, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_ind {Γ : Ctx} {i : Nat} {T : Tm} (h : HasType sg Γ (.ind i) T) :
    i < sg.length ∧ Conv (.sort .star) T := by
  generalize hx : Tm.ind i = x at h
  induction h with
  | ind hi => cases hx; exact ⟨hi, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨hi, h'⟩ := ih hx
      exact ⟨hi, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_ctor {Γ : Ctx} {i k : Nat} {mask : List Bool} {as T : Tm}
    (h : HasType sg Γ (.ctor i k mask as) T) :
    ∃ c, sg.ctorArgs i k = some c ∧ mask = c.mask ∧ as.isList = true ∧
      as.toList.length = c.length ∧
      (∀ j < c.length, HasType sg Γ (as.nth j) (argTy i (c.getD j none))) ∧ Conv (.ind i) T := by
  generalize hx : Tm.ctor i k mask as = x at h
  induction h with
  | ctor hc hm hl hlen ha => cases hx; exact ⟨_, hc, hm, hl, hlen, ha, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨c, h1, h2, h3, h4, h5, h'⟩ := ih hx
      exact ⟨c, h1, h2, h3, h4, h5, h'.trans hc⟩
  | _ => cases hx

theorem HasType.gen_elim {Γ : Ctx} {i : Nat} {C bs t T : Tm}
    (h : HasType sg Γ (.elim i C bs t) T) :
    ∃ m, sg.numCtors i = some m ∧ HasType sg Γ C (.sort .star) ∧ bs.isList = true ∧
      bs.toList.length = m ∧
      (∀ k c, sg.ctorArgs i k = some c → HasType sg Γ (bs.nth k) (branchTy i c C)) ∧
      (∀ k c, sg.ctorArgs i k = some c → ∀ o ∈ c, HasType sg Γ (argTy i o) (.sort .star)) ∧
      HasType sg Γ t (.ind i) ∧ Conv C T := by
  generalize hx : Tm.elim i C bs t = x at h
  induction h with
  | elim hm hC hl hlen hb ha ht => cases hx; exact ⟨_, hm, hC, hl, hlen, hb, ha, ht, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      obtain ⟨m, h1, h2, h3, h4, h5, h5', h6, h'⟩ := ih hx
      exact ⟨m, h1, h2, h3, h4, h5, h5', h6, h'.trans hc⟩
  | _ => cases hx

/-! ## Correctness of types -/

/-- **Every type is `□` or is itself typed by a sort.** -/
theorem HasType.correct {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) (hΓ : Wf sg Γ) :
    T = .sort .box ∨ ∃ s, HasType sg Γ T (.sort s) := by
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
  | ind _ => exact .inr ⟨_, .sort⟩
  | ctor hc _ _ _ _ _ => exact .inr ⟨_, .ind (Sig.ctorArgs_lt hc)⟩
  | elim _ hC _ _ _ _ _ _ _ _ _ => exact .inr ⟨_, hC⟩

end LambdaLab.Languages.CoIC.DeBruijn
