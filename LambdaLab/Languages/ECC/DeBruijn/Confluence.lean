import LambdaLab.Languages.ECC.DeBruijn.Reduction

/-!
# ECC — confluence, and conversion

β-reduction is confluent (`Red.confluent`), by Tait–Martin-Löf parallel reduction and Takahashi's
complete development:

1. `Par` contracts any set of redexes at once; `Step ⊆ Par ⊆ Red`.
2. `Par` is closed under substitution of parallel-reducing terms (`Par.subst`).
3. `cd t` contracts every redex of `t`; every parallel reduct of `t` parallel-reduces to it
   (`Par.triangle`), so `Par` has the diamond property, and `Red` is confluent by a strip lemma.

**Conversion** is then joinability, `Conv a b := ∃ c, Red a c ∧ Red b c`, an equivalence by
confluence (`Conv.trans`). What typing needs from it is that it cannot confuse rigid shapes: two
products are convertible only componentwise (`Conv.pi_inj`), and a sort is convertible only to
itself (`Conv.sort_inj`, `Conv.sort_pi`).
-/

namespace LambdaLab.Languages.ECC.DeBruijn

open LambdaLab (RTC)

/-! ## Parallel reduction -/

inductive Par : Tm → Tm → Prop where
  | var {n : Nat} : Par (.var n) (.var n)
  | sort {s : Srt} : Par (.sort s) (.sort s)
  | pi {A A' B B' : Tm} : Par A A' → Par B B' → Par (.pi A B) (.pi A' B')
  | lam {A A' t t' : Tm} : Par A A' → Par t t' → Par (.lam A t) (.lam A' t')
  | app {t t' u u' : Tm} : Par t t' → Par u u' → Par (.app t u) (.app t' u')
  | beta {A t t' u u' : Tm} : Par t t' → Par u u' → Par (.app (.lam A t) u) (t'.inst u')

theorem Par.refl : ∀ t : Tm, Par t t
  | .var _ => .var
  | .sort _ => .sort
  | .pi A B => .pi (Par.refl A) (Par.refl B)
  | .lam A t => .lam (Par.refl A) (Par.refl t)
  | .app t u => .app (Par.refl t) (Par.refl u)

theorem Step.toPar {t t' : Tm} (h : Step t t') : Par t t' := by
  induction h with
  | beta => exact .beta (Par.refl _) (Par.refl _)
  | appL _ ih => exact .app ih (Par.refl _)
  | appR _ ih => exact .app (Par.refl _) ih
  | lamA _ ih => exact .lam ih (Par.refl _)
  | lamB _ ih => exact .lam (Par.refl _) ih
  | piA _ ih => exact .pi ih (Par.refl _)
  | piB _ ih => exact .pi (Par.refl _) ih

theorem Par.toRed {t t' : Tm} (h : Par t t') : Red t t' := by
  induction h with
  | var => exact .refl
  | sort => exact .refl
  | pi _ _ ihA ihB => exact Red.pi ihA ihB
  | lam _ _ ihA iht => exact Red.lam ihA iht
  | app _ _ iht ihu => exact Red.app iht ihu
  | beta _ _ iht ihu => exact (Red.app (Red.lam .refl iht) ihu).tail .beta

theorem Par.ren {t t' : Tm} (h : Par t t') : ∀ ξ : Nat → Nat, Par (t.ren ξ) (t'.ren ξ) := by
  induction h with
  | var => intro ξ; exact .var
  | sort => intro ξ; exact .sort
  | pi _ _ ihA ihB => intro ξ; exact .pi (ihA ξ) (ihB _)
  | lam _ _ ihA iht => intro ξ; exact .lam (ihA ξ) (iht _)
  | app _ _ iht ihu => intro ξ; exact .app (iht ξ) (ihu ξ)
  | beta _ _ iht ihu =>
      intro ξ
      rw [Tm.ren_inst]
      exact .beta (iht _) (ihu ξ)

theorem Par.up {σ τ : Nat → Tm} (h : ∀ n, Par (σ n) (τ n)) : ∀ n, Par (Tm.up σ n) (Tm.up τ n)
  | 0 => .var
  | n + 1 => (h n).ren Nat.succ

/-- **Parallel reduction is closed under parallel-reducing substitutions.** -/
theorem Par.subst {t t' : Tm} (h : Par t t') :
    ∀ {σ τ : Nat → Tm}, (∀ n, Par (σ n) (τ n)) → Par (t.subst σ) (t'.subst τ) := by
  induction h with
  | var => intro σ τ hs; exact hs _
  | sort => intro σ τ _; exact .sort
  | pi _ _ ihA ihB => intro σ τ hs; exact .pi (ihA hs) (ihB (Par.up hs))
  | lam _ _ ihA iht => intro σ τ hs; exact .lam (ihA hs) (iht (Par.up hs))
  | app _ _ iht ihu => intro σ τ hs; exact .app (iht hs) (ihu hs)
  | beta _ _ iht ihu =>
      intro σ τ hs
      rw [Tm.subst_inst]
      exact .beta (iht (Par.up hs)) (ihu hs)

theorem Par.inst {t t' u u' : Tm} (ht : Par t t') (hu : Par u u') : Par (t.inst u) (t'.inst u') :=
  Par.subst ht (fun n => by cases n with | zero => exact hu | succ n => exact .var)

theorem Par.lam_inv {A t x : Tm} (h : Par (.lam A t) x) :
    ∃ A' t', x = .lam A' t' ∧ Par A A' ∧ Par t t' := by
  cases h with
  | lam hA ht => exact ⟨_, _, rfl, hA, ht⟩

/-! ## Complete development -/

/-- **Contract every redex**, innermost results first. -/
def cd : Tm → Tm
  | .var n => .var n
  | .sort s => .sort s
  | .pi A B => .pi (cd A) (cd B)
  | .lam A t => .lam (cd A) (cd t)
  | .app (.lam _ t) u => (cd t).inst (cd u)
  | .app t u => .app (cd t) (cd u)

theorem cd_app_lam (A t u : Tm) : cd (.app (.lam A t) u) = (cd t).inst (cd u) := rfl

theorem cd_app_of_not_lam {t u : Tm} (h : ∀ A b, t ≠ .lam A b) :
    cd (.app t u) = .app (cd t) (cd u) := by
  cases t with
  | lam A b => exact absurd rfl (h A b)
  | _ => rfl

/-- **The triangle**: a parallel reduct reduces, in parallel, to the complete development. -/
theorem Par.triangle {t u : Tm} (h : Par t u) : Par u (cd t) := by
  induction h with
  | var => exact .var
  | sort => exact .sort
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ ihA iht => exact .lam ihA iht
  | @app t t' u u' ht _ iht ihu =>
      cases t with
      | lam A b =>
          obtain ⟨A', b', rfl, _, _⟩ := Par.lam_inv ht
          obtain ⟨_, _, heq, _, hb⟩ := Par.lam_inv iht
          cases heq
          rw [cd_app_lam]
          exact .beta hb ihu
      | _ =>
          rw [cd_app_of_not_lam (fun _ _ h => Tm.noConfusion h)]
          exact .app iht ihu
  | beta _ _ iht ihu => exact Par.inst iht ihu

theorem Par.diamond {t u v : Tm} (hu : Par t u) (hv : Par t v) : ∃ w, Par u w ∧ Par v w :=
  ⟨cd t, hu.triangle, hv.triangle⟩

/-! ## Confluence -/

theorem Par.strip {t u v : Tm} (hu : Par t u) (hv : Red t v) : ∃ w, Red u w ∧ Par v w := by
  induction hv with
  | refl => exact ⟨u, .refl, hu⟩
  | tail _ hs ih =>
      obtain ⟨w, huw, hw⟩ := ih
      obtain ⟨x, hwx, hvx⟩ := Par.diamond hw hs.toPar
      exact ⟨x, huw.trans hwx.toRed, hvx⟩

/-- **Church–Rosser**: two reductions from one term can be joined. -/
theorem Red.confluent {t u v : Tm} (hu : Red t u) (hv : Red t v) : ∃ w, Red u w ∧ Red v w := by
  induction hu with
  | refl => exact ⟨v, hv, .refl⟩
  | tail _ hs ih =>
      obtain ⟨w, huw, hvw⟩ := ih
      obtain ⟨x, hx, hwx⟩ := Par.strip hs.toPar huw
      exact ⟨x, hx, hvw.trans hwx.toRed⟩

/-! ## Conversion -/

/-- **Convertibility**: a common reduct. An equivalence, by confluence. -/
def Conv (a b : Tm) : Prop := ∃ c, Red a c ∧ Red b c

theorem Conv.refl (a : Tm) : Conv a a := ⟨a, .refl, .refl⟩

theorem Conv.symm {a b : Tm} (h : Conv a b) : Conv b a :=
  let ⟨c, ha, hb⟩ := h
  ⟨c, hb, ha⟩

theorem Conv.trans {a b c : Tm} (hab : Conv a b) (hbc : Conv b c) : Conv a c := by
  obtain ⟨x, hax, hbx⟩ := hab
  obtain ⟨y, hby, hcy⟩ := hbc
  obtain ⟨z, hxz, hyz⟩ := Red.confluent hbx hby
  exact ⟨z, hax.trans hxz, hcy.trans hyz⟩

theorem Conv.ofRed {a b : Tm} (h : Red a b) : Conv a b := ⟨b, h, .refl⟩

theorem Conv.ofStep {a b : Tm} (h : Step a b) : Conv a b := Conv.ofRed (RTC.single h)

theorem Conv.red_left {a a' b : Tm} (h : Red a a') (hc : Conv a' b) : Conv a b :=
  (Conv.ofRed h).trans hc

theorem Conv.red_right {a b b' : Tm} (hc : Conv a b') (h : Red b b') : Conv a b :=
  hc.trans (Conv.ofRed h).symm

theorem Conv.pi {A A' B B' : Tm} (hA : Conv A A') (hB : Conv B B') : Conv (.pi A B) (.pi A' B') :=
  let ⟨a, h1, h2⟩ := hA
  let ⟨b, h3, h4⟩ := hB
  ⟨.pi a b, Red.pi h1 h3, Red.pi h2 h4⟩

theorem Conv.lam {A A' t t' : Tm} (hA : Conv A A') (ht : Conv t t') :
    Conv (.lam A t) (.lam A' t') :=
  let ⟨a, h1, h2⟩ := hA
  let ⟨b, h3, h4⟩ := ht
  ⟨.lam a b, Red.lam h1 h3, Red.lam h2 h4⟩

theorem Conv.app {t t' u u' : Tm} (ht : Conv t t') (hu : Conv u u') :
    Conv (.app t u) (.app t' u') :=
  let ⟨a, h1, h2⟩ := ht
  let ⟨b, h3, h4⟩ := hu
  ⟨.app a b, Red.app h1 h3, Red.app h2 h4⟩

theorem Conv.ren {a b : Tm} (h : Conv a b) (ξ : Nat → Nat) : Conv (a.ren ξ) (b.ren ξ) :=
  let ⟨c, h1, h2⟩ := h
  ⟨c.ren ξ, h1.ren ξ, h2.ren ξ⟩

theorem Conv.subst {a b : Tm} (h : Conv a b) (σ : Nat → Tm) : Conv (a.subst σ) (b.subst σ) :=
  let ⟨c, h1, h2⟩ := h
  ⟨c.subst σ, h1.subst σ, h2.subst σ⟩

/-- **Substituting convertible terms gives convertible results.** -/
theorem Conv.subst_conv (t : Tm) {σ τ : Nat → Tm} (h : ∀ n, Conv (σ n) (τ n)) :
    Conv (t.subst σ) (t.subst τ) :=
  ⟨t.subst (fun n => Classical.choose (h n)),
    Red.subst_red t (fun n => (Classical.choose_spec (h n)).1),
    Red.subst_red t (fun n => (Classical.choose_spec (h n)).2)⟩

theorem Conv.inst {t t' u u' : Tm} (ht : Conv t t') (hu : Conv u u') :
    Conv (t.inst u) (t'.inst u') :=
  (ht.subst _).trans (Conv.subst_conv t' (fun n => by
    cases n with
    | zero => exact hu
    | succ n => exact Conv.refl _))

/-! ## Rigid shapes -/

theorem Conv.sort_inj {s s' : Srt} (h : Conv (.sort s) (.sort s')) : s = s' := by
  obtain ⟨c, h1, h2⟩ := h
  rw [Red.sort_inv h1] at h2
  have := Red.sort_inv h2
  cases this
  rfl

theorem Conv.sort_pi {s : Srt} {A B : Tm} : ¬ Conv (.sort s) (.pi A B) := by
  rintro ⟨c, h1, h2⟩
  rw [Red.sort_inv h1] at h2
  obtain ⟨_, _, h, _, _⟩ := Red.pi_inv h2
  cases h

/-- **Π-injectivity**: convertible products have convertible components. -/
theorem Conv.pi_inj {A A' B B' : Tm} (h : Conv (.pi A B) (.pi A' B')) : Conv A A' ∧ Conv B B' := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨a1, b1, rfl, hA1, hB1⟩ := Red.pi_inv h1
  obtain ⟨a2, b2, heq, hA2, hB2⟩ := Red.pi_inv h2
  cases heq
  exact ⟨⟨_, hA1, hA2⟩, ⟨_, hB1, hB2⟩⟩

/-- Anything convertible to a sort reduces to it. -/
theorem Conv.to_sort {t : Tm} {s : Srt} (h : Conv t (.sort s)) : Red t (.sort s) := by
  obtain ⟨c, h1, h2⟩ := h
  rw [Red.sort_inv h2] at h1
  exact h1

end LambdaLab.Languages.ECC.DeBruijn
