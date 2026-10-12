import LambdaLab.Languages.CoIC.DeBruijn.Reduction

/-!
# CoC with inductive types — confluence, and conversion

β- and ι-reduction together are confluent (`Red.confluent`), by Tait–Martin-Löf parallel
reduction and Takahashi's complete development:

1. `Par` contracts any set of redexes at once — β and ι alike; `Step ⊆ Par ⊆ Red`. An ι-redex is a
   single node, so its parallel contraction (`Par.iota`) just reduces the node's parts first.
2. `Par` is closed under substitution of parallel-reducing terms (`Par.subst`).
3. `cd t` contracts every redex of `t`; every parallel reduct of `t` parallel-reduces to it
   (`Par.triangle`), so `Par` has the diamond property, and `Red` is confluent by a strip lemma.

**Conversion** is then joinability, `Conv a b := ∃ c, Red a c ∧ Red b c`, an equivalence by
confluence (`Conv.trans`). What typing needs from it is that it cannot confuse rigid shapes: two
products are convertible only componentwise (`Conv.pi_inj`), and a sort is convertible only to
itself (`Conv.sort_inj`, `Conv.sort_pi`), and an inductive type only to itself (`Conv.ind_inj`,
`Conv.ind_sort`, `Conv.ind_pi`).
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

open LambdaLab (RTC)

/-! ## Parallel reduction -/

inductive Par : Tm → Tm → Prop where
  | var {n : Nat} : Par (.var n) (.var n)
  | sort {s : Srt} : Par (.sort s) (.sort s)
  | pi {A A' B B' : Tm} : Par A A' → Par B B' → Par (.pi A B) (.pi A' B')
  | lam {A A' t t' : Tm} : Par A A' → Par t t' → Par (.lam A t) (.lam A' t')
  | app {t t' u u' : Tm} : Par t t' → Par u u' → Par (.app t u) (.app t' u')
  | beta {A t t' u u' : Tm} : Par t t' → Par u u' → Par (.app (.lam A t) u) (t'.inst u')
  | ind {i : Nat} : Par (.ind i) (.ind i)
  | ctor {i k : Nat} {mask : List Bool} {as as' : Tm} : Par as as' →
      Par (.ctor i k mask as) (.ctor i k mask as')
  | elim {i : Nat} {C C' bs bs' t t' : Tm} : Par C C' → Par bs bs' → Par t t' →
      Par (.elim i C bs t) (.elim i C' bs' t')
  | iota {i k : Nat} {mask : List Bool} {C C' bs bs' as as' : Tm} :
      bs.isList = true → as.isList = true → Par C C' → Par bs bs' → Par as as' →
      Par (.elim i C bs (.ctor i k mask as)) (Tm.iotaRhs i C' bs' k mask as')
  | tnil : Par .tnil .tnil
  | tcons {a a' l l' : Tm} : Par a a' → Par l l' → Par (.tcons a l) (.tcons a' l')

theorem Par.refl : ∀ t : Tm, Par t t
  | .var _ => .var
  | .sort _ => .sort
  | .pi A B => .pi (Par.refl A) (Par.refl B)
  | .lam A t => .lam (Par.refl A) (Par.refl t)
  | .app t u => .app (Par.refl t) (Par.refl u)
  | .ind _ => .ind
  | .ctor _ _ _ as => .ctor (Par.refl as)
  | .elim _ C bs t => .elim (Par.refl C) (Par.refl bs) (Par.refl t)
  | .tnil => .tnil
  | .tcons a l => .tcons (Par.refl a) (Par.refl l)

theorem Step.toPar {t t' : Tm} (h : Step t t') : Par t t' := by
  induction h with
  | beta => exact .beta (Par.refl _) (Par.refl _)
  | appL _ ih => exact .app ih (Par.refl _)
  | appR _ ih => exact .app (Par.refl _) ih
  | lamA _ ih => exact .lam ih (Par.refl _)
  | lamB _ ih => exact .lam (Par.refl _) ih
  | piA _ ih => exact .pi ih (Par.refl _)
  | piB _ ih => exact .pi (Par.refl _) ih
  | iota hb ha => exact .iota hb ha (Par.refl _) (Par.refl _) (Par.refl _)
  | ctorA _ ih => exact .ctor ih
  | elimC _ ih => exact .elim ih (Par.refl _) (Par.refl _)
  | elimB _ ih => exact .elim (Par.refl _) ih (Par.refl _)
  | elimT _ ih => exact .elim (Par.refl _) (Par.refl _) ih
  | consH _ ih => exact .tcons ih (Par.refl _)
  | consT _ ih => exact .tcons (Par.refl _) ih

/-- Parallel reduction keeps an argument list a list. -/
theorem Par.isList {l l' : Tm} (h : Par l l') (hl : l.isList = true) : l'.isList = true := by
  induction h with
  | tcons _ _ _ ih => exact ih hl
  | _ => simp_all [Tm.isList]

theorem Par.toRed {t t' : Tm} (h : Par t t') : Red t t' := by
  induction h with
  | var => exact .refl
  | sort => exact .refl
  | pi _ _ ihA ihB => exact Red.pi ihA ihB
  | lam _ _ ihA iht => exact Red.lam ihA iht
  | app _ _ iht ihu => exact Red.app iht ihu
  | beta _ _ iht ihu => exact (Red.app (Red.lam .refl iht) ihu).tail .beta
  | ind => exact .refl
  | ctor _ ih => exact Red.ctor ih
  | elim _ _ _ ihC ihb iht => exact Red.elim ihC ihb iht
  | iota hb ha _ hpb hpa ihC ihb iha =>
      exact (Red.elim ihC ihb (Red.ctor iha)).tail (.iota (hpb.isList hb) (hpa.isList ha))
  | tnil => exact .refl
  | tcons _ _ iha ihl => exact Red.tcons iha ihl

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
  | ind => intro ξ; exact .ind
  | ctor _ ih => intro ξ; exact .ctor (ih ξ)
  | elim _ _ _ ihC ihb iht => intro ξ; exact .elim (ihC ξ) (ihb ξ) (iht ξ)
  | iota hb ha _ hpb hpa ihC ihb iha =>
      intro ξ
      rw [Tm.iotaRhs_ren _ _ (hpb.isList hb) (hpa.isList ha)]
      exact .iota (Tm.isList_ren _ _ hb) (Tm.isList_ren _ _ ha) (ihC ξ) (ihb ξ) (iha ξ)
  | tnil => intro ξ; exact .tnil
  | tcons _ _ iha ihl => intro ξ; exact .tcons (iha ξ) (ihl ξ)

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
  | ind => intro σ τ _; exact .ind
  | ctor _ ih => intro σ τ hs; exact .ctor (ih hs)
  | elim _ _ _ ihC ihb iht => intro σ τ hs; exact .elim (ihC hs) (ihb hs) (iht hs)
  | iota hb ha _ hpb hpa ihC ihb iha =>
      intro σ τ hs
      rw [Tm.iotaRhs_subst _ _ (hpb.isList hb) (hpa.isList ha)]
      exact .iota (Tm.isList_subst _ _ hb) (Tm.isList_subst _ _ ha) (ihC hs) (ihb hs) (iha hs)
  | tnil => intro σ τ _; exact .tnil
  | tcons _ _ iha ihl => intro σ τ hs; exact .tcons (iha hs) (ihl hs)

theorem Par.inst {t t' u u' : Tm} (ht : Par t t') (hu : Par u u') : Par (t.inst u) (t'.inst u') :=
  Par.subst ht (fun n => by cases n with | zero => exact hu | succ n => exact .var)

theorem Par.lam_inv {A t x : Tm} (h : Par (.lam A t) x) :
    ∃ A' t', x = .lam A' t' ∧ Par A A' ∧ Par t t' := by
  cases h with
  | lam hA ht => exact ⟨_, _, rfl, hA, ht⟩

theorem Par.ctor_inv {i k : Nat} {mask : List Bool} {as x : Tm} (h : Par (.ctor i k mask as) x) :
    ∃ as', x = .ctor i k mask as' ∧ Par as as' := by
  cases h with
  | ctor h => exact ⟨_, rfl, h⟩

/-! ## Parallel reduction of lists, spines and ι-contracta -/

/-- Two lists that parallel-reduce pointwise. -/
inductive PList : List Tm → List Tm → Prop where
  | nil : PList [] []
  | cons {a a' : Tm} {l l' : List Tm} : Par a a' → PList l l' → PList (a :: l) (a' :: l')

theorem PList.append {l₁ l₁' l₂ l₂' : List Tm} (h₁ : PList l₁ l₁') (h₂ : PList l₂ l₂') :
    PList (l₁ ++ l₂) (l₁' ++ l₂') := by
  induction h₁ with
  | nil => exact h₂
  | cons ha _ ih => exact .cons ha ih

/-- An argument list parallel-reduces pointwise. -/
theorem Par.toList {l l' : Tm} (h : Par l l') (hl : l.isList = true) :
    PList l.toList l'.toList := by
  induction h with
  | tnil => exact .nil
  | tcons ha _ _ ihl => exact .cons ha (ihl hl)
  | _ => simp [Tm.isList] at hl

theorem PList.getD {l l' : List Tm} (h : PList l l') (k : Nat) (d : Tm) :
    Par (l.getD k d) (l'.getD k d) := by
  induction h generalizing k with
  | nil => exact Par.refl d
  | cons ha _ ih =>
      cases k with
      | zero => exact ha
      | succ k => exact ih k

theorem Par.apps {h h' : Tm} {l l' : List Tm} (hh : Par h h') (hl : PList l l') :
    Par (Tm.apps h l) (Tm.apps h' l') := by
  induction hl generalizing h h' with
  | nil => exact hh
  | cons ha _ ih => exact ih (.app hh ha)

theorem PList.recCalls {i : Nat} {C C' bs bs' : Tm} (hC : Par C C') (hb : Par bs bs')
    {as as' : List Tm} (ha : PList as as') (mask : List Bool) :
    PList (Tm.recCalls i C bs as mask) (Tm.recCalls i C' bs' as' mask) := by
  induction ha generalizing mask with
  | nil => exact .nil
  | @cons a a' l l' hpa _ ih =>
      cases mask with
      | nil => exact .nil
      | cons r mask =>
          cases r
          · simpa [Tm.recCalls] using ih mask
          · simpa [Tm.recCalls] using PList.cons (.elim hC hb hpa) (ih mask)

/-- **ι-contracta parallel-reduce with their parts.** -/
theorem Par.iotaRhs {i k : Nat} {mask : List Bool} {C C' bs bs' as as' : Tm}
    (hbl : bs.isList = true) (hal : as.isList = true) (hC : Par C C') (hb : Par bs bs')
    (ha : Par as as') : Par (Tm.iotaRhs i C bs k mask as) (Tm.iotaRhs i C' bs' k mask as') := by
  have hbs := hb.toList hbl
  have has := ha.toList hal
  exact Par.apps (hbs.getD k _) (has.append (PList.recCalls hC hb has mask))

/-! ## Complete development -/

/-- **Contract every redex**, innermost results first. -/
def cd : Tm → Tm
  | .var n => .var n
  | .sort s => .sort s
  | .pi A B => .pi (cd A) (cd B)
  | .lam A t => .lam (cd A) (cd t)
  | .app (.lam _ t) u => (cd t).inst (cd u)
  | .app t u => .app (cd t) (cd u)
  | .ind i => .ind i
  | .ctor i k mask as => .ctor i k mask (cd as)
  | .elim i C bs (.ctor i' k mask as) =>
      if i' = i ∧ bs.isList = true ∧ as.isList = true then
        Tm.iotaRhs i (cd C) (cd bs) k mask (cd as)
      else .elim i (cd C) (cd bs) (.ctor i' k mask (cd as))
  | .elim i C bs t => .elim i (cd C) (cd bs) (cd t)
  | .tnil => .tnil
  | .tcons a l => .tcons (cd a) (cd l)

theorem cd_app_lam (A t u : Tm) : cd (.app (.lam A t) u) = (cd t).inst (cd u) := rfl

theorem cd_app_of_not_lam {t u : Tm} (h : ∀ A b, t ≠ .lam A b) :
    cd (.app t u) = .app (cd t) (cd u) := by
  cases t with
  | lam A b => exact absurd rfl (h A b)
  | _ => rfl

theorem cd_elim_of_not_ctor {i : Nat} {C bs t : Tm} (h : ∀ i' k mask as, t ≠ .ctor i' k mask as) :
    cd (.elim i C bs t) = .elim i (cd C) (cd bs) (cd t) := by
  cases t with
  | ctor i' k mask as => exact absurd rfl (h i' k mask as)
  | _ => rfl

theorem cd_isList {l : Tm} (hl : l.isList = true) : (cd l).isList = true := by
  induction l with
  | tnil => rfl
  | tcons _ _ _ ih => exact ih hl
  | _ => simp [Tm.isList] at hl

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
  | ind => exact .ind
  | ctor _ ih => exact .ctor ih
  | @elim i C C' bs bs' t t' hC hb ht ihC ihb iht =>
      cases t with
      | ctor i' k mask as =>
          obtain ⟨as', rfl, has⟩ := Par.ctor_inv ht
          obtain ⟨as'', heq, has'⟩ := Par.ctor_inv iht
          cases heq
          by_cases hc : i' = i ∧ bs.isList = true ∧ as.isList = true
          · obtain ⟨rfl, hbl, hal⟩ := hc
            have e : cd (.elim i' C bs (.ctor i' k mask as)) =
                Tm.iotaRhs i' (cd C) (cd bs) k mask (cd as) := by
              simp [cd, hbl, hal]
            rw [e]
            exact .iota (hb.isList hbl) (has.isList hal) ihC ihb has'
          · have e : cd (.elim i C bs (.ctor i' k mask as)) =
                .elim i (cd C) (cd bs) (.ctor i' k mask (cd as)) := by
              simp only [cd]
              rw [if_neg hc]
            rw [e]
            exact .elim ihC ihb (.ctor has')
      | _ =>
          rw [cd_elim_of_not_ctor (fun _ _ _ _ h => Tm.noConfusion h)]
          exact .elim ihC ihb iht
  | @iota i k mask C C' bs bs' as as' hbl hal _ _ _ ihC ihb iha =>
      have e : cd (.elim i C bs (.ctor i k mask as)) =
          Tm.iotaRhs i (cd C) (cd bs) k mask (cd as) := by
        simp [cd, hbl, hal]
      rw [e]
      exact Par.iotaRhs (‹Par bs bs'›.isList hbl) (‹Par as as'›.isList hal) ihC ihb iha
  | tnil => exact .tnil
  | tcons _ _ iha ihl => exact .tcons iha ihl

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

/-! ## The inductive constructs -/

theorem Conv.ctor {i k : Nat} {mask : List Bool} {as as' : Tm} (h : Conv as as') :
    Conv (.ctor i k mask as) (.ctor i k mask as') :=
  let ⟨c, h1, h2⟩ := h
  ⟨.ctor i k mask c, Red.ctor h1, Red.ctor h2⟩

theorem Conv.elim {i : Nat} {C C' bs bs' t t' : Tm} (hC : Conv C C') (hb : Conv bs bs')
    (ht : Conv t t') : Conv (.elim i C bs t) (.elim i C' bs' t') :=
  let ⟨c, h1, h2⟩ := hC
  let ⟨b, h3, h4⟩ := hb
  let ⟨d, h5, h6⟩ := ht
  ⟨.elim i c b d, Red.elim h1 h3 h5, Red.elim h2 h4 h6⟩

theorem Conv.tcons {a a' l l' : Tm} (ha : Conv a a') (hl : Conv l l') :
    Conv (.tcons a l) (.tcons a' l') :=
  let ⟨c, h1, h2⟩ := ha
  let ⟨d, h3, h4⟩ := hl
  ⟨.tcons c d, Red.tcons h1 h3, Red.tcons h2 h4⟩

/-- Anything convertible to an inductive type reduces to it. -/
theorem Conv.to_ind {t : Tm} {i : Nat} (h : Conv t (.ind i)) : Red t (.ind i) := by
  obtain ⟨c, h1, h2⟩ := h
  rw [Red.ind_inv h2] at h1
  exact h1

theorem Conv.ind_inj {i j : Nat} (h : Conv (.ind i) (.ind j)) : i = j := by
  have := Red.ind_inv h.to_ind
  cases this
  rfl

theorem Conv.ind_sort {i : Nat} {s : Srt} : ¬ Conv (.ind i) (.sort s) := by
  intro h
  have := Red.sort_inv h.symm.to_ind
  cases this

theorem Conv.ind_pi {i : Nat} {A B : Tm} : ¬ Conv (.ind i) (.pi A B) := by
  intro h
  obtain ⟨_, _, e, _, _⟩ := Red.pi_inv (h.symm.to_ind)
  cases e

end LambdaLab.Languages.CoIC.DeBruijn
