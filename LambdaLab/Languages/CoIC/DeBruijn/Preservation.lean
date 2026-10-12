import LambdaLab.Languages.CoIC.DeBruijn.Inversion

/-!
# CoC with inductive types — subject reduction, and uniqueness of types

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

variable {sg : Sig}

/-! ## Arrows, branches and spines -/

/-- Two lists convertible pointwise. -/
inductive CList : List Tm → List Tm → Prop where
  | nil : CList [] []
  | cons {a a' : Tm} {l l' : List Tm} : Conv a a' → CList l l' → CList (a :: l) (a' :: l')

theorem CList.refl : ∀ l : List Tm, CList l l
  | [] => .nil
  | a :: l => .cons (Conv.refl a) (CList.refl l)

theorem CList.append {l₁ l₁' l₂ l₂' : List Tm} (h₁ : CList l₁ l₁') (h₂ : CList l₂ l₂') :
    CList (l₁ ++ l₂) (l₁' ++ l₂') := by
  induction h₁ with
  | nil => exact h₂
  | cons ha _ ih => exact .cons ha ih

theorem CList.replicate {a a' : Tm} (h : Conv a a') :
    ∀ n, CList (List.replicate n a) (List.replicate n a')
  | 0 => .nil
  | n + 1 => .cons h (CList.replicate h n)

theorem Conv.arrows {ds ds' : List Tm} {c c' : Tm} (hd : CList ds ds') (hc : Conv c c') :
    Conv (arrows ds c) (arrows ds' c') := by
  induction hd with
  | nil => exact hc
  | cons ha _ ih => exact Conv.pi ha (ih.ren Nat.succ)

/-- Convertible result types give convertible branch types. -/
theorem Conv.branchTy {i : Nat} {c : CtorSpec} {C C' : Tm} (h : Conv C C') :
    Conv (branchTy i c C) (branchTy i c C') :=
  Conv.arrows ((CList.refl _).append (CList.replicate h _)) h

/-- A branch type is a type, when the argument types and the result are. -/
theorem HasType.branchTy_sort {Γ : Ctx} {i : Nat} {c : CtorSpec} {C : Tm}
    (hargs : ∀ o ∈ c, HasType sg Γ (argTy i o) (.sort .star)) (hC : HasType sg Γ C (.sort .star)) :
    HasType sg Γ (branchTy i c C) (.sort .star) := by
  refine HasType.arrows_sort (fun d hd => ?_) hC
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hd
    exact hargs o ho
  · rw [(List.eq_of_mem_replicate hd)]
    exact hC

/-- Arguments typed pointwise by position are typed as a list. -/
theorem TyList.of_getD {Γ : Ctx} : ∀ {as ds : List Tm} (d₀ : Tm), as.length = ds.length →
    (∀ j < ds.length, HasType sg Γ (as.getD j d₀) (ds.getD j d₀)) → TyList sg Γ as ds
  | [], [], _, _, _ => .nil
  | a :: as, d :: ds, d₀, hl, h =>
      .cons (h 0 (by simp)) (TyList.of_getD d₀ (by simpa using hl) (fun j hj => by
        simpa using h (j + 1) (by simp; omega)))
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

/-- The recursive calls of a constructor are typed by the result type, one per recursive
argument. -/
theorem TyList.recCalls {Γ : Ctx} {i : Nat} {C bs : Tm}
    (helim : ∀ a, HasType sg Γ a (.ind i) → HasType sg Γ (.elim i C bs a) C) :
    ∀ (as : List Tm) (c : CtorSpec), as.length = c.length →
      (∀ j < c.length, HasType sg Γ (as.getD j (.sort .star)) (argTy i (c.getD j none))) →
      TyList sg Γ (Tm.recCalls i C bs as c.mask) (List.replicate c.recCount C)
  | [], [], _, _ => .nil
  | a :: as, o :: c, hl, h => by
      have ih := TyList.recCalls helim as c (by simpa using hl) (fun j hj => by
        simpa using h (j + 1) (by simp; omega))
      cases o with
      | none =>
          have ha := h 0 (by simp)
          simp only [List.getD_cons_zero, argTy] at ha
          simpa [Tm.recCalls, CtorSpec.mask, CtorSpec.recCount, List.replicate_succ] using
            TyList.cons (helim a ha) ih
      | some A =>
          simpa [Tm.recCalls, CtorSpec.mask, CtorSpec.recCount] using ih
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- The result type of an application is well-sorted. -/
theorem HasType.inst_sorted {Γ : Ctx} {t u A B : Tm} (ht : HasType sg Γ t (.pi A B))
    (hu : HasType sg Γ u A) (hΓ : Wf sg Γ) : ∃ s, HasType sg Γ (B.inst u) (.sort s) := by
  rcases ht.correct hΓ with h | ⟨s, hs⟩
  · cases h
  · obtain ⟨_, s₂, _, hB, _⟩ := hs.gen_pi
    exact ⟨s₂, hB.inst hu⟩

/-- **Subject reduction.** -/
theorem HasType.preservation {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) :
    Wf sg Γ → ∀ {t' : Tm}, Step t t' → HasType sg Γ t' T := by
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
  | ind => intro _ _ hs; cases hs
  | @ctor Γ i k mask as c hc hm hl hlen ha iha =>
      intro hΓ _ hs
      cases hs with
      | ctorA h' =>
          obtain ⟨hlen', j, hj, heq⟩ := h'.list_inv hl
          refine .ctor hc hm (h'.isList hl) (hlen'.trans hlen) (fun j' hj' => ?_)
          by_cases e : j' = j
          · subst e; exact iha j' hj' hΓ hj
          · rw [heq j' e]; exact ha j' hj'
  | @elim Γ i m C bs t hm hC hl hlen hb harg ht ihC ihb _ iht =>
      intro hΓ _ hs
      cases hs with
      | elimC h' =>
          have hC' := ihC hΓ h'
          have hcv := Conv.ofStep h'
          refine .conv (.elim hm hC' hl hlen (fun k c hc => ?_) harg ht) hC hcv.symm
          exact .conv (hb k c hc) (HasType.branchTy_sort (harg k c hc) hC') (Conv.branchTy hcv)
      | elimB h' =>
          obtain ⟨hlen', j, hj, heq⟩ := h'.list_inv hl
          refine .elim hm hC (h'.isList hl) (hlen'.trans hlen) (fun k c hc => ?_) harg ht
          by_cases e : k = j
          · subst e; exact ihb k c hc hΓ hj
          · rw [heq k e]; exact hb k c hc
      | elimT h' => exact .elim hm hC hl hlen hb harg (iht hΓ h')
      | @iota _ k mask _ _ as hbl hal =>
          obtain ⟨c, hc, hmask, _, hlenas, has, _⟩ := ht.gen_ctor
          subst hmask
          have hf := hb k c hc
          refine HasType.apps hf (TyList.append ?_ ?_)
          · refine TyList.of_getD (.sort .star) (by simpa using hlenas) (fun j hj => ?_)
            have hj' : j < c.length := by simpa using hj
            have := has j hj'
            simpa [Tm.nth, List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_getElem hj'] using this
          · exact TyList.recCalls (fun a ha => .elim hm hC hl hlen hb harg ha) as.toList c hlenas
              (fun j hj => has j hj)

/-- Subject reduction along many steps. -/
theorem HasType.preservation_red {Γ : Ctx} {t t' T : Tm} (h : HasType sg Γ t T) (hΓ : Wf sg Γ)
    (hr : Red t t') : HasType sg Γ t' T := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.preservation hΓ hs

/-- An argument list has no type. -/
theorem HasType.not_list {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) :
    t ≠ .tnil ∧ ∀ a l, t ≠ .tcons a l := by
  induction h with
  | conv _ _ _ ih _ => exact ih
  | _ => exact ⟨nofun, fun _ _ => nofun⟩

/-- **Uniqueness of types**: two types of one term are convertible. -/
theorem HasType.unique : ∀ {Γ : Ctx} {t T₁ T₂ : Tm},
    HasType sg Γ t T₁ → HasType sg Γ t T₂ → Conv T₁ T₂
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
  | _, .ind _, _, _, h₁, h₂ => h₁.gen_ind.2.symm.trans h₂.gen_ind.2
  | _, .ctor _ _ _ _, _, _, h₁, h₂ => by
      obtain ⟨_, _, _, _, _, _, c₁⟩ := h₁.gen_ctor
      obtain ⟨_, _, _, _, _, _, c₂⟩ := h₂.gen_ctor
      exact c₁.symm.trans c₂
  | _, .elim _ _ _ _, _, _, h₁, h₂ => by
      obtain ⟨_, _, _, _, _, _, _, _, c₁⟩ := h₁.gen_elim
      obtain ⟨_, _, _, _, _, _, _, _, c₂⟩ := h₂.gen_elim
      exact c₁.symm.trans c₂
  | _, .tnil, _, _, h₁, _ => absurd rfl h₁.not_list.1
  | _, .tcons _ _, _, _, h₁, _ => absurd rfl (h₁.not_list.2 _ _)

/-! ## Nothing well-typed is `□` -/

/-- No well-typed term reduces to `□`. -/
theorem HasType.not_red_box {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) (hΓ : Wf sg Γ)
    (hr : Red t (.sort .box)) : False :=
  (h.preservation_red hΓ hr).ne_box rfl

/-- **No well-typed term is convertible to `□`.** -/
theorem HasType.not_conv_box {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) (hΓ : Wf sg Γ)
    (hc : Conv t (.sort .box)) : False :=
  h.not_red_box hΓ hc.to_sort

/-- So a conversion never reaches `□` from a well-sorted type: a term typed by `□` is typed so
without conversion. -/
theorem HasType.conv_box_eq {Γ : Ctx} {A : Tm} {s : Srt} (hA : HasType sg Γ A (.sort s))
    (hΓ : Wf sg Γ)
    (hc : Conv (.sort .box) A) : False :=
  hA.not_conv_box hΓ hc.symm

end LambdaLab.Languages.CoIC.DeBruijn
