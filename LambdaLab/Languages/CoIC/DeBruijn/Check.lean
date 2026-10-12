import LambdaLab.Languages.CoIC.DeBruijn.Eval

/-!
# CoC with inductive types — the type checker, sound and complete

`infer sg hsg Γ hΓ t` computes a type of `t` in the valid context `Γ` over the valid signature
`sg`, or fails. As in CoC (`Languages/CoC/DeBruijn/Check.lean`), types are compared by their normal
forms and shapes are read off normal forms (`sortOf`, `piOf`, and now `indOf` for the target of a
recursor); normalizing is total because what is normalized is a type, hence strongly normalizing.

A constructor's arguments and a recursor's branches are lists of terms checked against lists of
types (`checkArgs`), each one inferred and its type compared with the expected one — mutually
recursive with `infer`, both structural on the term.

* **Soundness is by construction**: `infer` returns a type together with its derivation.
* **Completeness** (`infer_complete`): if `t` has a type at all, `infer` finds one.

Together they decide the judgement (`decHasType`).
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

open LambdaLab (SN)

variable {sg : Sig}

/-! ## Reading shapes off a type -/

/-- What is convertible to an inductive type normalizes to it. -/
theorem Tm.eval_ind {t : Tm} {i : Nat} (h : SN Step t) (hc : Conv t (.ind i)) :
    t.eval h = .ind i :=
  (Tm.eval_eq_iff h (sn_ind i)).mpr hc |>.trans (Tm.eval_of_normal _ (fun _ hs => nomatch hs))

/-- **Read a sort off the type of `A`.** -/
def sortOf (hsg : WfSig sg) {Γ : Ctx} (hΓ : Wf sg Γ) {A T : Tm} (h : HasType sg Γ A T) :
    Option {s : Srt // HasType sg Γ A (.sort s)} :=
  if hb : T = .sort .box then some ⟨.box, hb ▸ h⟩
  else if he : T.eval (h.sn_type hsg hΓ) = .sort .star then
    some ⟨.star, .conv h .sort (by
      have := (Tm.eval_spec (h.sn_type hsg hΓ)).1
      rw [he] at this
      exact Conv.ofRed this)⟩
  else none

/-- If `A` is sorted at all, `sortOf` finds the sort. -/
theorem sortOf_spec (hsg : WfSig sg) {Γ : Ctx} (hΓ : Wf sg Γ) {A T : Tm} (h : HasType sg Γ A T)
    {s : Srt} (hs : HasType sg Γ A (.sort s)) : ∃ h', sortOf hsg hΓ h = some ⟨s, h'⟩ := by
  unfold sortOf
  have hc := h.unique hs
  by_cases hb : T = .sort .box
  · rw [dif_pos hb]
    subst hb
    cases s with
    | box => exact ⟨_, rfl⟩
    | star => exact absurd (Conv.sort_inj hc) (by decide)
  · rw [dif_neg hb]
    cases s with
    | box =>
        obtain ⟨s', hs'⟩ := (h.correct hΓ).resolve_left hb
        exact (hs'.not_conv_box hΓ hc).elim
    | star => rw [dif_pos (Tm.eval_sort _ hc)]; exact ⟨_, rfl⟩

/-- **Read a product off the type of `t`.** -/
def piOf (hsg : WfSig sg) {Γ : Ctx} (hΓ : Wf sg Γ) {t T : Tm} (h : HasType sg Γ t T) :
    Option {AB : Tm × Tm // HasType sg Γ t (.pi AB.1 AB.2)} :=
  if hb : T = .sort .box then none
  else
    match he : T.eval (h.sn_type hsg hΓ) with
    | .pi A B => some ⟨(A, B), by
        obtain ⟨s, hs⟩ := (h.correct hΓ).resolve_left hb
        have hr := (Tm.eval_spec (h.sn_type hsg hΓ)).1
        rw [he] at hr
        exact .conv h (hs.preservation_red hΓ hr) (Conv.ofRed hr)⟩
    | _ => none

/-- If the type of `t` is convertible to a product, `piOf` finds a convertible product. -/
theorem piOf_spec (hsg : WfSig sg) {Γ : Ctx} (hΓ : Wf sg Γ) {t T A B : Tm}
    (h : HasType sg Γ t T) (hc : Conv T (.pi A B)) :
    ∃ p, piOf hsg hΓ h = some p ∧ Conv A p.1.1 ∧ Conv B p.1.2 := by
  have hb : T ≠ .sort .box := fun e => by subst e; exact Conv.sort_pi hc
  obtain ⟨A', B', he, hA, hB⟩ := Tm.eval_pi (h.sn_type hsg hΓ) hc
  unfold piOf
  rw [dif_neg hb]
  split
  · rename_i A'' B'' he''
    rw [he] at he''
    cases he''
    exact ⟨_, rfl, hA, hB⟩
  · rename_i he''
    rw [he] at he''
    exact (he'' A' B' rfl).elim

/-- **Read an inductive type off the type of `t`.** -/
def indOf (hsg : WfSig sg) {Γ : Ctx} (hΓ : Wf sg Γ) {t T : Tm} (h : HasType sg Γ t T) (i : Nat)
    (hi : i < sg.length) : Option (PLift (HasType sg Γ t (.ind i))) :=
  if hb : T = .sort .box then none
  else if he : T.eval (h.sn_type hsg hΓ) = .ind i then
    some ⟨.conv h (.ind hi) (by
      have := (Tm.eval_spec (h.sn_type hsg hΓ)).1
      rw [he] at this
      exact Conv.ofRed this)⟩
  else none

theorem indOf_isSome (hsg : WfSig sg) {Γ : Ctx} (hΓ : Wf sg Γ) {t T : Tm} (h : HasType sg Γ t T)
    {i : Nat} (hi : i < sg.length) (ht : HasType sg Γ t (.ind i)) :
    (indOf hsg hΓ h i hi).isSome := by
  have hc := h.unique ht
  have hb : T ≠ .sort .box := fun e => by subst e; exact Conv.ind_sort hc.symm
  unfold indOf
  rw [dif_neg hb, dif_pos (Tm.eval_ind _ hc)]
  rfl

/-! ## The signature, listed -/

/-- The constructors of inductive `i`. -/
def Sig.ctorsOf (sg : Sig) (i : Nat) : List CtorSpec := (sg[i]?.map (·.ctors)).getD []

theorem Sig.numCtors_eq {sg : Sig} {i m : Nat} (h : sg.numCtors i = some m) :
    i < sg.length ∧ (sg.ctorsOf i).length = m := by
  simp only [Sig.numCtors, Option.map_eq_some_iff] at h
  obtain ⟨I, hI, rfl⟩ := h
  exact ⟨(List.getElem?_eq_some_iff.mp hI).1, by simp [Sig.ctorsOf, hI]⟩

theorem Sig.ctorArgs_iff {sg : Sig} {i k : Nat} {c : CtorSpec} :
    sg.ctorArgs i k = some c ↔ (sg.ctorsOf i)[k]? = some c := by
  simp only [Sig.ctorArgs, Sig.ctorsOf]
  cases sg[i]? <;> simp

theorem Sig.mem_ctorsOf {sg : Sig} {i : Nat} {c : CtorSpec} (h : c ∈ sg.ctorsOf i) :
    ∃ k, sg.ctorArgs i k = some c := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨k, Sig.ctorArgs_iff.mpr (List.getElem?_eq_getElem hk)⟩

/-- The types of a constructor's arguments are types. -/
theorem argTys_sorted (hsg : WfSig sg) {Γ : Ctx} {i k : Nat} {c : CtorSpec}
    (hc : sg.ctorArgs i k = some c) : ∀ T ∈ c.map (argTy i), ∃ s, HasType sg Γ T (.sort s) := by
  intro T hT
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hT
  exact ⟨_, hsg.argTy hc ho⟩

/-- The types of a recursor's branches are types. -/
theorem branchTys_sorted (hsg : WfSig sg) {Γ : Ctx} {i : Nat} {C : Tm}
    (hC : HasType sg Γ C (.sort .star)) :
    ∀ T ∈ (sg.ctorsOf i).map (branchTy i · C), ∃ s, HasType sg Γ T (.sort s) := by
  intro T hT
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hT
  obtain ⟨k, hk⟩ := Sig.mem_ctorsOf hc
  exact ⟨_, HasType.branchTy_sort (fun o ho => hsg.argTy hk ho) hC⟩

theorem getD_argTy {i : Nat} {c : CtorSpec} {j : Nat} (hj : j < c.length) :
    (c.map (argTy i)).getD j (.sort .star) = argTy i (c.getD j none) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem getD_branchTy {sg : Sig} {i k : Nat} {c : CtorSpec} (hc : sg.ctorArgs i k = some c)
    (C : Tm) : ((sg.ctorsOf i).map (branchTy i · C)).getD k (.sort .star) = branchTy i c C := by
  simp [List.getD_eq_getElem?_getD, Sig.ctorArgs_iff.mp hc]

theorem ctorArgs_lt_ctorsOf {sg : Sig} {i k : Nat} {c : CtorSpec} (hc : sg.ctorArgs i k = some c) :
    k < (sg.ctorsOf i).length :=
  (List.getElem?_eq_some_iff.mp (Sig.ctorArgs_iff.mp hc)).1

/-! ## Inference -/

mutual

/-- **Type inference**, in a valid context over a valid signature. Returns the type with its
derivation. -/
def infer (hsg : WfSig sg) : (Γ : Ctx) → Wf sg Γ → (t : Tm) → Option {T : Tm // HasType sg Γ t T}
  | _, _, .sort .star => some ⟨.sort .box, .sort⟩
  | _, _, .sort .box => none
  | Γ, _, .var n =>
      match h : Γ.lookup n with
      | some A => some ⟨A, .var h⟩
      | none => none
  | Γ, hΓ, .pi A B =>
      match infer hsg Γ hΓ A with
      | none => none
      | some ⟨_, hA⟩ =>
          match sortOf hsg hΓ hA with
          | none => none
          | some ⟨_, hA'⟩ =>
              match infer hsg (A :: Γ) (hΓ.cons hA') B with
              | none => none
              | some ⟨_, hB⟩ =>
                  match sortOf hsg (hΓ.cons hA') hB with
                  | none => none
                  | some ⟨s₂, hB'⟩ => some ⟨.sort s₂, .pi hA' hB'⟩
  | Γ, hΓ, .lam A t =>
      match infer hsg Γ hΓ A with
      | none => none
      | some ⟨_, hA⟩ =>
          match sortOf hsg hΓ hA with
          | none => none
          | some ⟨_, hA'⟩ =>
              match infer hsg (A :: Γ) (hΓ.cons hA') t with
              | none => none
              | some ⟨B, ht⟩ =>
                  if hb : B = .sort .box then none
                  else some ⟨.pi A B, by
                    obtain ⟨s, hs⟩ := (ht.correct (hΓ.cons hA')).resolve_left hb
                    exact .lam hA' ht hs⟩
  | Γ, hΓ, .app t u =>
      match infer hsg Γ hΓ t with
      | none => none
      | some ⟨_, ht⟩ =>
          match piOf hsg hΓ ht with
          | none => none
          | some ⟨(A, B), ht'⟩ =>
              match infer hsg Γ hΓ u with
              | none => none
              | some ⟨U, hu⟩ =>
                  have hsA : SN Step A := by
                    obtain ⟨s, hs⟩ := (ht'.correct hΓ).resolve_left (by intro e; cases e)
                    obtain ⟨_, _, hA, _, _⟩ := hs.gen_pi
                    exact hA.sn hsg hΓ
                  match Conv.decide U A (hu.sn_type hsg hΓ) hsA with
                  | isTrue hc => some ⟨B.inst u, by
                      obtain ⟨s, hs⟩ := (ht'.correct hΓ).resolve_left (by intro e; cases e)
                      obtain ⟨_, _, hA, _, _⟩ := hs.gen_pi
                      exact .app ht' (.conv hu hA hc)⟩
                  | isFalse _ => none
  | _, _, .ind i => if h : i < sg.length then some ⟨.sort .star, .ind h⟩ else none
  | Γ, hΓ, .ctor i k mask as =>
      match hc : sg.ctorArgs i k with
      | none => none
      | some c =>
          if hm : mask = c.mask ∧ as.isList = true ∧ as.toList.length = c.length then
            match checkArgs hsg Γ hΓ as (c.map (argTy i)) (argTys_sorted hsg hc) with
            | some ⟨ha⟩ => some ⟨.ind i, .ctor hc hm.1 hm.2.1 hm.2.2 (fun j hj => by
                have := ha j (by simpa using hj)
                rwa [getD_argTy hj] at this)⟩
            | none => none
          else none
  | Γ, hΓ, .elim i C bs t =>
      match hm : sg.numCtors i with
      | none => none
      | some m =>
          match infer hsg Γ hΓ C with
          | none => none
          | some ⟨_, hC⟩ =>
              match sortOf hsg hΓ hC with
              | some ⟨.star, hC'⟩ =>
                  match infer hsg Γ hΓ t with
                  | none => none
                  | some ⟨_, ht⟩ =>
                      match indOf hsg hΓ ht i (Sig.numCtors_eq hm).1 with
                      | none => none
                      | some ⟨ht'⟩ =>
                          if hl : bs.isList = true ∧ bs.toList.length = m then
                            match checkArgs hsg Γ hΓ bs ((sg.ctorsOf i).map (branchTy i · C))
                                (branchTys_sorted hsg hC') with
                            | some ⟨hb⟩ => some ⟨C, .elim hm hC' hl.1 hl.2 (fun k c hc => by
                                have := hb k (by simpa using ctorArgs_lt_ctorsOf hc)
                                rwa [getD_branchTy hc] at this)
                                (fun _ _ hc _ ho => hsg.argTy hc ho) ht'⟩
                            | none => none
                          else none
              | _ => none
  | _, _, .tnil => none
  | _, _, .tcons _ _ => none

/-- **Check a list of terms against a list of types**, each of which is a type. -/
def checkArgs (hsg : WfSig sg) (Γ : Ctx) (hΓ : Wf sg Γ) : (l : Tm) → (tys : List Tm) →
    (∀ T ∈ tys, ∃ s, HasType sg Γ T (.sort s)) →
    Option (PLift (∀ j < tys.length, HasType sg Γ (l.nth j) (tys.getD j (.sort .star))))
  | .tcons a l, T :: tys, hT =>
      match infer hsg Γ hΓ a with
      | none => none
      | some ⟨U, hU⟩ =>
          have hsT : SN Step T := by
            obtain ⟨s, hs⟩ := hT T (by simp)
            exact hs.sn hsg hΓ
          match Conv.decide U T (hU.sn_type hsg hΓ) hsT with
          | isFalse _ => none
          | isTrue hc =>
              match checkArgs hsg Γ hΓ l tys (fun T' hT' => hT T' (by simp [hT'])) with
              | none => none
              | some ⟨hrest⟩ => some ⟨fun j hj => by
                  cases j with
                  | zero =>
                      obtain ⟨s, hs⟩ := hT T (by simp)
                      exact .conv hU hs hc
                  | succ j => simpa using hrest j (by simpa using hj)⟩
  | .tnil, [], _ => some ⟨fun j hj => absurd hj (by simp)⟩
  | _, _, _ => none

end

/-! ## Completeness -/

mutual

/-- **Completeness**: a typable term gets a type. -/
theorem infer_complete (hsg : WfSig sg) : ∀ {t : Tm} {Γ : Ctx} (hΓ : Wf sg Γ) {T : Tm},
    HasType sg Γ t T → (infer hsg Γ hΓ t).isSome
  | .sort s, _, _, _, h => by
      obtain ⟨rfl, _⟩ := h.gen_sort
      rfl
  | .var n, Γ, _, _, h => by
      obtain ⟨A, hA, _⟩ := h.gen_var
      simp only [infer]
      split
      · rfl
      · rename_i heq; rw [hA] at heq; cases heq
  | .pi A B, Γ, hΓ, _, h => by
      obtain ⟨s₁, s₂, hA, hB, _⟩ := h.gen_pi
      obtain ⟨⟨_, hTA⟩, eA⟩ := Option.isSome_iff_exists.mp (infer_complete hsg hΓ hA)
      obtain ⟨hA', eA'⟩ := sortOf_spec hsg hΓ hTA hA
      obtain ⟨⟨_, hTB⟩, eB⟩ := Option.isSome_iff_exists.mp (infer_complete hsg (hΓ.cons hA') hB)
      obtain ⟨_, eB'⟩ := sortOf_spec hsg (hΓ.cons hA') hTB hB
      simp only [infer, eA, eA', eB, eB']
      rfl
  | .lam A t, Γ, hΓ, _, h => by
      obtain ⟨B, s₁, s₂, hA, ht, hB, _⟩ := h.gen_lam
      obtain ⟨⟨_, hTA⟩, eA⟩ := Option.isSome_iff_exists.mp (infer_complete hsg hΓ hA)
      obtain ⟨hA', eA'⟩ := sortOf_spec hsg hΓ hTA hA
      obtain ⟨⟨B', hB'⟩, et⟩ := Option.isSome_iff_exists.mp (infer_complete hsg (hΓ.cons hA') ht)
      have hne : B' ≠ .sort .box := by
        intro e
        subst e
        exact hB.not_conv_box (hΓ.cons hA) (hB'.unique ht).symm
      simp only [infer, eA, eA', et, dif_neg hne]
      rfl
  | .app t u, Γ, hΓ, _, h => by
      obtain ⟨A, B, ht, hu, _⟩ := h.gen_app
      obtain ⟨⟨T', hT'⟩, et⟩ := Option.isSome_iff_exists.mp (infer_complete hsg hΓ ht)
      obtain ⟨⟨⟨A', B'⟩, h'⟩, epi, hAA, _⟩ := piOf_spec hsg hΓ hT' (hT'.unique ht)
      obtain ⟨⟨U, hU⟩, eu⟩ := Option.isSome_iff_exists.mp (infer_complete hsg hΓ hu)
      have hc : Conv U A' := (hU.unique hu).trans hAA
      simp only [infer, et, epi, eu]
      split
      · rfl
      · rename_i hn _; exact (hn hc).elim
  | .ind i, _, _, _, h => by
      obtain ⟨hi, _⟩ := h.gen_ind
      simp [infer, hi]
  | .ctor i k mask as, Γ, hΓ, _, h => by
      obtain ⟨c, hc, hm, hl, hlen, has, _⟩ := h.gen_ctor
      have hca := checkArgs_complete hsg Γ hΓ as (c.map (argTy i)) (argTys_sorted hsg hc) hl
        (by simpa using hlen) (fun j hj => by
          have hj' : j < c.length := by simpa using hj
          rw [getD_argTy hj']
          exact has j hj')
      obtain ⟨⟨ha⟩, eca⟩ := Option.isSome_iff_exists.mp hca
      simp only [infer]
      split
      · rename_i hc'; rw [hc] at hc'; cases hc'
      · rename_i c' hc'
        rw [hc] at hc'
        cases hc'
        rw [dif_pos ⟨hm, hl, hlen⟩]
        split
        · rfl
        · rename_i heq; rw [eca] at heq; cases heq
  | .elim i C bs t, Γ, hΓ, _, h => by
      obtain ⟨m, hm, hC, hl, hlen, hb, _, ht, _⟩ := h.gen_elim
      obtain ⟨⟨_, hTC⟩, eC⟩ := Option.isSome_iff_exists.mp (infer_complete hsg hΓ hC)
      obtain ⟨hC'', eC'⟩ := sortOf_spec hsg hΓ hTC hC
      obtain ⟨⟨_, hTt⟩, et⟩ := Option.isSome_iff_exists.mp (infer_complete hsg hΓ ht)
      obtain ⟨⟨ht'⟩, eind⟩ := Option.isSome_iff_exists.mp
        (indOf_isSome hsg hΓ hTt (Sig.numCtors_eq hm).1 ht)
      have hcb := checkArgs_complete hsg Γ hΓ bs ((sg.ctorsOf i).map (branchTy i · C))
        (branchTys_sorted hsg hC'') hl (by simp [hlen, (Sig.numCtors_eq hm).2]) (fun k hk => by
          have hk' : k < (sg.ctorsOf i).length := by simpa using hk
          obtain ⟨c, hc⟩ : ∃ c, sg.ctorArgs i k = some c :=
            ⟨_, Sig.ctorArgs_iff.mpr (List.getElem?_eq_getElem hk')⟩
          rw [getD_branchTy hc]
          exact hb k c hc)
      obtain ⟨⟨hb'⟩, ecb⟩ := Option.isSome_iff_exists.mp hcb
      simp only [infer]
      split
      · rename_i hm'; rw [hm] at hm'; cases hm'
      · rename_i m' hm'
        rw [hm] at hm'
        cases hm'
        simp only [eC, eC', et, eind, dif_pos (And.intro hl hlen), ecb]
        rfl
  | .tnil, _, _, _, h => absurd rfl h.not_list.1
  | .tcons _ _, _, _, _, h => absurd rfl (h.not_list.2 _ _)

/-- **`checkArgs` is complete**: a list typed pointwise passes. -/
theorem checkArgs_complete (hsg : WfSig sg) (Γ : Ctx) (hΓ : Wf sg Γ) :
    ∀ (l : Tm) (tys : List Tm) (hT : ∀ T ∈ tys, ∃ s, HasType sg Γ T (.sort s)),
      l.isList = true → l.toList.length = tys.length →
      (∀ j < tys.length, HasType sg Γ (l.nth j) (tys.getD j (.sort .star))) →
      (checkArgs hsg Γ hΓ l tys hT).isSome
  | .tnil, [], _, _, _, _ => rfl
  | .tcons a l, T :: tys, hT, hl, hlen, h => by
      have ha := h 0 (by simp)
      simp only [Tm.nth_tcons_zero, List.getD_cons_zero] at ha
      obtain ⟨⟨U, hU⟩, ea⟩ := Option.isSome_iff_exists.mp (infer_complete hsg hΓ ha)
      have hrest := checkArgs_complete hsg Γ hΓ l tys (fun T' hT' => hT T' (by simp [hT'])) hl
        (by simpa [Tm.toList] using hlen) (fun j hj => by
          simpa using h (j + 1) (by simp; omega))
      obtain ⟨⟨hr⟩, er⟩ := Option.isSome_iff_exists.mp hrest
      have hc : Conv U T := hU.unique ha
      simp only [checkArgs, ea]
      split
      · rename_i hn _; exact (hn hc).elim
      · simp only [er]
        rfl
  | .tnil, _ :: _, _, _, hlen, _ => by simp [Tm.toList] at hlen
  | .tcons _ _, [], _, _, hlen, _ => by simp [Tm.toList] at hlen
  | .var _, _, _, hl, _, _ => by simp [Tm.isList] at hl
  | .sort _, _, _, hl, _, _ => by simp [Tm.isList] at hl
  | .pi _ _, _, _, hl, _, _ => by simp [Tm.isList] at hl
  | .lam _ _, _, _, hl, _, _ => by simp [Tm.isList] at hl
  | .app _ _, _, _, hl, _, _ => by simp [Tm.isList] at hl
  | .ind _, _, _, hl, _, _ => by simp [Tm.isList] at hl
  | .ctor _ _ _ _, _, _, hl, _, _ => by simp [Tm.isList] at hl
  | .elim _ _ _ _, _, _, hl, _, _ => by simp [Tm.isList] at hl

end

/-! ## Deciding the judgement -/

/-- **`Γ ⊢ t : T` is decidable** in a valid context over a valid signature. -/
def decHasType (hsg : WfSig sg) (Γ : Ctx) (hΓ : Wf sg Γ) (t T : Tm) :
    Decidable (HasType sg Γ t T) :=
  match hi : infer hsg Γ hΓ t with
  | none => isFalse (fun h => by have := infer_complete hsg hΓ h; rw [hi] at this; cases this)
  | some ⟨U, hU⟩ =>
      if hb : T = .sort .box then
        if hU' : U = .sort .box then isTrue (hb ▸ hU' ▸ hU)
        else isFalse (fun h => by
          subst hb
          obtain ⟨s, hs⟩ := (hU.correct hΓ).resolve_left hU'
          exact hs.not_conv_box hΓ (hU.unique h))
      else
        match hT : infer hsg Γ hΓ T with
        | none => isFalse (fun h => by
            obtain ⟨s, hs⟩ := (h.correct hΓ).resolve_left hb
            have := infer_complete hsg hΓ hs
            rw [hT] at this
            cases this)
        | some ⟨_, hTT⟩ =>
            match hs : sortOf hsg hΓ hTT with
            | none => isFalse (fun h => by
                obtain ⟨s, hs'⟩ := (h.correct hΓ).resolve_left hb
                obtain ⟨_, e⟩ := sortOf_spec hsg hΓ hTT hs'
                rw [hs] at e
                cases e)
            | some ⟨_, hTs⟩ =>
                match Conv.decide U T (hU.sn_type hsg hΓ) (hTs.sn hsg hΓ) with
                | isTrue hc => isTrue (.conv hU hTs hc)
                | isFalse hn => isFalse (fun h => hn (hU.unique h))

end LambdaLab.Languages.CoIC.DeBruijn
