import LambdaLab.Languages.CoIC.DeBruijn.Eval

/-!
# CoC — the type checker, sound and complete

`infer Γ hΓ t` computes a type of `t` in the valid context `Γ`, or fails. Unlike System F's, it
cannot compare types syntactically: `t : (λ X : * . X) A` and `t : A` are the same judgement. So
where a rule needs a type to have a shape — a sort, for a domain; a product, for a function — the
type is **normalized** and the shape read off the normal form (`sortOf`, `piOf`), and where it
needs two types to agree, their normal forms are compared (`Conv.decide`). Normalizing is total
because what is normalized is a type, hence strongly normalizing (`HasType.sn_type`).

* **Soundness is by construction**: `infer` returns a type together with its derivation.
* **Completeness** (`infer_complete`): if `t` has a type at all, `infer` finds one — by induction
  on `t`, through the generation lemmas and uniqueness of types.

Together they decide the judgement (`decHasType`): to check `t : T`, infer a type of `t` and
compare it with `T` — which must itself be `□` or sorted.
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

open LambdaLab (SN)

/-! ## Reading shapes off a type -/

/-- **Read a sort off the type of `A`.** -/
def sortOf {Γ : Ctx} (hΓ : Wf Γ) {A T : Tm} (h : HasType Γ A T) :
    Option {s : Srt // HasType Γ A (.sort s)} :=
  if hb : T = .sort .box then some ⟨.box, hb ▸ h⟩
  else if he : T.eval (h.sn_type hΓ) = .sort .star then
    some ⟨.star, .conv h .sort (by
      have := (Tm.eval_spec (h.sn_type hΓ)).1
      rw [he] at this
      exact Conv.ofRed this)⟩
  else none

/-- If `A` is sorted at all, `sortOf` finds the sort. -/
theorem sortOf_isSome {Γ : Ctx} (hΓ : Wf Γ) {A T : Tm} (h : HasType Γ A T) {s : Srt}
    (hs : HasType Γ A (.sort s)) : (sortOf hΓ h).isSome := by
  unfold sortOf
  by_cases hb : T = .sort .box
  · rw [dif_pos hb]; rfl
  · rw [dif_neg hb]
    have hc := h.unique hs
    cases s with
    | box =>
        obtain ⟨s', hs'⟩ := (h.correct hΓ).resolve_left hb
        exact (hs'.not_conv_box hΓ hc).elim
    | star => rw [dif_pos (Tm.eval_sort _ hc)]; rfl

/-- **Read a product off the type of `t`.** -/
def piOf {Γ : Ctx} (hΓ : Wf Γ) {t T : Tm} (h : HasType Γ t T) :
    Option {AB : Tm × Tm // HasType Γ t (.pi AB.1 AB.2)} :=
  if hb : T = .sort .box then none
  else
    match he : T.eval (h.sn_type hΓ) with
    | .pi A B => some ⟨(A, B), by
        obtain ⟨s, hs⟩ := (h.correct hΓ).resolve_left hb
        have hr := (Tm.eval_spec (h.sn_type hΓ)).1
        rw [he] at hr
        exact .conv h (hs.preservation_red hΓ hr) (Conv.ofRed hr)⟩
    | _ => none

/-- If the type of `t` is convertible to a product, `piOf` finds a convertible product. -/
theorem piOf_spec {Γ : Ctx} (hΓ : Wf Γ) {t T A B : Tm} (h : HasType Γ t T)
    (hc : Conv T (.pi A B)) :
    ∃ p, piOf hΓ h = some p ∧ Conv A p.1.1 ∧ Conv B p.1.2 := by
  have hb : T ≠ .sort .box := fun e => by subst e; exact Conv.sort_pi hc
  obtain ⟨A', B', he, hA, hB⟩ := Tm.eval_pi (h.sn_type hΓ) hc
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

/-! ## Inference -/

/-- **Type inference**, in a valid context. Returns the type with its derivation. -/
def infer : (Γ : Ctx) → Wf Γ → (t : Tm) → Option {T : Tm // HasType Γ t T}
  | _, _, .sort .star => some ⟨.sort .box, .sort⟩
  | _, _, .sort .box => none
  | Γ, _, .var n =>
      match h : Γ.lookup n with
      | some A => some ⟨A, .var h⟩
      | none => none
  | Γ, hΓ, .pi A B =>
      match infer Γ hΓ A with
      | none => none
      | some ⟨_, hA⟩ =>
          match sortOf hΓ hA with
          | none => none
          | some ⟨_, hA'⟩ =>
              match infer (A :: Γ) (hΓ.cons hA') B with
              | none => none
              | some ⟨_, hB⟩ =>
                  match sortOf (hΓ.cons hA') hB with
                  | none => none
                  | some ⟨s₂, hB'⟩ => some ⟨.sort s₂, .pi hA' hB'⟩
  | Γ, hΓ, .lam A t =>
      match infer Γ hΓ A with
      | none => none
      | some ⟨_, hA⟩ =>
          match sortOf hΓ hA with
          | none => none
          | some ⟨_, hA'⟩ =>
              match infer (A :: Γ) (hΓ.cons hA') t with
              | none => none
              | some ⟨B, ht⟩ =>
                  if hb : B = .sort .box then none
                  else some ⟨.pi A B, by
                    obtain ⟨s, hs⟩ := (ht.correct (hΓ.cons hA')).resolve_left hb
                    exact .lam hA' ht hs⟩
  | Γ, hΓ, .app t u =>
      match infer Γ hΓ t with
      | none => none
      | some ⟨_, ht⟩ =>
          match piOf hΓ ht with
          | none => none
          | some ⟨(A, B), ht'⟩ =>
              match infer Γ hΓ u with
              | none => none
              | some ⟨U, hu⟩ =>
                  have hsA : SN Step A := by
                    obtain ⟨s, hs⟩ := (ht'.correct hΓ).resolve_left (by intro e; cases e)
                    obtain ⟨_, _, hA, _, _⟩ := hs.gen_pi
                    exact hA.sn hΓ
                  match Conv.decide U A (hu.sn_type hΓ) hsA with
                  | isTrue hc => some ⟨B.inst u, by
                      obtain ⟨s, hs⟩ := (ht'.correct hΓ).resolve_left (by intro e; cases e)
                      obtain ⟨_, _, hA, _, _⟩ := hs.gen_pi
                      exact .app ht' (.conv hu hA hc)⟩
                  | isFalse _ => none

/-- **Completeness**: a typable term gets a type. -/
theorem infer_complete : ∀ {t : Tm} {Γ : Ctx} (hΓ : Wf Γ) {T : Tm}, HasType Γ t T →
    (infer Γ hΓ t).isSome
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
      obtain ⟨⟨_, hTA⟩, eA⟩ := Option.isSome_iff_exists.mp (infer_complete hΓ hA)
      obtain ⟨⟨_, hA'⟩, eA'⟩ := Option.isSome_iff_exists.mp (sortOf_isSome hΓ hTA hA)
      obtain ⟨⟨_, hTB⟩, eB⟩ := Option.isSome_iff_exists.mp (infer_complete (hΓ.cons hA') hB)
      obtain ⟨⟨_, _⟩, eB'⟩ := Option.isSome_iff_exists.mp (sortOf_isSome (hΓ.cons hA') hTB hB)
      simp only [infer, eA, eA', eB, eB']
      rfl
  | .lam A t, Γ, hΓ, _, h => by
      obtain ⟨B, s₁, s₂, hA, ht, hB, _⟩ := h.gen_lam
      obtain ⟨⟨_, hTA⟩, eA⟩ := Option.isSome_iff_exists.mp (infer_complete hΓ hA)
      obtain ⟨⟨_, hA'⟩, eA'⟩ := Option.isSome_iff_exists.mp (sortOf_isSome hΓ hTA hA)
      obtain ⟨⟨B', hB'⟩, et⟩ := Option.isSome_iff_exists.mp (infer_complete (hΓ.cons hA') ht)
      have hne : B' ≠ .sort .box := by
        intro e
        subst e
        exact hB.not_conv_box (hΓ.cons hA) (hB'.unique ht).symm
      simp only [infer, eA, eA', et, dif_neg hne]
      rfl
  | .app t u, Γ, hΓ, _, h => by
      obtain ⟨A, B, ht, hu, _⟩ := h.gen_app
      obtain ⟨⟨T', hT'⟩, et⟩ := Option.isSome_iff_exists.mp (infer_complete hΓ ht)
      obtain ⟨⟨⟨A', B'⟩, h'⟩, epi, hAA, _⟩ := piOf_spec hΓ hT' (hT'.unique ht)
      obtain ⟨⟨U, hU⟩, eu⟩ := Option.isSome_iff_exists.mp (infer_complete hΓ hu)
      have hc : Conv U A' := (hU.unique hu).trans hAA
      simp only [infer, et, epi, eu]
      split
      · rfl
      · rename_i hn _; exact (hn hc).elim

/-! ## Deciding the judgement -/

/-- **`Γ ⊢ t : T` is decidable** in a valid context. -/
def decHasType (Γ : Ctx) (hΓ : Wf Γ) (t T : Tm) : Decidable (HasType Γ t T) :=
  match hi : infer Γ hΓ t with
  | none => isFalse (fun h => by have := infer_complete hΓ h; rw [hi] at this; cases this)
  | some ⟨U, hU⟩ =>
      if hb : T = .sort .box then
        if hU' : U = .sort .box then isTrue (hb ▸ hU' ▸ hU)
        else isFalse (fun h => by
          subst hb
          obtain ⟨s, hs⟩ := (hU.correct hΓ).resolve_left hU'
          exact hs.not_conv_box hΓ (hU.unique h))
      else
        match hT : infer Γ hΓ T with
        | none => isFalse (fun h => by
            obtain ⟨s, hs⟩ := (h.correct hΓ).resolve_left hb
            have := infer_complete hΓ hs
            rw [hT] at this
            cases this)
        | some ⟨_, hTT⟩ =>
            match hs : sortOf hΓ hTT with
            | none => isFalse (fun h => by
                obtain ⟨s, hs'⟩ := (h.correct hΓ).resolve_left hb
                have := sortOf_isSome hΓ hTT hs'
                rw [hs] at this
                cases this)
            | some ⟨_, hTs⟩ =>
                match Conv.decide U T (hU.sn_type hΓ) (hTs.sn hΓ) with
                | isTrue hc => isTrue (.conv hU hTs hc)
                | isFalse hn => isFalse (fun h => hn (hU.unique h))

end LambdaLab.Languages.CoIC.DeBruijn
