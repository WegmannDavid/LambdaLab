import LambdaLab.Languages.ECC.DeBruijn.Eval

/-!
# ECC — the type checker

`infer Γ hΓ t` computes a type of `t` in the valid context `Γ`, or fails. Where a rule needs a type
to have a shape — a sort, for a domain; a product, for a function — the type is **normalized** and
the shape read off the normal form (`sortOf`, `piOf`), and where it needs one type to be a subtype
of another, their normal forms are compared (`subB`).

* **Soundness is by construction**: `infer` returns a type together with its derivation, and
  `check` a derivation. Nothing about normalization is assumed for that.
* **Completeness** (`infer_complete`, `check_complete`) holds if ECC normalizes (`Normalizing`):
  then every typable term gets a type, and the type `infer` finds is its **least** type —
  a subtype of every other (`Sub P T`). That is the *principal type* that replaces CoC's
  uniqueness of types: with cumulativity a term has many types, `Prop : Type 0` and also
  `Prop : Type 1`, but one of them is below all the others.

Without the hypothesis, completeness can only fail by divergence: the checker never rejects a
typable term, it may at worst not return.
-/

namespace LambdaLab.Languages.ECC.DeBruijn

open LambdaLab (SN)

/-! ## Reading shapes off a type -/

/-- **Read a sort off the type `T` of `A`**: `T`'s normal form, if it is a sort. -/
def sortOf {Γ : Ctx} {A T : Tm} (h : HasType Γ A T) : Option {s : Srt // HasType Γ A (.sort s)} :=
  match he : T.eval with
  | some (.sort s) => some ⟨s, .cumul h .sort (Conv.ofRed (Tm.eval_sound he).1).toSub⟩
  | _ => none

/-- If `T` is below a sort and normalizes, `sortOf` finds a sort below it. -/
theorem sortOf_spec (hsn : Normalizing) {Γ : Ctx} (hΓ : Wf Γ) {A T : Tm} (h : HasType Γ A T)
    {s : Srt} (hs : Sub T (.sort s)) :
    ∃ s', (sortOf h).map Subtype.val = some s' ∧ s'.le s := by
  obtain ⟨s', hr, hle⟩ := hs.to_sort
  obtain ⟨_, hT⟩ := h.correct hΓ
  obtain ⟨v, hv⟩ := Tm.eval_of_sn (hsn hΓ hT)
  obtain ⟨hrv, hnv⟩ := Tm.eval_sound hv
  have e : v = .sort s' := Red.normal_unique hrv hr hnv (fun _ hs => nomatch hs)
  subst e
  refine ⟨s', ?_, hle⟩
  unfold sortOf
  split
  · rename_i s'' _ he
    rw [hv] at he
    cases he
    rfl
  · rename_i hne
    exact (hne s' hv).elim

/-- **Read a product off the type `T` of `t`**: `T`'s normal form, if it is a product. -/
def piOf {Γ : Ctx} (hΓ : Wf Γ) {t T : Tm} (h : HasType Γ t T) :
    Option {AB : Tm × Tm // HasType Γ t (.pi AB.1 AB.2)} :=
  match he : T.eval with
  | some (.pi A B) => some ⟨(A, B), by
      obtain ⟨s, hs⟩ := h.correct hΓ
      have hr := (Tm.eval_sound he).1
      exact .cumul h (hs.preservation_red hΓ hr) (Conv.ofRed hr).toSub⟩
  | _ => none

/-- If `T` is below a product and normalizes, `piOf` finds a product below it. -/
theorem piOf_spec (hsn : Normalizing) {Γ : Ctx} (hΓ : Wf Γ) {t T A B : Tm} (h : HasType Γ t T)
    (hs : Sub T (.pi A B)) :
    ∃ A' B', (piOf hΓ h).map Subtype.val = some (A', B') ∧ Conv A' A ∧ Sub B' B := by
  obtain ⟨A₀, B₀, hr, hA₀, hB₀⟩ := hs.to_pi
  obtain ⟨_, hT⟩ := h.correct hΓ
  obtain ⟨v, hv⟩ := Tm.eval_of_sn (hsn hΓ hT)
  obtain ⟨hrv, hnv⟩ := Tm.eval_sound hv
  obtain ⟨A', B', rfl, hA', hB'⟩ := Red.pi_inv (Red.to_normal hrv hnv hr)
  refine ⟨A', B', ?_, (Conv.ofRed hA').symm.trans hA₀, Sub.conv_left (Conv.ofRed hB').symm hB₀⟩
  unfold piOf
  split
  · rename_i A'' B'' _ he
    rw [hv] at he
    cases he
    rfl
  · rename_i hne
    exact (hne A' B' hv).elim

/-! ## Inference -/

/-- **Type inference**, in a valid context. Returns the type with its derivation. -/
def infer : (Γ : Ctx) → Wf Γ → (t : Tm) → Option {T : Tm // HasType Γ t T}
  | _, _, .sort s => some ⟨.sort s.succ, .sort⟩
  | Γ, _, .var n =>
      match h : Γ.lookup n with
      | some A => some ⟨A, .var h⟩
      | none => none
  | Γ, hΓ, .pi A B =>
      match infer Γ hΓ A with
      | none => none
      | some ⟨_, hA⟩ =>
          match sortOf hA with
          | none => none
          | some ⟨s₁, hA'⟩ =>
              match infer (A :: Γ) (hΓ.cons hA') B with
              | none => none
              | some ⟨_, hB⟩ =>
                  match sortOf hB with
                  | none => none
                  | some ⟨s₂, hB'⟩ => some ⟨.sort (s₁.pi s₂), .pi hA' hB'⟩
  | Γ, hΓ, .lam A t =>
      match infer Γ hΓ A with
      | none => none
      | some ⟨_, hA⟩ =>
          match sortOf hA with
          | none => none
          | some ⟨_, hA'⟩ =>
              match infer (A :: Γ) (hΓ.cons hA') t with
              | none => none
              | some ⟨B, ht⟩ => some ⟨.pi A B, by
                  obtain ⟨s, hs⟩ := ht.correct (hΓ.cons hA')
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
                  if hs : subB U A then some ⟨B.inst u, by
                    obtain ⟨_, hP⟩ := ht'.correct hΓ
                    obtain ⟨_, _, hA, _, _⟩ := hP.gen_pi
                    exact .app ht' (.cumul hu hA (subB_sound hs))⟩
                  else none

/-- **Completeness, and principality**: if ECC normalizes, a typable term gets a type, and it is
below every type the term has. -/
theorem infer_complete (hsn : Normalizing) : ∀ {t : Tm} {Γ : Ctx} (hΓ : Wf Γ) {T : Tm},
    HasType Γ t T → ∃ P, (infer Γ hΓ t).map Subtype.val = some P ∧ Sub P T
  | .sort _, _, _, _, h => ⟨_, rfl, h.gen_sort⟩
  | .var n, Γ, _, _, h => by
      obtain ⟨A, hA, hs⟩ := h.gen_var
      simp only [infer]
      split
      · rename_i A' hA'
        rw [hA] at hA'
        cases hA'
        exact ⟨_, rfl, hs⟩
      · rename_i heq
        rw [hA] at heq
        cases heq
  | .pi A B, Γ, hΓ, _, h => by
      obtain ⟨s₁, s₂, hA, hB, hs⟩ := h.gen_pi
      obtain ⟨_, e₀, sA⟩ := infer_complete hsn hΓ hA
      obtain ⟨⟨_, hPA⟩, eA, rfl⟩ := Option.map_eq_some_iff.mp e₀
      obtain ⟨_, e₁, le₁⟩ := sortOf_spec hsn hΓ hPA sA
      obtain ⟨⟨_, hA'⟩, eA', rfl⟩ := Option.map_eq_some_iff.mp e₁
      obtain ⟨_, e₂, sB⟩ := infer_complete hsn (hΓ.cons hA') hB
      obtain ⟨⟨_, hPB⟩, eB, rfl⟩ := Option.map_eq_some_iff.mp e₂
      obtain ⟨_, e₃, le₂⟩ := sortOf_spec hsn (hΓ.cons hA') hPB sB
      obtain ⟨⟨_, _⟩, eB', rfl⟩ := Option.map_eq_some_iff.mp e₃
      simp only [infer, eA, eA', eB, eB']
      exact ⟨_, rfl, (Sub.sort (Srt.pi_mono le₁ le₂)).trans hs⟩
  | .lam A t, Γ, hΓ, _, h => by
      obtain ⟨B, s₁, s₂, hA, ht, hB, hs⟩ := h.gen_lam
      obtain ⟨_, e₀, sA⟩ := infer_complete hsn hΓ hA
      obtain ⟨⟨_, hPA⟩, eA, rfl⟩ := Option.map_eq_some_iff.mp e₀
      obtain ⟨_, e₁, _⟩ := sortOf_spec hsn hΓ hPA sA
      obtain ⟨⟨_, hA'⟩, eA', rfl⟩ := Option.map_eq_some_iff.mp e₁
      obtain ⟨_, e₂, st⟩ := infer_complete hsn (hΓ.cons hA') ht
      obtain ⟨⟨_, _⟩, et, rfl⟩ := Option.map_eq_some_iff.mp e₂
      simp only [infer, eA, eA', et]
      exact ⟨_, rfl, (Sub.pi (Conv.refl _) st).trans hs⟩
  | .app t u, Γ, hΓ, _, h => by
      obtain ⟨A, B, ht, hu, hs⟩ := h.gen_app
      obtain ⟨_, e₀, st⟩ := infer_complete hsn hΓ ht
      obtain ⟨⟨_, hPt⟩, et, rfl⟩ := Option.map_eq_some_iff.mp e₀
      obtain ⟨A', B', e₁, hAA, hBB⟩ := piOf_spec hsn hΓ hPt st
      obtain ⟨⟨_, ht'⟩, epi, rfl⟩ := Option.map_eq_some_iff.mp e₁
      obtain ⟨_, e₂, su⟩ := infer_complete hsn hΓ hu
      obtain ⟨⟨Pu, hPu⟩, eu, rfl⟩ := Option.map_eq_some_iff.mp e₂
      have hsnPu : SN Step Pu := by
        obtain ⟨_, hP⟩ := hPu.correct hΓ
        exact hsn hΓ hP
      have hsnA' : SN Step A' := by
        obtain ⟨_, hP⟩ := ht'.correct hΓ
        obtain ⟨_, _, hA', _, _⟩ := hP.gen_pi
        exact hsn hΓ hA'
      have hb := subB_complete hsnPu hsnA' (su.trans hAA.symm.toSub)
      simp only [infer, et, epi, eu, hb, dite_true]
      exact ⟨_, rfl, (hBB.subst _).trans hs⟩

/-! ## Checking -/

/-- **Check `t : T`**: infer the least type of `t`, check that `T` is a type, and compare. -/
def check (Γ : Ctx) (hΓ : Wf Γ) (t T : Tm) : Option (PLift (HasType Γ t T)) :=
  match infer Γ hΓ t, infer Γ hΓ T with
  | some ⟨U, hU⟩, some ⟨_, hT⟩ =>
      match sortOf hT with
      | some ⟨_, hT'⟩ => if hs : subB U T then some ⟨.cumul hU hT' (subB_sound hs)⟩ else none
      | none => none
  | _, _ => none

/-- **The checker is sound**: what it accepts is derivable. -/
theorem check_sound {Γ : Ctx} {hΓ : Wf Γ} {t T : Tm} {p : PLift (HasType Γ t T)}
    (_ : check Γ hΓ t T = some p) : HasType Γ t T :=
  p.down

/-- **The checker is complete**, if ECC normalizes. -/
theorem check_complete (hsn : Normalizing) {Γ : Ctx} (hΓ : Wf Γ) {t T : Tm}
    (h : HasType Γ t T) : (check Γ hΓ t T).isSome := by
  obtain ⟨_, e₀, st⟩ := infer_complete hsn hΓ h
  obtain ⟨⟨U, hU⟩, et, rfl⟩ := Option.map_eq_some_iff.mp e₀
  obtain ⟨s, hT⟩ := h.correct hΓ
  obtain ⟨_, e₂, sT⟩ := infer_complete hsn hΓ hT
  obtain ⟨⟨_, hPT⟩, eT, rfl⟩ := Option.map_eq_some_iff.mp e₂
  obtain ⟨_, e₁, _⟩ := sortOf_spec hsn hΓ hPT sT
  obtain ⟨⟨_, _⟩, eT', rfl⟩ := Option.map_eq_some_iff.mp e₁
  have hsnU : SN Step U := by
    obtain ⟨_, hP⟩ := hU.correct hΓ
    exact hsn hΓ hP
  have hb := subB_complete hsnU (hsn hΓ hT) st
  simp only [check, et, eT, eT', hb, dite_true]
  rfl

end LambdaLab.Languages.ECC.DeBruijn
