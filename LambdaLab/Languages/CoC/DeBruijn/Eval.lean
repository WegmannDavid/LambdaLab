import LambdaLab.Languages.CoC.DeBruijn.Normalization

/-!
# CoC — the normalizer, and deciding conversion

`Tm.eval t h` reduces `t` to its normal form, given a proof `h` that `t` is strongly normalizing;
for a well-typed term that proof is `HasType.sn`. `findStep` picks a redex, leftmost-outermost,
by structural recursion, and the outer loop contracts it until none is left — total because every
reduct of a strongly normalizing term is strongly normalizing.

By confluence a term has at most one normal form (`Red.normal_unique`), so two normalizing terms
are convertible exactly when their normal forms are equal (`Tm.eval_eq_iff`). That is what makes
conversion — and with it type checking — decidable: compare normal forms. It is also what reads a
shape off a type: whatever is convertible to a product normalizes to a product (`Tm.eval_pi`), and
whatever is convertible to a sort normalizes to it (`Tm.eval_sort`).
-/

namespace LambdaLab.Languages.CoC.DeBruijn

open LambdaLab (SN RTC)

/-- **Find a redex**, leftmost-outermost, and contract it. -/
def Tm.findStep : (t : Tm) → Option ((t' : Tm) ×' Step t t')
  | .var _ => none
  | .sort _ => none
  | .pi A B =>
      match A.findStep with
      | some ⟨A', s⟩ => some ⟨.pi A' B, .piA s⟩
      | none =>
          match B.findStep with
          | some ⟨B', s⟩ => some ⟨.pi A B', .piB s⟩
          | none => none
  | .lam A t =>
      match A.findStep with
      | some ⟨A', s⟩ => some ⟨.lam A' t, .lamA s⟩
      | none =>
          match t.findStep with
          | some ⟨t', s⟩ => some ⟨.lam A t', .lamB s⟩
          | none => none
  | .app (.lam _ t) u => some ⟨t.inst u, .beta⟩
  | .app t u =>
      match t.findStep with
      | some ⟨t', s⟩ => some ⟨.app t' u, .appL s⟩
      | none =>
          match u.findStep with
          | some ⟨u', s⟩ => some ⟨.app t u', .appR s⟩
          | none => none

/-- A term is **normal** when it has no reduct. -/
def Tm.Normal (t : Tm) : Prop := ∀ w, ¬ Step t w

/-- `findStep` on an application whose head is not an abstraction. -/
theorem Tm.findStep_app_of_ne_lam {t u : Tm} (h : ∀ A b, t ≠ .lam A b) :
    (Tm.app t u).findStep =
      (match t.findStep with
        | some ⟨t', s⟩ => some ⟨.app t' u, .appL s⟩
        | none =>
            match u.findStep with
            | some ⟨u', s⟩ => some ⟨.app t u', .appR s⟩
            | none => none) := by
  cases t with
  | lam A b => exact absurd rfl (h A b)
  | _ => rfl

/-- **`findStep` misses no redex.** -/
theorem Step.findStep_isSome {t w : Tm} (h : Step t w) : t.findStep.isSome := by
  induction h with
  | beta => rfl
  | @appL t t' u _ ih =>
      by_cases hl : ∃ A b, t = .lam A b
      · obtain ⟨A, b, rfl⟩ := hl; rfl
      · rw [Tm.findStep_app_of_ne_lam (fun A b e => hl ⟨A, b, e⟩)]
        cases hf : t.findStep with
        | none => rw [hf] at ih; cases ih
        | some p => rfl
  | @appR t u u' _ ih =>
      by_cases hl : ∃ A b, t = .lam A b
      · obtain ⟨A, b, rfl⟩ := hl; rfl
      · rw [Tm.findStep_app_of_ne_lam (fun A b e => hl ⟨A, b, e⟩)]
        cases hf : t.findStep with
        | some p => rfl
        | none =>
            cases hf' : u.findStep with
            | none => rw [hf'] at ih; cases ih
            | some p => rfl
  | @lamA A A' t _ ih =>
      simp only [Tm.findStep]
      cases hf : A.findStep with
      | none => rw [hf] at ih; cases ih
      | some p => rfl
  | @lamB A t t' _ ih =>
      simp only [Tm.findStep]
      cases hf : A.findStep with
      | some p => rfl
      | none =>
          cases hf' : t.findStep with
          | none => rw [hf'] at ih; cases ih
          | some p => rfl
  | @piA A A' B _ ih =>
      simp only [Tm.findStep]
      cases hf : A.findStep with
      | none => rw [hf] at ih; cases ih
      | some p => rfl
  | @piB A B B' _ ih =>
      simp only [Tm.findStep]
      cases hf : A.findStep with
      | some p => rfl
      | none =>
          cases hf' : B.findStep with
          | none => rw [hf'] at ih; cases ih
          | some p => rfl

theorem Tm.normal_of_findStep {t : Tm} (h : t.findStep = none) : t.Normal := by
  intro w hw
  have := hw.findStep_isSome
  rw [h] at this
  cases this

/-- Strongly normalizing terms, ordered by reduction — the measure the loop descends. -/
abbrev SNTm := { t : Tm // SN Step t }

instance : WellFoundedRelation SNTm where
  rel := fun a b => Step b.val a.val
  wf := ⟨fun ⟨_, h⟩ => by
    induction h with
    | intro _ ih =>
        constructor
        intro ⟨e', _⟩ hs
        exact ih e' hs⟩

/-- **The normalizer**, total on strongly normalizing terms. -/
def Tm.eval (t : Tm) (h : SN Step t) : Tm :=
  match t.findStep with
  | none => t
  | some ⟨t', s⟩ => Tm.eval t' (h.unfold s)
termination_by (⟨t, h⟩ : SNTm)

/-- **What `eval` returns** is reached by reduction and is normal. -/
theorem Tm.eval_spec {t : Tm} (h : SN Step t) : Red t (t.eval h) ∧ (t.eval h).Normal := by
  induction h with
  | @intro t _ ih =>
      rw [Tm.eval]
      split
      · rename_i hf
        exact ⟨.refl, Tm.normal_of_findStep hf⟩
      · rename_i t' s _
        obtain ⟨hr, hn⟩ := ih t' s
        exact ⟨RTC.head s hr, hn⟩

/-- **A normal term evaluates to itself.** -/
theorem Tm.eval_of_normal {t : Tm} (h : SN Step t) (hn : t.Normal) : t.eval h = t := by
  rw [Tm.eval]
  split
  · rfl
  · rename_i t' s _
    exact absurd s (hn t')

/-! ## Normal forms are unique -/

theorem Tm.Normal.red_eq {t u : Tm} (hn : t.Normal) (hr : Red t u) : u = t := by
  induction hr with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs (hn _)

/-- **A term has at most one normal form.** -/
theorem Red.normal_unique {t a b : Tm} (ha : Red t a) (hb : Red t b) (hna : a.Normal)
    (hnb : b.Normal) : a = b := by
  obtain ⟨c, hac, hbc⟩ := Red.confluent ha hb
  rw [← hna.red_eq hac, ← hnb.red_eq hbc]

/-- **Two normalizing terms are convertible exactly when their normal forms are equal.** -/
theorem Tm.eval_eq_iff {a b : Tm} (ha : SN Step a) (hb : SN Step b) :
    a.eval ha = b.eval hb ↔ Conv a b := by
  obtain ⟨hra, hna⟩ := Tm.eval_spec ha
  obtain ⟨hrb, hnb⟩ := Tm.eval_spec hb
  constructor
  · intro e
    exact ⟨a.eval ha, hra, e ▸ hrb⟩
  · rintro ⟨c, hac, hbc⟩
    -- both normal forms are normal forms of the common reduct
    obtain ⟨d, had, hcd⟩ := Red.confluent hra hac
    obtain ⟨d', hbd', hcd'⟩ := Red.confluent hrb hbc
    rw [hna.red_eq had] at hcd
    rw [hnb.red_eq hbd'] at hcd'
    exact Red.normal_unique hcd hcd' hna hnb

/-- Convertibility of normalizing terms is decidable. -/
def Conv.decide (a b : Tm) (ha : SN Step a) (hb : SN Step b) : Decidable (Conv a b) :=
  decidable_of_iff _ (Tm.eval_eq_iff ha hb)

/-- What is convertible to a sort normalizes to it. -/
theorem Tm.eval_sort {t : Tm} {s : Srt} (h : SN Step t) (hc : Conv t (.sort s)) :
    t.eval h = .sort s :=
  (Tm.eval_eq_iff h (sn_sort s)).mpr hc |>.trans (Tm.eval_of_normal _ (fun _ hs => nomatch hs))

/-- What is convertible to a product normalizes to a product, with convertible components. -/
theorem Tm.eval_pi {t A B : Tm} (h : SN Step t) (hc : Conv t (.pi A B)) :
    ∃ A' B', t.eval h = .pi A' B' ∧ Conv A A' ∧ Conv B B' := by
  obtain ⟨hr, hn⟩ := Tm.eval_spec h
  obtain ⟨c, htc, hpc⟩ := hc
  obtain ⟨d, hd, hcd⟩ := Red.confluent hr htc
  rw [hn.red_eq hd] at hcd
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Red.pi_inv hpc
  obtain ⟨A', B', he, hA', hB'⟩ := Red.pi_inv hcd
  exact ⟨A', B', he, Conv.ofRed (hA₁.trans hA'), Conv.ofRed (hB₁.trans hB')⟩

/-! ## On well-typed terms -/

/-- A well-typed term's normal form. -/
def HasType.eval {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ) : Tm :=
  t.eval (h.sn hΓ)

/-- The normal form keeps the type. -/
theorem HasType.eval_typed {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ) :
    HasType Γ (h.eval hΓ) T :=
  h.preservation_red hΓ (Tm.eval_spec (h.sn hΓ)).1

/-- `eval` depends only on the term. -/
theorem Tm.eval_congr {t u : Tm} (e : t = u) (h : SN Step t) (h' : SN Step u) :
    t.eval h = u.eval h' := by
  subst e; rfl

end LambdaLab.Languages.CoC.DeBruijn
