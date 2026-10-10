import LambdaLab.Languages.SystemF.Normalization

/-!
# System F — the normalizer

`Tm.eval t h` reduces `t` to its normal form, given a proof `h` that `t` is strongly normalizing.
For a well-typed term that proof is `HasType.sn`, so `HasType.eval` needs nothing else — and
evaluation is total by proof, not by a step budget.

`findStep` picks a redex, leftmost-outermost, by structural recursion; the outer loop contracts
it until none is left, and terminates because every reduct of a strongly normalizing term is
strongly normalizing. What is proved about the result (`eval_spec`, `eval_of_normal`):

* it is reached from `t` by reduction, so it has `t`'s type (`HasType.eval_typed`);
* it is normal — `findStep` finds a redex whenever there is one (`Step.findStep_isSome`);
* a term that is already normal is its own result.
-/

namespace LambdaLab.Languages.SystemF

/-- **Find a redex**, leftmost-outermost, and contract it. -/
def Tm.findStep : (t : Tm) → Option ((t' : Tm) ×' Step t t')
  | .var _ => none
  | .lam A b =>
      match b.findStep with
      | some ⟨b', s⟩ => some ⟨.lam A b', .lam s⟩
      | none => none
  | .app (.lam _ b) u => some ⟨b.inst u, .beta⟩
  | .app t u =>
      match t.findStep with
      | some ⟨t', s⟩ => some ⟨.app t' u, .appL s⟩
      | none =>
          match u.findStep with
          | some ⟨u', s⟩ => some ⟨.app t u', .appR s⟩
          | none => none
  | .tlam b =>
      match b.findStep with
      | some ⟨b', s⟩ => some ⟨.tlam b', .tlam s⟩
      | none => none
  | .tapp (.tlam b) B => some ⟨b.tinst B, .tbeta⟩
  | .tapp t B =>
      match t.findStep with
      | some ⟨t', s⟩ => some ⟨.tapp t' B, .tappL s⟩
      | none => none

/-- A term is **normal** when it has no reduct. -/
def Tm.Normal (t : Tm) : Prop := ∀ w, ¬ Step t w

/-- **`findStep` misses no redex**: if the term reduces at all, it finds something. -/
theorem Step.findStep_isSome {t w : Tm} (h : Step t w) : t.findStep.isSome := by
  induction h with
  | beta => rfl
  | tbeta => rfl
  | @lam A b b' _ ih =>
      cases hb : b.findStep with
      | none => rw [hb] at ih; cases ih
      | some p => simp [Tm.findStep, hb]
  | @appL t t' u _ ih =>
      cases t with
      | lam => rfl
      | var => cases ih
      | app t₁ t₂ =>
          cases hf : (Tm.app t₁ t₂).findStep with
          | none => rw [hf] at ih; cases ih
          | some p => simp only [Tm.findStep] at hf ⊢; rw [hf]; rfl
      | tlam b =>
          cases hf : (Tm.tlam b).findStep with
          | none => rw [hf] at ih; cases ih
          | some p => simp only [Tm.findStep] at hf ⊢; rw [hf]; rfl
      | tapp t₁ B =>
          cases hf : (Tm.tapp t₁ B).findStep with
          | none => rw [hf] at ih; cases ih
          | some p => simp only [Tm.findStep] at hf ⊢; rw [hf]; rfl
  | @appR t u u' _ ih =>
      cases t with
      | lam => rfl
      | var n =>
          cases hf : u.findStep with
          | none => rw [hf] at ih; cases ih
          | some p => simp [Tm.findStep, hf]
      | app t₁ t₂ =>
          cases ht : (Tm.app t₁ t₂).findStep with
          | some p => simp only [Tm.findStep] at ht ⊢; rw [ht]; rfl
          | none =>
              cases hf : u.findStep with
              | none => rw [hf] at ih; cases ih
              | some p => simp only [Tm.findStep] at ht ⊢; rw [ht]; simp [hf]
      | tlam b =>
          cases ht : (Tm.tlam b).findStep with
          | some p => simp only [Tm.findStep] at ht ⊢; rw [ht]; rfl
          | none =>
              cases hf : u.findStep with
              | none => rw [hf] at ih; cases ih
              | some p => simp only [Tm.findStep] at ht ⊢; rw [ht]; simp [hf]
      | tapp t₁ B =>
          cases ht : (Tm.tapp t₁ B).findStep with
          | some p => simp only [Tm.findStep] at ht ⊢; rw [ht]; rfl
          | none =>
              cases hf : u.findStep with
              | none => rw [hf] at ih; cases ih
              | some p => simp only [Tm.findStep] at ht ⊢; rw [ht]; simp [hf]
  | @tlam b b' _ ih =>
      cases hb : b.findStep with
      | none => rw [hb] at ih; cases ih
      | some p => simp [Tm.findStep, hb]
  | @tappL t t' B _ ih =>
      cases t with
      | tlam => rfl
      | var => cases ih
      | lam A b =>
          cases hf : (Tm.lam A b).findStep with
          | none => rw [hf] at ih; cases ih
          | some p => simp only [Tm.findStep] at hf ⊢; rw [hf]; rfl
      | app t₁ t₂ =>
          cases hf : (Tm.app t₁ t₂).findStep with
          | none => rw [hf] at ih; cases ih
          | some p => simp only [Tm.findStep] at hf ⊢; rw [hf]; rfl
      | tapp t₁ B' =>
          cases hf : (Tm.tapp t₁ B').findStep with
          | none => rw [hf] at ih; cases ih
          | some p => simp only [Tm.findStep] at hf ⊢; rw [hf]; rfl

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
theorem Tm.eval_spec {t : Tm} (h : SN Step t) : RTC Step t (t.eval h) ∧ (t.eval h).Normal := by
  induction h with
  | @intro t hall ih =>
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

/-- A well-typed term's normal form. -/
def HasType.eval {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Δ Γ t A) : Tm :=
  t.eval h.sn

/-- The normal form keeps the type. -/
theorem HasType.eval_typed {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Δ Γ t A) :
    HasType Δ Γ h.eval A :=
  h.preservation_rtc (Tm.eval_spec h.sn).1

end LambdaLab.Languages.SystemF
