import LambdaLab.Languages.SystemF.Named.Typing

/-!
# System F, named — the normalizer

The named counterpart of `DeBruijn/Eval.lean`: `findStep` contracts the leftmost-outermost
redex, by capture-avoiding substitution, and `Tm.eval` repeats it until none is left —
terminating because the term is strongly normalizing, which for a well-typed term is
`HasType.sn`. The result is reached by reduction, is normal, keeps the type, and a normal term
is its own result.
-/

namespace LambdaLab.Languages.SystemF.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N]

/-- **Find a redex**, leftmost-outermost, and contract it. -/
def Tm.findStep : (t : Tm N) → Option ((t' : Tm N) ×' Step t t')
  | .var _ => none
  | .lam x A b =>
      match b.findStep with
      | some ⟨b', s⟩ => some ⟨.lam x A b', .lam s⟩
      | none => none
  | .app (.lam x _ b) u => some ⟨b.inst x u, .beta⟩
  | .app t u =>
      match t.findStep with
      | some ⟨t', s⟩ => some ⟨.app t' u, .appL s⟩
      | none =>
          match u.findStep with
          | some ⟨u', s⟩ => some ⟨.app t u', .appR s⟩
          | none => none
  | .tlam α b =>
      match b.findStep with
      | some ⟨b', s⟩ => some ⟨.tlam α b', .tlam s⟩
      | none => none
  | .tapp (.tlam α b) B => some ⟨b.tinst α B, .tbeta⟩
  | .tapp t B =>
      match t.findStep with
      | some ⟨t', s⟩ => some ⟨.tapp t' B, .tappL s⟩
      | none => none

/-- **`findStep` misses no redex.** -/
theorem Tm.normal_of_findStep : ∀ (t : Tm N), t.findStep = none → t.Normal
  | .var _, _ => fun _ hw => by cases hw
  | .lam x A b, h => by
      have hb : b.findStep = none := by
        cases hb : b.findStep with
        | none => rfl
        | some p => simp [Tm.findStep, hb] at h
      intro w hw
      cases hw with
      | lam hs => exact Tm.normal_of_findStep b hb _ hs
  | .tlam α b, h => by
      have hb : b.findStep = none := by
        cases hb : b.findStep with
        | none => rfl
        | some p => simp [Tm.findStep, hb] at h
      intro w hw
      cases hw with
      | tlam hs => exact Tm.normal_of_findStep b hb _ hs
  | .app t u, h => by
      cases t with
      | lam x A b => simp [Tm.findStep] at h
      | var y =>
          have hu : u.findStep = none := by
            cases hu : u.findStep with
            | none => rfl
            | some p => simp [Tm.findStep, hu] at h
          intro w hw
          cases hw with
          | appL hs => cases hs
          | appR hs => exact Tm.normal_of_findStep u hu _ hs
      | app t₁ t₂ =>
          have ht : (Tm.app t₁ t₂).findStep = none := by
            cases ht : (Tm.app t₁ t₂).findStep with
            | none => rfl
            | some p => simp only [Tm.findStep] at ht h; rw [ht] at h; cases h
          have hu : u.findStep = none := by
            cases hu : u.findStep with
            | none => rfl
            | some p => simp only [Tm.findStep] at ht h; rw [ht] at h; simp [hu] at h
          intro w hw
          cases hw with
          | appL hs => exact Tm.normal_of_findStep _ ht _ hs
          | appR hs => exact Tm.normal_of_findStep u hu _ hs
      | tlam α b =>
          have ht : (Tm.tlam α b).findStep = none := by
            cases ht : (Tm.tlam α b).findStep with
            | none => rfl
            | some p => simp only [Tm.findStep] at ht h; rw [ht] at h; cases h
          have hu : u.findStep = none := by
            cases hu : u.findStep with
            | none => rfl
            | some p => simp only [Tm.findStep] at ht h; rw [ht] at h; simp [hu] at h
          intro w hw
          cases hw with
          | appL hs => exact Tm.normal_of_findStep _ ht _ hs
          | appR hs => exact Tm.normal_of_findStep u hu _ hs
      | tapp t₁ B =>
          have ht : (Tm.tapp t₁ B).findStep = none := by
            cases ht : (Tm.tapp t₁ B).findStep with
            | none => rfl
            | some p => simp only [Tm.findStep] at ht h; rw [ht] at h; cases h
          have hu : u.findStep = none := by
            cases hu : u.findStep with
            | none => rfl
            | some p => simp only [Tm.findStep] at ht h; rw [ht] at h; simp [hu] at h
          intro w hw
          cases hw with
          | appL hs => exact Tm.normal_of_findStep _ ht _ hs
          | appR hs => exact Tm.normal_of_findStep u hu _ hs
  | .tapp t B, h => by
      cases t with
      | tlam α b => simp [Tm.findStep] at h
      | var y =>
          intro w hw
          cases hw with
          | tappL hs => cases hs
      | lam x A b =>
          have ht : (Tm.lam x A b).findStep = none := by
            cases ht : (Tm.lam x A b).findStep with
            | none => rfl
            | some p => simp only [Tm.findStep] at ht h; rw [ht] at h; cases h
          intro w hw
          cases hw with
          | tappL hs => exact Tm.normal_of_findStep _ ht _ hs
      | app t₁ t₂ =>
          have ht : (Tm.app t₁ t₂).findStep = none := by
            cases ht : (Tm.app t₁ t₂).findStep with
            | none => rfl
            | some p => simp only [Tm.findStep] at ht h; rw [ht] at h; cases h
          intro w hw
          cases hw with
          | tappL hs => exact Tm.normal_of_findStep _ ht _ hs
      | tapp t₁ B' =>
          have ht : (Tm.tapp t₁ B').findStep = none := by
            cases ht : (Tm.tapp t₁ B').findStep with
            | none => rfl
            | some p => simp only [Tm.findStep] at ht h; rw [ht] at h; cases h
          intro w hw
          cases hw with
          | tappL hs => exact Tm.normal_of_findStep _ ht _ hs

/-- Strongly normalizing named terms, ordered by reduction. -/
abbrev SNTm (N : Type) [Atom N] := { t : Tm N // SN Step t }

instance : WellFoundedRelation (SNTm N) where
  rel := fun a b => Step b.val a.val
  wf := ⟨fun ⟨_, h⟩ => by
    induction h with
    | intro _ ih =>
        constructor
        intro ⟨e', _⟩ hs
        exact ih e' hs⟩

/-- **The named normalizer**, total on strongly normalizing terms. -/
def Tm.eval (t : Tm N) (h : SN Step t) : Tm N :=
  match t.findStep with
  | none => t
  | some ⟨t', s⟩ => Tm.eval t' (h.unfold s)
termination_by (⟨t, h⟩ : SNTm N)

/-- What `eval` returns is reached by reduction and is normal. -/
theorem Tm.eval_spec {t : Tm N} (h : SN Step t) : RTC Step t (t.eval h) ∧ (t.eval h).Normal := by
  induction h with
  | @intro t hall ih =>
      rw [Tm.eval]
      split
      · rename_i hf
        exact ⟨.refl, Tm.normal_of_findStep t hf⟩
      · rename_i t' s _
        obtain ⟨hr, hn⟩ := ih t' s
        exact ⟨RTC.head s hr, hn⟩

/-- A normal term evaluates to itself. -/
theorem Tm.eval_of_normal {t : Tm N} (h : SN Step t) (hn : t.Normal) : t.eval h = t := by
  rw [Tm.eval]
  split
  · rfl
  · rename_i t' s _
    exact absurd s (hn t')

/-- Preservation along any number of steps. -/
theorem HasType.preservation_rtc {Θ : List N} {Γ : Ctx N} {t t' : Tm N} {A : Ty N}
    (h : HasType Θ Γ t A) (hs : RTC Step t t') : HasType Θ Γ t' A := by
  induction hs with
  | refl => exact h
  | tail _ s ih => exact ih.preservation s

/-- A well-typed named term's normal form. -/
def HasType.eval {Θ : List N} {Γ : Ctx N} {t : Tm N} {A : Ty N} (h : HasType Θ Γ t A) : Tm N :=
  t.eval h.sn

/-- The normal form keeps the type. -/
theorem HasType.eval_typed {Θ : List N} {Γ : Ctx N} {t : Tm N} {A : Ty N}
    (h : HasType Θ Γ t A) : HasType Θ Γ h.eval A :=
  h.preservation_rtc (Tm.eval_spec h.sn).1

end LambdaLab.Languages.SystemF.Named
