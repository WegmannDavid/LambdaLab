import LambdaLab.Languages.ECC.Named.Typing

/-!
# ECC, named — the normalizer

The named counterpart of `DeBruijn/Eval.lean`: `findStep` contracts the leftmost-outermost redex,
by capture-avoiding substitution, and `Tm.eval` repeats it until none is left. Like the de Bruijn
one it is a `partial_fixpoint`: what it returns is reached by reduction and normal, with no
normalization assumed, and it returns on every strongly normalizing term. A normal term is its own
result, and a result keeps the type.
-/

namespace LambdaLab.Languages.ECC.Named

open LambdaLab.Nominal (Atom)
open LambdaLab (SN RTC)

variable {N : Type} [Atom N]

/-- **Find a redex**, leftmost-outermost, and contract it. -/
def Tm.findStep : (t : Tm N) → Option ((t' : Tm N) ×' Step t t')
  | .var _ => none
  | .sort _ => none
  | .pi x A B =>
      match A.findStep with
      | some ⟨A', s⟩ => some ⟨.pi x A' B, .piA s⟩
      | none =>
          match B.findStep with
          | some ⟨B', s⟩ => some ⟨.pi x A B', .piB s⟩
          | none => none
  | .lam x A t =>
      match A.findStep with
      | some ⟨A', s⟩ => some ⟨.lam x A' t, .lamA s⟩
      | none =>
          match t.findStep with
          | some ⟨t', s⟩ => some ⟨.lam x A t', .lamB s⟩
          | none => none
  | .app (.lam x _ b) u => some ⟨b.inst x u, .beta⟩
  | .app t u =>
      match t.findStep with
      | some ⟨t', s⟩ => some ⟨.app t' u, .appL s⟩
      | none =>
          match u.findStep with
          | some ⟨u', s⟩ => some ⟨.app t u', .appR s⟩
          | none => none

theorem Tm.findStep_app_of_ne_lam {t u : Tm N} (h : ∀ x A b, t ≠ .lam x A b) :
    (Tm.app t u).findStep =
      (match t.findStep with
        | some ⟨t', s⟩ => some ⟨.app t' u, .appL s⟩
        | none =>
            match u.findStep with
            | some ⟨u', s⟩ => some ⟨.app t u', .appR s⟩
            | none => none) := by
  cases t with
  | lam x A b => exact absurd rfl (h x A b)
  | _ => rfl

/-- **`findStep` misses no redex.** -/
theorem Step.findStep_isSome {t w : Tm N} (h : Step t w) : t.findStep.isSome := by
  induction h with
  | beta => rfl
  | @appL t t' u _ ih =>
      by_cases hl : ∃ x A b, t = .lam x A b
      · obtain ⟨x, A, b, rfl⟩ := hl; rfl
      · rw [Tm.findStep_app_of_ne_lam (fun x A b e => hl ⟨x, A, b, e⟩)]
        cases hf : t.findStep with
        | none => rw [hf] at ih; cases ih
        | some p => rfl
  | @appR t u u' _ ih =>
      by_cases hl : ∃ x A b, t = .lam x A b
      · obtain ⟨x, A, b, rfl⟩ := hl; rfl
      · rw [Tm.findStep_app_of_ne_lam (fun x A b e => hl ⟨x, A, b, e⟩)]
        cases hf : t.findStep with
        | some p => rfl
        | none =>
            cases hf' : u.findStep with
            | none => rw [hf'] at ih; cases ih
            | some p => rfl
  | @lamA x A A' t _ ih =>
      simp only [Tm.findStep]
      cases hf : A.findStep with
      | none => rw [hf] at ih; cases ih
      | some p => rfl
  | @lamB x A t t' _ ih =>
      simp only [Tm.findStep]
      cases hf : A.findStep with
      | some p => rfl
      | none =>
          cases hf' : t.findStep with
          | none => rw [hf'] at ih; cases ih
          | some p => rfl
  | @piA x A A' B _ ih =>
      simp only [Tm.findStep]
      cases hf : A.findStep with
      | none => rw [hf] at ih; cases ih
      | some p => rfl
  | @piB x A B B' _ ih =>
      simp only [Tm.findStep]
      cases hf : A.findStep with
      | some p => rfl
      | none =>
          cases hf' : B.findStep with
          | none => rw [hf'] at ih; cases ih
          | some p => rfl

theorem Tm.normal_of_findStep {t : Tm N} (h : t.findStep = none) : t.Normal := by
  intro w hw
  have := hw.findStep_isSome
  rw [h] at this
  cases this

/-- **The named normalizer.** It returns `none`, logically, where the loop would not stop. -/
def Tm.eval (t : Tm N) : Option (Tm N) :=
  match t.findStep with
  | none => some t
  | some ⟨t', _⟩ => Tm.eval t'
partial_fixpoint

/-- What `eval` returns is reached by reduction and is normal. -/
theorem Tm.eval_sound {t v : Tm N} (h : t.eval = some v) : RTC Step t v ∧ v.Normal := by
  refine Tm.eval.partial_correctness (fun t v => RTC Step t v ∧ v.Normal) ?_ t v h
  intro ev ih t v hv
  split at hv
  · rename_i hf
    cases hv
    exact ⟨.refl, Tm.normal_of_findStep hf⟩
  · rename_i t' s _
    obtain ⟨hr, hn⟩ := ih t' v hv
    exact ⟨RTC.head s hr, hn⟩

/-- A normal term evaluates to itself. -/
theorem Tm.eval_of_normal {t : Tm N} (hn : t.Normal) : t.eval = some t := by
  rw [Tm.eval]
  split
  · rfl
  · rename_i t' s _
    exact absurd s (hn t')

/-- `eval` returns on every strongly normalizing term. -/
theorem Tm.eval_of_sn {t : Tm N} (h : SN Step t) : ∃ v, t.eval = some v := by
  induction h with
  | @intro t _ ih =>
      rw [Tm.eval]
      split
      · exact ⟨t, rfl⟩
      · rename_i t' s _
        exact ih t' s

/-- Preservation along any number of steps. -/
theorem HasType.preservation_rtc {Γ : Ctx N} {t t' T : Tm N} (h : HasType Γ t T)
    (hΓ : Ctx.Wf Γ) (hs : RTC Step t t') : HasType Γ t' T := by
  induction hs with
  | refl => exact h
  | tail _ s ih => exact ih.preservation hΓ s

/-- What `eval` returns keeps the type. -/
theorem HasType.eval_typed {Γ : Ctx N} {t T v : Tm N} (h : HasType Γ t T) (hΓ : Ctx.Wf Γ)
    (hv : t.eval = some v) : HasType Γ v T :=
  h.preservation_rtc hΓ (Tm.eval_sound hv).1

end LambdaLab.Languages.ECC.Named
