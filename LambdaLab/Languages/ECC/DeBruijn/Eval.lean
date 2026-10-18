import LambdaLab.Languages.ECC.DeBruijn.Preservation
import LambdaLab.Languages.ECC.DeBruijn.Scope

/-!
# ECC — the normalizer, and deciding conversion and subtyping

`Tm.eval t` reduces `t` to its normal form: `findStep` picks a redex, leftmost-outermost, by
structural recursion, and the outer loop contracts it until none is left.

## A partial fixpoint

The loop terminates exactly when `t` is normalizing — for a well-typed term, when ECC is — and
strong normalization is not proved here for the whole hierarchy (it could not be: it implies
consistency, and ECC with every universe is about as strong as Lean). So `eval` is a
**`partial_fixpoint`**: a function into `Option` that runs as plain recursion and that the logic
reads as the least fixed point of its equation — `none` where the loop would not stop. What it
returns is correct without any normalization assumption (`Tm.eval_sound`): reached by reduction,
and normal. And it does return, on every strongly normalizing term (`Tm.eval_of_sn`).

## Comparing normal forms

By confluence a term has at most one normal form (`Red.normal_unique`), so two normalizing terms
are convertible exactly when their normal forms are equal (`Tm.eval_conv_iff`), and one is a
subtype of the other exactly when their normal forms are syntactically cumulative
(`Tm.eval_sub_iff`) — a decidable, syntactic check (`leqB`).
-/

namespace LambdaLab.Languages.ECC.DeBruijn

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

/-- **The normalizer.** It returns `none`, logically, where the loop would not stop. -/
def Tm.eval (t : Tm) : Option Tm :=
  match t.findStep with
  | none => some t
  | some ⟨t', _⟩ => Tm.eval t'
partial_fixpoint

/-- **What `eval` returns** is reached by reduction and is normal — no normalization assumed. -/
theorem Tm.eval_sound {t v : Tm} (h : t.eval = some v) : Red t v ∧ v.Normal := by
  refine Tm.eval.partial_correctness (fun t v => Red t v ∧ v.Normal) ?_ t v h
  intro ev ih t v hv
  split at hv
  · rename_i hf
    cases hv
    exact ⟨.refl, Tm.normal_of_findStep hf⟩
  · rename_i t' s _
    obtain ⟨hr, hn⟩ := ih t' v hv
    exact ⟨RTC.head s hr, hn⟩

/-- **A normal term evaluates to itself.** -/
theorem Tm.eval_of_normal {t : Tm} (hn : t.Normal) : t.eval = some t := by
  rw [Tm.eval]
  split
  · rfl
  · rename_i t' s _
    exact absurd s (hn t')

/-- **`eval` returns on every strongly normalizing term.** -/
theorem Tm.eval_of_sn {t : Tm} (h : SN Step t) : ∃ v, t.eval = some v := by
  induction h with
  | @intro t _ ih =>
      rw [Tm.eval]
      split
      · exact ⟨t, rfl⟩
      · rename_i t' s _
        exact ih t' s

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

/-- Every reduct of a term with a normal form reduces to it. -/
theorem Red.to_normal {t a v : Tm} (hv : Red t v) (hn : v.Normal) (ha : Red t a) : Red a v := by
  obtain ⟨c, hac, hvc⟩ := Red.confluent ha hv
  rw [hn.red_eq hvc] at hac
  exact hac

/-- **Two terms with normal forms are convertible exactly when the normal forms are equal.** -/
theorem Tm.eval_conv_iff {a b va vb : Tm} (ha : a.eval = some va) (hb : b.eval = some vb) :
    va = vb ↔ Conv a b := by
  obtain ⟨hra, hna⟩ := Tm.eval_sound ha
  obtain ⟨hrb, hnb⟩ := Tm.eval_sound hb
  constructor
  · intro e
    exact ⟨va, hra, e ▸ hrb⟩
  · rintro ⟨c, hac, hbc⟩
    exact Red.normal_unique (Red.to_normal hra hna hac) (Red.to_normal hrb hnb hbc) hna hnb

/-- **Two terms with normal forms are subtypes exactly when the normal forms are syntactically
cumulative.** -/
theorem Tm.eval_sub_iff {a b va vb : Tm} (ha : a.eval = some va) (hb : b.eval = some vb) :
    Leq va vb ↔ Sub a b := by
  obtain ⟨hra, hna⟩ := Tm.eval_sound ha
  obtain ⟨hrb, hnb⟩ := Tm.eval_sound hb
  constructor
  · intro hl
    exact ⟨va, vb, hra, hrb, hl⟩
  · rintro ⟨a', b', ha', hb', hl⟩
    -- push the left side to its normal form
    obtain ⟨b₁, hb₁, hl₁⟩ := hl.red_left (Red.to_normal hra hna ha')
    -- and the right side to its normal form
    have hb₁v : Red b₁ vb := Red.to_normal hrb hnb (RTC.trans hb' hb₁)
    obtain ⟨a₂, ha₂, hl₂⟩ := hl₁.red_right hb₁v
    rw [hna.red_eq ha₂] at hl₂
    exact hl₂

/-! ## Deciding syntactic cumulativity -/

/-- **Syntactic cumulativity, decided.** -/
def leqB : Tm → Tm → Bool
  | .sort s, .sort s' => decide (s.le s')
  | .pi A B, .pi A' B' => A == A' && leqB B B'
  | a, b => a == b

theorem leqB_refl : ∀ t : Tm, leqB t t = true
  | .sort s => by simp [leqB, Srt.le_refl]
  | .pi A B => by simp [leqB, leqB_refl B]
  | .var _ => by simp [leqB]
  | .lam _ _ => by simp [leqB]
  | .app _ _ => by simp [leqB]

theorem leqB_complete {a b : Tm} (h : Leq a b) : leqB a b = true := by
  induction h with
  | refl => exact leqB_refl _
  | sort hs => simp [leqB, hs]
  | pi _ ih => simp [leqB, ih]

theorem leqB_sound : ∀ {a b : Tm}, leqB a b = true → Leq a b
  | .sort s, .sort s', h => .sort (by simpa [leqB] using h)
  | .pi A B, .pi A' B', h => by
      simp only [leqB, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      exact .pi (leqB_sound h)
  | .var _, b, h => by simp only [leqB, beq_iff_eq] at h; subst h; exact .refl _
  | .lam _ _, b, h => by simp only [leqB, beq_iff_eq] at h; subst h; exact .refl _
  | .app _ _, b, h => by simp only [leqB, beq_iff_eq] at h; subst h; exact .refl _
  | .sort _, .var _, h => by simp [leqB] at h
  | .sort _, .pi _ _, h => by simp [leqB] at h
  | .sort _, .lam _ _, h => by simp [leqB] at h
  | .sort _, .app _ _, h => by simp [leqB] at h
  | .pi _ _, .var _, h => by simp [leqB] at h
  | .pi _ _, .sort _, h => by simp [leqB] at h
  | .pi _ _, .lam _ _, h => by simp [leqB] at h
  | .pi _ _, .app _ _, h => by simp [leqB] at h

/-- **Decide `A ≼ B`** by normalizing both; `false` if either has no normal form. -/
def subB (A B : Tm) : Bool :=
  match A.eval, B.eval with
  | some a, some b => leqB a b
  | _, _ => false

theorem subB_sound {A B : Tm} (h : subB A B = true) : Sub A B := by
  unfold subB at h
  split at h
  · rename_i a b ha hb
    exact (Tm.eval_sub_iff ha hb).mp (leqB_sound h)
  · cases h

theorem subB_complete {A B : Tm} (hA : SN Step A) (hB : SN Step B) (h : Sub A B) :
    subB A B = true := by
  obtain ⟨a, ha⟩ := Tm.eval_of_sn hA
  obtain ⟨b, hb⟩ := Tm.eval_of_sn hB
  unfold subB
  rw [ha, hb]
  exact leqB_complete ((Tm.eval_sub_iff ha hb).mpr h)

/-! ## Normalization, as a hypothesis -/

/-- **ECC normalizes**: every well-typed term, in a valid context, is strongly normalizing. Not
proved for the whole hierarchy; theorems that need it take it as a hypothesis. -/
def Normalizing : Prop := ∀ {Γ : Ctx} {t T : Tm}, Wf Γ → HasType Γ t T → SN Step t

/-- What `eval` returns keeps the type. -/
theorem HasType.eval_typed {Γ : Ctx} {t T v : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hv : t.eval = some v) : HasType Γ v T :=
  h.preservation_red hΓ (Tm.eval_sound hv).1

end LambdaLab.Languages.ECC.DeBruijn
