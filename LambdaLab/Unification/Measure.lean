import LambdaLab.Unification.Signature

/-! # Termination measure for `unify`

The Martelli–Montanari algorithm terminates by a lexicographic
`(mvarCount, size)` decrease. This module defines the measure and the
monotonicity lemmas needed to discharge the four `decreasing_by` goals
in `Unification.Basic`.

In the slim-typeclass approach, `Signature.occurs n t = true ↔
HasVars.isFree t n` is *definitional* (the derived `HasSubst α α`
instance defines `isFree` as `occurs · = true`), so the bool/Prop
bridge collapses to `Iff.rfl`. -/

/-- Total syntactic size of an equation set. -/
def Equations.size {α : Type} [Signature α] (eqs : Equations α) : Nat :=
  eqs.foldr (fun p acc => acc + Signature.size p.1 + Signature.size p.2) 0

/-- Number of distinct metavariables appearing in an equation set,
bounded above by `HasVars.fresh eqs` and detected by `Signature.occurs`. -/
def Equations.mvarCount {α : Type} [Signature α] (eqs : Equations α) : Nat :=
  let bound := HasVars.fresh eqs
  (List.range bound).countP (fun n =>
    eqs.any (fun p => Signature.occurs n p.1 || Signature.occurs n p.2))

namespace Equations
variable {α : Type} [Signature α]

/-- The boolean predicate inside `mvarCount` is exactly `HasVars.isFree`.
    Bridges the bool/Prop divide for measure reasoning — definitionally
    in the slim-typeclass setup, but kept as a named lemma for clarity. -/
theorem any_occurs_iff_isFree (eqs : Equations α) (n : Nat) :
    (eqs.any (fun p => Signature.occurs n p.1 || Signature.occurs n p.2) = true)
      ↔ HasVars.isFree eqs n := by
  simp only [List.any_eq_true, Bool.or_eq_true]
  rfl

/-- A variable at or above `fresh eqs` is never free in `eqs` — the
    contrapositive of `fresh_gt_free`. -/
theorem not_isFree_of_fresh_le {eqs : Equations α} {n : Nat}
    (h : HasVars.fresh eqs ≤ n) : ¬ HasVars.isFree eqs n := by
  intro hfree
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (HasVars.fresh_gt_free eqs n hfree) h)

/-- Extending the range above `a` doesn't change `countP` if the predicate
    is false everywhere above `a`. -/
theorem countP_range_eq_of_false_above {a M : Nat} {P : Nat → Bool}
    (hMa : a ≤ M) (h : ∀ n, a ≤ n → P n = false) :
    (List.range M).countP P = (List.range a).countP P := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hMa
  rw [List.range_add, List.countP_append]
  have hzero : (List.map (fun x => a + x) (List.range k)).countP P = 0 := by
    rw [List.countP_eq_zero]
    intro y hy hytrue
    rcases List.mem_map.mp hy with ⟨x, _, hx⟩
    subst hx
    rw [h (a + x) (Nat.le_add_right _ _)] at hytrue
    cases hytrue
  omega

/-- A strict-drop lemma for `countP`. -/
theorem countP_lt_countP_of_strict_at {α} {P Q : α → Bool} {l : List α} {a : α}
    (hPQ : ∀ x ∈ l, P x = true → Q x = true)
    (ha : a ∈ l) (hPa : P a = false) (hQa : Q a = true) :
    l.countP P < l.countP Q := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.mp ha with rfl | ha'
      · simp only [hPa, hQa, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        have : xs.countP P ≤ xs.countP Q :=
          List.countP_mono_left (fun y hy hPy => hPQ y (List.mem_cons_of_mem _ hy) hPy)
        omega
      · have ihres : xs.countP P < xs.countP Q :=
          ih (fun y hy => hPQ y (List.mem_cons_of_mem _ hy)) ha'
        have hhead : (if P x = true then 1 else 0) ≤ (if Q x = true then 1 else 0) := by
          cases hPx : P x
          · simp [Bool.false_eq_true]
          · cases hQx : Q x
            · exact absurd (hPQ x List.mem_cons_self hPx) (by rw [hQx]; intro; contradiction)
            · simp
        omega

/-- Containment of free-variable sets gives `mvarCount ≤`. -/
theorem mvarCount_le_of_isFree_subset {eqs₁ eqs₂ : Equations α}
    (hvars : ∀ n, HasVars.isFree eqs₁ n → HasVars.isFree eqs₂ n) :
    eqs₁.mvarCount ≤ eqs₂.mvarCount := by
  let P : Equations α → Nat → Bool := fun eqs n =>
    eqs.any (fun p => Signature.occurs n p.1 || Signature.occurs n p.2)
  have hPfalse : ∀ (eqs : Equations α) n, HasVars.fresh eqs ≤ n → P eqs n = false := by
    intro eqs n hn
    cases hb : P eqs n
    · rfl
    · exact absurd (not_isFree_of_fresh_le hn ((any_occurs_iff_isFree eqs n).mp hb)) (by
        intro; contradiction)
  let M := max (HasVars.fresh eqs₁) (HasVars.fresh eqs₂)
  have heq₁ : (List.range M).countP (P eqs₁) = Equations.mvarCount eqs₁ :=
    countP_range_eq_of_false_above (Nat.le_max_left _ _) (hPfalse eqs₁)
  have heq₂ : (List.range M).countP (P eqs₂) = Equations.mvarCount eqs₂ :=
    countP_range_eq_of_false_above (Nat.le_max_right _ _) (hPfalse eqs₂)
  rw [← heq₁, ← heq₂]
  apply List.countP_mono_left
  intro n _ h
  exact (any_occurs_iff_isFree eqs₂ n).mpr (hvars n ((any_occurs_iff_isFree eqs₁ n).mp h))

/-- Cons increases `fresh`. -/
theorem fresh_cons_le (p : Equation α) (eqs : Equations α) :
    HasVars.fresh eqs ≤ HasVars.fresh (p :: eqs) := by
  show _ ≤ max (HasVars.fresh eqs) (HasVars.fresh p)
  exact Nat.le_max_left _ _

/-- Append on the left increases `fresh`. -/
theorem fresh_append_right_le (xs eqs : Equations α) :
    HasVars.fresh eqs ≤ HasVars.fresh (xs ++ eqs) := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons p ps ih =>
      exact Nat.le_trans ih (fresh_cons_le p (ps ++ eqs))

/-- Cons-monotonicity of `mvarCount`. -/
theorem mvarCount_cons_le (p : Equation α) (eqs : Equations α) :
    Equations.mvarCount eqs ≤ Equations.mvarCount (p :: eqs) := by
  apply mvarCount_le_of_isFree_subset
  intro n ⟨q, hq, hor⟩
  exact ⟨q, List.mem_cons_of_mem _ hq, hor⟩

/-- Strict drop in `mvarCount` when a variable is in the larger set but
    not the smaller. -/
theorem mvarCount_lt_of_isFree_subset_strict {eqs₁ eqs₂ : Equations α} (n : Nat)
    (hvars : ∀ m, HasVars.isFree eqs₁ m → HasVars.isFree eqs₂ m)
    (hn₁ : ¬ HasVars.isFree eqs₁ n)
    (hn₂ : HasVars.isFree eqs₂ n) :
    eqs₁.mvarCount < eqs₂.mvarCount := by
  let P : Equations α → Nat → Bool := fun eqs n =>
    eqs.any (fun p => Signature.occurs n p.1 || Signature.occurs n p.2)
  have hPfalse : ∀ (eqs : Equations α) m, HasVars.fresh eqs ≤ m → P eqs m = false := by
    intro eqs m hm
    cases hb : P eqs m
    · rfl
    · exact absurd (not_isFree_of_fresh_le hm ((any_occurs_iff_isFree eqs m).mp hb)) (by
        intro; contradiction)
  let M := max (HasVars.fresh eqs₁) (HasVars.fresh eqs₂)
  have heq₁ : (List.range M).countP (P eqs₁) = Equations.mvarCount eqs₁ :=
    countP_range_eq_of_false_above (Nat.le_max_left _ _) (hPfalse eqs₁)
  have heq₂ : (List.range M).countP (P eqs₂) = Equations.mvarCount eqs₂ :=
    countP_range_eq_of_false_above (Nat.le_max_right _ _) (hPfalse eqs₂)
  rw [← heq₁, ← heq₂]
  have hnM : n < M := by
    have := HasVars.fresh_gt_free eqs₂ n hn₂
    exact Nat.lt_of_lt_of_le this (Nat.le_max_right _ _)
  apply countP_lt_countP_of_strict_at
    (a := n) (P := P eqs₁) (Q := P eqs₂)
  · intro m _ h
    exact (any_occurs_iff_isFree eqs₂ m).mpr (hvars m ((any_occurs_iff_isFree eqs₁ m).mp h))
  · exact List.mem_range.mpr hnM
  · cases hb : P eqs₁ n
    · rfl
    · exact absurd ((any_occurs_iff_isFree eqs₁ n).mp hb) hn₁
  · exact (any_occurs_iff_isFree eqs₂ n).mpr hn₂

/-- `size` of a cons. -/
theorem size_cons (p : Equation α) (eqs : Equations α) :
    Equations.size (p :: eqs) =
      Equations.size eqs + Signature.size p.1 + Signature.size p.2 :=
  rfl

/-- `size` of an append. -/
theorem size_append (xs eqs : Equations α) :
    Equations.size (xs ++ eqs) = Equations.size xs + Equations.size eqs := by
  induction xs with
  | nil =>
      show Equations.size eqs = Equations.size [] + Equations.size eqs
      simp [Equations.size]
  | cons p ps ih =>
      show Equations.size ((p :: ps) ++ eqs) = _
      rw [List.cons_append, size_cons, size_cons, ih]
      omega

/-- Lex helper: weak first component, strict second component. -/
theorem _root_.Prod.Lex.ofNat_le_lt {a₁ a₂ b₁ b₂ : Nat}
    (hle : a₁ ≤ a₂) (hlt : a₁ = a₂ → b₁ < b₂) :
    Prod.Lex (· < ·) (· < ·) (a₁, b₁) (a₂, b₂) := by
  rcases Nat.lt_or_eq_of_le hle with h | h
  · exact Prod.Lex.left _ _ h
  · subst h
    exact Prod.Lex.right _ (hlt rfl)

end Equations
