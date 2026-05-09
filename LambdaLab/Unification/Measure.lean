import LambdaLab.Unification.Bridge

/-! # Termination measure for `unify`

The Martelli–Montanari algorithm terminates by lex `(mvarCount, size)`
decrease. -/

namespace LambdaLab.Unification

namespace Equations

variable {C : Type}

/-- Total syntactic size of an equation set. -/
def size (eqs : Equations C) : Nat :=
  eqs.foldr (fun p acc => acc + Term.size p.1 + Term.size p.2) 0

/-- Maximum `fresh` over all terms in the equations. -/
def fresh (eqs : Equations C) : Nat :=
  eqs.foldr (fun p acc => max acc (max (Term.fresh p.1) (Term.fresh p.2))) 0

/-- `n` is free somewhere in the equation set. -/
def isFree (eqs : Equations C) (n : Nat) : Prop :=
  ∃ p, p ∈ eqs ∧ (Term.occurs n p.1 = true ∨ Term.occurs n p.2 = true)

/-- Number of distinct metavariables appearing in `eqs`. -/
def mvarCount (eqs : Equations C) : Nat :=
  let bound := fresh eqs
  (List.range bound).countP (fun n =>
    eqs.any (fun p => Term.occurs n p.1 || Term.occurs n p.2))

/-- The boolean predicate inside `mvarCount` is exactly `isFree`. -/
theorem any_occurs_iff_isFree (eqs : Equations C) (n : Nat) :
    (eqs.any (fun p => Term.occurs n p.1 || Term.occurs n p.2) = true)
      ↔ isFree eqs n := by
  simp only [List.any_eq_true, Bool.or_eq_true]
  rfl

/-- For any equation in `eqs`, its component freshes are ≤ `fresh eqs`. -/
theorem fresh_ge_of_mem : ∀ {eqs : Equations C} {p : Equation C}, p ∈ eqs →
    max (Term.fresh p.1) (Term.fresh p.2) ≤ fresh eqs
  | _ :: qs, p, hp => by
      rcases List.mem_cons.mp hp with rfl | hp'
      · show _ ≤ max (fresh qs) (max (Term.fresh p.1) (Term.fresh p.2))
        exact Nat.le_max_right _ _
      · have := fresh_ge_of_mem (eqs := qs) hp'
        show _ ≤ max (fresh qs) _; omega

/-- A variable at or above `fresh eqs` is never free in `eqs`. -/
theorem not_isFree_of_fresh_le {eqs : Equations C} {n : Nat}
    (hle : fresh eqs ≤ n) : ¬ isFree eqs n := by
  intro ⟨p, hp, hor⟩
  have hpfresh := fresh_ge_of_mem hp
  rcases hor with h1 | h2
  · have h := Term.fresh_gt_occurs p.1 n h1; omega
  · have h := Term.fresh_gt_occurs p.2 n h2; omega

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

theorem mvarCount_le_of_isFree_subset {eqs₁ eqs₂ : Equations C}
    (hvars : ∀ n, isFree eqs₁ n → isFree eqs₂ n) :
    eqs₁.mvarCount ≤ eqs₂.mvarCount := by
  let P : Equations C → Nat → Bool := fun eqs n =>
    eqs.any (fun p => Term.occurs n p.1 || Term.occurs n p.2)
  have hPfalse : ∀ (eqs : Equations C) n, fresh eqs ≤ n → P eqs n = false := by
    intro eqs n hn
    cases hb : P eqs n
    · rfl
    · exact absurd (not_isFree_of_fresh_le hn ((any_occurs_iff_isFree eqs n).mp hb))
        (by intro; contradiction)
  let M := max (fresh eqs₁) (fresh eqs₂)
  have heq₁ : (List.range M).countP (P eqs₁) = mvarCount eqs₁ :=
    countP_range_eq_of_false_above (Nat.le_max_left _ _) (hPfalse eqs₁)
  have heq₂ : (List.range M).countP (P eqs₂) = mvarCount eqs₂ :=
    countP_range_eq_of_false_above (Nat.le_max_right _ _) (hPfalse eqs₂)
  rw [← heq₁, ← heq₂]
  apply List.countP_mono_left
  intro n _ h
  exact (any_occurs_iff_isFree eqs₂ n).mpr (hvars n ((any_occurs_iff_isFree eqs₁ n).mp h))

theorem mvarCount_cons_le (p : Equation C) (eqs : Equations C) :
    mvarCount eqs ≤ mvarCount (p :: eqs) := by
  apply mvarCount_le_of_isFree_subset
  intro n ⟨q, hq, hor⟩
  exact ⟨q, List.mem_cons_of_mem _ hq, hor⟩

theorem mvarCount_lt_of_isFree_subset_strict {eqs₁ eqs₂ : Equations C} (n : Nat)
    (hvars : ∀ m, isFree eqs₁ m → isFree eqs₂ m)
    (hn₁ : ¬ isFree eqs₁ n)
    (hn₂ : isFree eqs₂ n) :
    eqs₁.mvarCount < eqs₂.mvarCount := by
  let P : Equations C → Nat → Bool := fun eqs n =>
    eqs.any (fun p => Term.occurs n p.1 || Term.occurs n p.2)
  have hPfalse : ∀ (eqs : Equations C) m, fresh eqs ≤ m → P eqs m = false := by
    intro eqs m hm
    cases hb : P eqs m
    · rfl
    · exact absurd (not_isFree_of_fresh_le hm ((any_occurs_iff_isFree eqs m).mp hb))
        (by intro; contradiction)
  let M := max (fresh eqs₁) (fresh eqs₂)
  have heq₁ : (List.range M).countP (P eqs₁) = mvarCount eqs₁ :=
    countP_range_eq_of_false_above (Nat.le_max_left _ _) (hPfalse eqs₁)
  have heq₂ : (List.range M).countP (P eqs₂) = mvarCount eqs₂ :=
    countP_range_eq_of_false_above (Nat.le_max_right _ _) (hPfalse eqs₂)
  rw [← heq₁, ← heq₂]
  have hnM : n < M := by
    obtain ⟨q, hq, hor⟩ := hn₂
    have hpfresh := fresh_ge_of_mem hq
    rcases hor with h | h
    · have := Term.fresh_gt_occurs q.1 n h
      exact Nat.lt_of_lt_of_le (by omega) (Nat.le_max_right _ _)
    · have := Term.fresh_gt_occurs q.2 n h
      exact Nat.lt_of_lt_of_le (by omega) (Nat.le_max_right _ _)
  apply countP_lt_countP_of_strict_at (a := n) (P := P eqs₁) (Q := P eqs₂)
  · intro m _ h
    exact (any_occurs_iff_isFree eqs₂ m).mpr (hvars m ((any_occurs_iff_isFree eqs₁ m).mp h))
  · exact List.mem_range.mpr hnM
  · cases hb : P eqs₁ n
    · rfl
    · exact absurd ((any_occurs_iff_isFree eqs₁ n).mp hb) hn₁
  · exact (any_occurs_iff_isFree eqs₂ n).mpr hn₂

theorem size_cons (p : Equation C) (eqs : Equations C) :
    size (p :: eqs) = size eqs + Term.size p.1 + Term.size p.2 := rfl

theorem size_append (xs eqs : Equations C) :
    size (xs ++ eqs) = size xs + size eqs := by
  induction xs with
  | nil =>
      show size eqs = size [] + size eqs
      simp [size]
  | cons p ps ih =>
      show size ((p :: ps) ++ eqs) = _
      rw [List.cons_append, size_cons, size_cons, ih]
      omega

theorem _root_.Prod.Lex.ofNat_le_lt {a₁ a₂ b₁ b₂ : Nat}
    (hle : a₁ ≤ a₂) (hlt : a₁ = a₂ → b₁ < b₂) :
    Prod.Lex (· < ·) (· < ·) (a₁, b₁) (a₂, b₂) := by
  rcases Nat.lt_or_eq_of_le hle with h | h
  · exact Prod.Lex.left _ _ h
  · subst h
    exact Prod.Lex.right _ (hlt rfl)

end Equations

end LambdaLab.Unification
