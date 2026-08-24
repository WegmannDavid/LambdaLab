import LambdaLab.Nominal.Unification.Signature

namespace LambdaLab.Nominal.Unification

open LambdaLab.Nominal

/-! # Termination measure for `unify`

The Martelli–Montanari algorithm terminates by a lexicographic
`(mvarCount, size)` decrease. This module defines the measure and the
monotonicity lemmas needed to discharge the four `decreasing_by` goals
in `Unification.Basic`.

In the slim-typeclass approach, `Signature.occurs n t = true ↔
HasVars.isFree t n` is *definitional* (the derived `HasSubst A α α`
instance defines `isFree` as `occurs · = true`), so the bool/Prop
bridge collapses to `Iff.rfl`.

## Why the measure does not use `Nat`'s order

`mvarCount` used to count by searching an initial segment: it took `HasVars.fresh eqs` as an upper
bound and ran `(List.range bound).countP (occurs · )`. That is correct but it needs three things
atoms do not have — an order, an enumeration below a bound, and a `max` to build a common search
space for two equation sets. It is also wasteful, since the segment is as long as the largest
variable *index*, not as long as the number of variables.

It now counts the distinct elements of `Equations.vars`, which asks only for `DecidableEq`. The
lemma statements below are unchanged — they were always phrased in terms of `HasVars.isFree`, and
only their proofs knew about the order — so `Unification.Basic` is untouched. The measure is still
`Nat`-valued and the lexicographic argument is still `Nat × Nat`; nothing about termination moved.

What survives here referring to `fresh` is `not_isFree_of_fresh_le`, which the elaborator's
pruning arguments use (`Typing/W.lean`, `Typing/JComplete.lean`) and which is not part of the
measure. -/

/-- Total syntactic size of an equation set. -/
def Equations.size {A α : Type} [Atom A] [Signature A α] (eqs : Equations α) : Nat :=
  eqs.foldr (fun p acc => acc + Signature.size p.1 + Signature.size p.2) 0

/-! ## Counting distinct elements

`List.dedup` is Mathlib's, and `Substitution/` imports nothing but `Std`. Three short definitions
and a pigeonhole lemma are cheaper than the dependency — and this is the whole of what replaces
the order. -/

/-- The distinct elements of a list. -/
def distinct {β : Type} [DecidableEq β] : List β → List β
  | [] => []
  | x :: xs => if x ∈ xs then distinct xs else x :: distinct xs

theorem mem_distinct {β : Type} [DecidableEq β] {l : List β} {a : β} :
    a ∈ distinct l ↔ a ∈ l := by
  induction l with
  | nil => exact Iff.rfl
  | cons x xs ih =>
      show a ∈ (if x ∈ xs then distinct xs else x :: distinct xs) ↔ a ∈ x :: xs
      by_cases hx : x ∈ xs
      · rw [if_pos hx, List.mem_cons]
        exact ⟨fun h => Or.inr (ih.mp h), fun h => ih.mpr (h.elim (fun he => he ▸ hx) id)⟩
      · rw [if_neg hx, List.mem_cons, List.mem_cons]
        exact or_congr Iff.rfl ih

theorem nodup_distinct {β : Type} [DecidableEq β] (l : List β) : (distinct l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      show (if x ∈ xs then distinct xs else x :: distinct xs).Nodup
      by_cases hx : x ∈ xs
      · rw [if_pos hx]; exact ih
      · rw [if_neg hx]
        exact List.nodup_cons.mpr ⟨fun h => hx (mem_distinct.mp h), ih⟩

/-- **Pigeonhole.** A duplicate-free list contained in another is no longer than it. This is what
`countP_range_eq_of_false_above` used to buy by splitting a range, and unlike that argument it
says nothing about where the elements sit. -/
theorem Nodup.length_le_of_subset {β : Type} [DecidableEq β] :
    ∀ {l₁ l₂ : List β}, l₁.Nodup → l₁ ⊆ l₂ → l₁.length ≤ l₂.length := by
  intro l₁
  induction l₁ with
  | nil => intro _ _ _; exact Nat.zero_le _
  | cons a t ih =>
      intro l₂ hnd hsub
      have ha : a ∈ l₂ := hsub List.mem_cons_self
      obtain ⟨hant, htnd⟩ := List.nodup_cons.mp hnd
      have hsub' : t ⊆ l₂.erase a := by
        intro b hb
        have hne : b ≠ a := by intro h; subst h; exact hant hb
        exact (List.mem_erase_of_ne hne).mpr (hsub (List.mem_cons_of_mem _ hb))
      have hle := ih htnd hsub'
      rw [List.length_erase_of_mem ha] at hle
      have hpos : 0 < l₂.length := List.length_pos_of_mem ha
      simp only [List.length_cons]
      omega

/-- Strict pigeonhole: one element of the larger list missing from the smaller forces a gap. -/
theorem Nodup.length_lt_of_subset_of_mem {β : Type} [DecidableEq β] {l₁ l₂ : List β} {a : β}
    (hnd : l₁.Nodup) (hsub : l₁ ⊆ l₂) (ha₂ : a ∈ l₂) (ha₁ : a ∉ l₁) :
    l₁.length < l₂.length := by
  have hsub' : l₁ ⊆ l₂.erase a := by
    intro b hb
    have hne : b ≠ a := by intro h; subst h; exact ha₁ hb
    exact (List.mem_erase_of_ne hne).mpr (hsub hb)
  have hle := Nodup.length_le_of_subset hnd hsub'
  rw [List.length_erase_of_mem ha₂] at hle
  have hpos : 0 < l₂.length := List.length_pos_of_mem ha₂
  omega

/-- Every variable occurring anywhere in an equation set, with multiplicity. -/
def Equations.vars {A α : Type} [Atom A] [Signature A α] (eqs : Equations α) : List A :=
  eqs.flatMap (fun p => Signature.vars p.1 ++ Signature.vars p.2)

/-- Number of distinct metavariables appearing in an equation set. -/
def Equations.mvarCount {A α : Type} [Atom A] [Signature A α] (eqs : Equations α) : Nat :=
  (distinct eqs.vars).length

namespace Equations
variable {A α : Type} [Atom A] [Signature A α]

/-- The boolean predicate `mvarCount` used to range over is exactly `HasVars.isFree`.
    Bridges the bool/Prop divide for measure reasoning — definitionally
    in the slim-typeclass setup, but kept as a named lemma for clarity. -/
theorem any_occurs_iff_isFree (eqs : Equations α) (n : A) :
    (eqs.any (fun p => Signature.occurs n p.1 || Signature.occurs n p.2) = true)
      ↔ HasVars.isFree eqs n := by
  simp only [List.any_eq_true, Bool.or_eq_true]
  rfl

/-- **`Equations.vars` lists exactly the free variables.** Everything below reads the measure
through this and never touches the term structure again. -/
theorem mem_vars_iff_isFree (eqs : Equations α) (n : A) :
    n ∈ eqs.vars ↔ HasVars.isFree eqs n := by
  rw [← any_occurs_iff_isFree]
  simp only [Equations.vars, List.mem_flatMap, List.any_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨p, hp, hmem⟩
    refine ⟨p, hp, ?_⟩
    rcases List.mem_append.mp hmem with h | h
    · exact Or.inl ((Signature.mem_vars_iff_occurs n p.1).mp h)
    · exact Or.inr ((Signature.mem_vars_iff_occurs n p.2).mp h)
  · rintro ⟨p, hp, h | h⟩
    · exact ⟨p, hp, List.mem_append.mpr (Or.inl ((Signature.mem_vars_iff_occurs n p.1).mpr h))⟩
    · exact ⟨p, hp, List.mem_append.mpr (Or.inr ((Signature.mem_vars_iff_occurs n p.2).mpr h))⟩

/-- Membership in the counted list, stated the way the measure lemmas want it. -/
theorem mem_distinct_vars_iff_isFree (eqs : Equations α) (n : A) :
    n ∈ distinct eqs.vars ↔ HasVars.isFree eqs n :=
  Iff.trans mem_distinct (mem_vars_iff_isFree eqs n)

/-- Containment of free-variable sets gives `mvarCount ≤`. -/
theorem mvarCount_le_of_isFree_subset {eqs₁ eqs₂ : Equations α}
    (hvars : ∀ n, HasVars.isFree eqs₁ n → HasVars.isFree eqs₂ n) :
    eqs₁.mvarCount ≤ eqs₂.mvarCount :=
  Nodup.length_le_of_subset (nodup_distinct _) (fun n hn =>
    (mem_distinct_vars_iff_isFree eqs₂ n).mpr
      (hvars n ((mem_distinct_vars_iff_isFree eqs₁ n).mp hn)))

/-- Cons-monotonicity of `mvarCount`. -/
theorem mvarCount_cons_le (p : Equation α) (eqs : Equations α) :
    Equations.mvarCount eqs ≤ Equations.mvarCount (p :: eqs) := by
  apply mvarCount_le_of_isFree_subset
  intro n ⟨q, hq, hor⟩
  exact ⟨q, List.mem_cons_of_mem _ hq, hor⟩

/-- Strict drop in `mvarCount` when a variable is in the larger set but
    not the smaller. -/
theorem mvarCount_lt_of_isFree_subset_strict {eqs₁ eqs₂ : Equations α} (n : A)
    (hvars : ∀ m, HasVars.isFree eqs₁ m → HasVars.isFree eqs₂ m)
    (hn₁ : ¬ HasVars.isFree eqs₁ n)
    (hn₂ : HasVars.isFree eqs₂ n) :
    eqs₁.mvarCount < eqs₂.mvarCount :=
  Nodup.length_lt_of_subset_of_mem (a := n) (nodup_distinct _)
    (fun m hm => (mem_distinct_vars_iff_isFree eqs₂ m).mpr
      (hvars m ((mem_distinct_vars_iff_isFree eqs₁ m).mp hm)))
    ((mem_distinct_vars_iff_isFree eqs₂ n).mpr hn₂)
    (fun h => hn₁ ((mem_distinct_vars_iff_isFree eqs₁ n).mp h))

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

end LambdaLab.Nominal.Unification
