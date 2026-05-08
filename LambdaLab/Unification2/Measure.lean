import LambdaLab.Unification2.Bridge

/-! # Termination measure for `unify`

The Martelli–Montanari algorithm terminates by lex `(mvarCount, size)`
decrease. -/

namespace LambdaLab.Unification2

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
  ∃ p ∈ eqs, Term.occurs n p.1 = true ∨ Term.occurs n p.2 = true

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

/-! Note: the rest of the measure infrastructure (`fresh_gt_occurs` for
Term, mvarCount monotonicity lemmas, etc.) requires a proper structural
induction principle on `Term C` that handles the nested `List` correctly.
Auto-generated `Term.rec` exists but is awkward; deferring this to a
proper port effort. -/

end Equations

end LambdaLab.Unification2
