import LambdaLab.Substitution.Basic

/-! # Generic free term algebra (Fin-function args, no typeclass)

`Term C` has variables and constructor applications where args are
`Fin n → Term C`. The arity `n` is a separate constructor argument
(not tied to `c`), so well-formedness is checked extrinsically. -/

namespace LambdaLab.Substitution.Unification

inductive Term (C : Type) : Type where
  | var (n : Nat) : Term C
  | app (c : C) (n : Nat) (args : Fin n → Term C) : Term C

namespace Term

variable {C : Type}

/-- Detect whether a term is a variable. -/
def isVar : Term C → Option Nat
  | .var n     => some n
  | .app _ _ _ => none

/-- Structural size: variables count as 1, constructors are 1 plus the
sum of children's sizes. -/
def size : Term C → Nat
  | .var _        => 1
  | .app _ n args => 1 + (List.finRange n).foldr (fun i acc => acc + size (args i)) 0

/-- Decidable occurs check. -/
def occurs (n : Nat) : Term C → Bool
  | .var m        => decide (n = m)
  | .app _ _ args => (List.finRange _).any (fun i => occurs n (args i))

/-- Fresh variable index. -/
def fresh : Term C → Nat
  | .var n        => n + 1
  | .app _ _ args => (List.finRange _).foldr (fun i acc => max acc (fresh (args i))) 0

/-- Apply a parallel substitution. -/
def pSubst (σ : Subst (Term C)) : Term C → Term C
  | .var n        => σ.getD n (.var n)
  | .app c k args => .app c k (fun i => pSubst σ (args i))

/-- Single-binding substitution. -/
def single (t : Term C) (n : Nat) (s : Term C) : Term C :=
  pSubst ((∅ : Subst (Term C)).insert n s) t

end Term

/-! ## Equations -/

abbrev Equation (C : Type) := Term C × Term C
abbrev Equations (C : Type) := List (Equation C)

namespace Term

variable {C : Type}

/-- Decomposition: heads must agree AND arity must match. -/
def decomp [DecidableEq C] (x y : Term C) : Option (Equations C) :=
  match x, y with
  | .app cx nx argsx, .app cy ny argsy =>
      if h : cx = cy ∧ nx = ny then
        some ((List.finRange nx).map (fun i => (argsx i, argsy (h.2 ▸ i))))
      else none
  | _, _ => none

theorem decomp_var_left [DecidableEq C] (n : Nat) (y : Term C) :
    decomp (.var n) y = none := by simp [decomp]

theorem decomp_var_right [DecidableEq C] (x : Term C) (n : Nat) :
    decomp x (.var n) = none := by cases x <;> simp [decomp]

end Term

/-- A unifier as an iterated single-binding sequence. -/
abbrev Unifier (C : Type) := List (Nat × Term C)

namespace Unifier

variable {C : Type}

def apply (u : Unifier C) (t : Term C) : Term C :=
  u.foldl (fun acc p => Term.single acc p.1 p.2) t

@[simp] theorem apply_nil (t : Term C) : apply [] t = t := rfl

@[simp] theorem apply_cons (n : Nat) (s : Term C) (rest : Unifier C) (t : Term C) :
    apply ((n, s) :: rest) t = apply rest (Term.single t n s) := rfl

end Unifier

abbrev Unifier.Unifies {C : Type} (u : Unifier C) (eqs : Equations C) : Prop :=
  ∀ p ∈ eqs, u.apply p.1 = u.apply p.2

/-- Pull the head equation out of a unifier of `(x, y) :: eqs'`. -/
theorem Unifier.Unifies.head_eq {C : Type}
    {u : Unifier C} {x y : Term C} {eqs' : Equations C}
    (hu : u.Unifies ((x, y) :: eqs')) : u.apply x = u.apply y := by
  simpa using hu (x, y) List.mem_cons_self

end LambdaLab.Substitution.Unification
