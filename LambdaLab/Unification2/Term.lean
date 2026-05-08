import LambdaLab.Unification2.Substitution

/-! # Generic free term algebra (no typeclass)

`Term C` is the inductive type of terms with `Nat`-many variables and
constructor labels from `C`. Args are a `List` (length validity is
checked extrinsically — see `WellFormed`).

Keeping the args length out of the inductive lets Lean's structural
recursion checker handle definitions over `Term C` cleanly. -/

namespace LambdaLab.Unification2

inductive Term (C : Type) : Type where
  | var (n : Nat) : Term C
  | app (c : C) (args : List (Term C)) : Term C
  deriving Repr

namespace Term

variable {C : Type}

/-- Detect whether a term is a variable. -/
def isVar : Term C → Option Nat
  | .var n   => some n
  | .app _ _ => none

mutual
  /-- Structural size. -/
  def size : Term C → Nat
    | .var _      => 1
    | .app _ args => 1 + sizeList args
  def sizeList : List (Term C) → Nat
    | []      => 0
    | t :: ts => size t + sizeList ts
end

mutual
  /-- Decidable occurs check. -/
  def occurs (n : Nat) : Term C → Bool
    | .var m      => decide (n = m)
    | .app _ args => occursList n args
  def occursList (n : Nat) : List (Term C) → Bool
    | []      => false
    | t :: ts => occurs n t || occursList n ts
end

mutual
  /-- Fresh variable index. -/
  def fresh : Term C → Nat
    | .var n      => n + 1
    | .app _ args => freshList args
  def freshList : List (Term C) → Nat
    | []      => 0
    | t :: ts => max (fresh t) (freshList ts)
end

mutual
  /-- Apply a parallel substitution (Subst from Unification2.Substitution). -/
  def pSubst (σ : Subst (Term C)) : Term C → Term C
    | .var n      => σ.getD n (.var n)
    | .app c args => .app c (pSubstList σ args)
  def pSubstList (σ : Subst (Term C)) : List (Term C) → List (Term C)
    | []      => []
    | t :: ts => pSubst σ t :: pSubstList σ ts
end

/-- Single-binding substitution. -/
def single (t : Term C) (n : Nat) (s : Term C) : Term C :=
  pSubst ((∅ : Subst (Term C)).insert n s) t

end Term

/-! ## Equations -/

abbrev Equation (C : Type) := Term C × Term C
abbrev Equations (C : Type) := List (Equation C)

namespace Term

variable {C : Type}

/-- Apply a substitution to an equation pointwise. -/
def Equation.subst (σ : Subst (Term C)) (eq : Equation C) : Equation C :=
  (pSubst σ eq.1, pSubst σ eq.2)

/-- Apply a single-binding to all equations in a list. -/
def Equations.single (eqs : Equations C) (n : Nat) (s : Term C) : Equations C :=
  eqs.map (fun p => (Term.single p.1 n s, Term.single p.2 n s))

/-! ## Decomposition

`decomp x y` matches the outermost constructors of `x` and `y`. -/

/-- One step of constructor matching. Requires `DecidableEq C` to compare
constructor heads. -/
def decomp [DecidableEq C] (x y : Term C) : Option (Equations C) :=
  match x, y with
  | .app cx argsx, .app cy argsy =>
      if h : cx = cy ∧ argsx.length = argsy.length then
        some (argsx.zip argsy)
      else none
  | _, _ => none

theorem decomp_var_left [DecidableEq C] (n : Nat) (y : Term C) :
    decomp (.var n) y = none := by
  simp [decomp]

theorem decomp_var_right [DecidableEq C] (x : Term C) (n : Nat) :
    decomp x (.var n) = none := by
  cases x <;> simp [decomp]

end Term

/-! ## Unifiers and `MoreGeneral` -/

/-- `MoreGeneral σ σ'`: σ is at least as general as σ'. -/
def MoreGeneral {C : Type} (σ σ' : Subst (Term C)) : Prop :=
  ∃ τ : Subst (Term C), ∀ t : Term C,
    Term.pSubst σ' t = Term.pSubst τ (Term.pSubst σ t)

/-- A unifier as an iterated single-binding sequence. -/
abbrev Unifier (C : Type) := List (Nat × Term C)

namespace Unifier

variable {C : Type}

/-- Apply a unifier to a term: each `(n, s)` binding is applied as a
single substitution, in order from the head. -/
def apply (u : Unifier C) (t : Term C) : Term C :=
  u.foldl (fun acc p => Term.single acc p.1 p.2) t

@[simp] theorem apply_nil (t : Term C) : apply [] t = t := rfl

@[simp] theorem apply_cons (n : Nat) (s : Term C) (rest : Unifier C) (t : Term C) :
    apply ((n, s) :: rest) t = apply rest (Term.single t n s) := rfl

@[simp] theorem apply_append (u₁ u₂ : Unifier C) (t : Term C) :
    (u₁ ++ u₂).apply t = u₂.apply (u₁.apply t) := by
  show List.foldl _ _ _ = _
  rw [List.foldl_append]; rfl

end Unifier

/-- A unifier (in the algebraic sense) of an equation set. -/
abbrev Unifier.Unifies {C : Type} (u : Unifier C) (eqs : Equations C) : Prop :=
  ∀ p ∈ eqs, u.apply p.1 = u.apply p.2

/-- Pull the head equation out of a unifier of `(x, y) :: eqs'`. -/
theorem Unifier.Unifies.head_eq {C : Type}
    {u : Unifier C} {x y : Term C} {eqs' : Equations C}
    (hu : u.Unifies ((x, y) :: eqs')) : u.apply x = u.apply y := by
  simpa using hu (x, y) List.mem_cons_self

end LambdaLab.Unification2
