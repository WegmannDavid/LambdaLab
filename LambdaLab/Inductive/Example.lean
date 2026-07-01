import LambdaLab.Inductive.Basic

/-!
# `Nat` and `List` as `Inductive` instances

The standard-library `Nat` and `List` are instances of the generic `Inductive`
class. With the telescope `Signature`, each constructor is described by its field
list, `construct`/`destruct` are the constructors / `casesOn`, and `child_wf`
(well-foundedness of the recursive-child relation) is discharged via
`Subrelation.wf` against the usual measure (`<` for `Nat`, `length` for `List`).

Each carrier is then registered with a `WellFoundedRelation` instance, so ordinary
`termination_by`/`decreasing_by` recursion over it descends along `childRel`.
-/

namespace LambdaLab.Inductive

/-! ## `Nat` -/

/-- The two constructors of `Nat`: `zero` (no fields) and `succ` (one recursive
field). -/
inductive NatC | zero | succ

def natSig : Signature where
  Con := NatC
  constructor := fun | .zero => .nil | .succ => .recursive .nil

/-- The destructor, named so `simp` can unfold it in the `child_wf` proof. -/
def natDestruct : Nat → natSig.Apply Nat
  | 0     => ⟨.zero, ⟨⟩⟩
  | n + 1 => ⟨.succ, (n, ⟨⟩)⟩

instance : Inductive Nat natSig where
  construct := fun ⟨c, args⟩ => match c, args with
    | .zero, _      => 0
    | .succ, (n, _) => n.succ
  destruct := natDestruct
  destruct_construct := by
    rintro ⟨c, args⟩; cases c
    · rfl
    · obtain ⟨n, _⟩ := args; rfl
  construct_destruct := by rintro (_ | n) <;> rfl
  child_wf := by
    refine Subrelation.wf ?_ Nat.lt_wfRel.wf
    intro x a hx
    show x < a
    rcases a with _ | n
    · simp [childRel, natDestruct, natSig, Constructor.children] at hx
    · simp [childRel, natDestruct, natSig, Constructor.children] at hx
      omega

instance : WellFoundedRelation Nat := Inductive.wfRel

/-! ## `List` -/

/-- The two constructors of `List`: `nil` (no fields) and `cons` (its head as a
`data` field, the tail as a recursive field). -/
inductive ListC | nil | cons

def listSig (α : Type) : Signature where
  Con := ListC
  constructor := fun | .nil => .nil | .cons => .data α (.recursive .nil)

def listDestruct {α : Type} : List α → (listSig α).Apply (List α)
  | []     => ⟨.nil, ⟨⟩⟩
  | a :: t => ⟨.cons, (a, t, ⟨⟩)⟩

instance (α : Type) : Inductive (List α) (listSig α) where
  construct := fun ⟨c, args⟩ => match c, args with
    | .nil,  _         => []
    | .cons, (a, t, _) => a :: t
  destruct := listDestruct
  destruct_construct := by
    rintro ⟨c, args⟩; cases c
    · rfl
    · obtain ⟨a, t, _⟩ := args; rfl
  construct_destruct := by rintro (_ | ⟨a, t⟩) <;> rfl
  child_wf := by
    refine Subrelation.wf ?_ (measure List.length).wf
    intro x a hx
    show x.length < a.length
    rcases a with _ | ⟨h, t⟩
    · simp [childRel, listDestruct, listSig, Constructor.children] at hx
    · simp [childRel, listDestruct, listSig, Constructor.children] at hx
      subst hx
      exact Nat.lt_succ_self _

instance (α : Type) : WellFoundedRelation (List α) := Inductive.wfRel

end LambdaLab.Inductive
