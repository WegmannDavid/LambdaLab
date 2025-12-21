import LambdaLab.Nominal.Subst

inductive Ty : Type where
| atm : String → Ty
| var : Nat → Ty
| arr : Ty → Ty → Ty
deriving DecidableEq

prefix:90 "!"  => Ty.atm
prefix:90 "?"  => Ty.var
infixr:60 "⟶"  => Ty.arr

instance : ToString Ty where
  toString :=
    let rec h t :=
      match t with
      | .atm s    => s
      | .var n    => s!"? {n}"
      | .arr α β  => s!"{h α} ⟶ {h β}"
    h

def occurs (x : Nat) (t : Ty) :=
  match t with
  | .atm s => false
  | .var y => x == y
  | .arr α β => if occurs x α then true else occurs x β

instance : Nominal Ty where
  fresh :=
    let rec h t :=
      match t with
      | .atm s    => 0
      | .var n    => n + 1
      | .arr α β  => max (h α) (h β)
    h

instance : Subst Nat Ty Ty where
  subst σ := let rec h t :=
    match t with
    | .atm s => .atm s
    | .var n => match σ[n]? with
                | some α => α
                | none   => .var n
    | .arr α β => .arr (h α) (h β)
    h

open Subst

@[simp]
theorem subst_arr {σ : Substitution Nat Ty} : subst σ (α ⟶ β) = subst σ α ⟶ subst σ β := by rfl
