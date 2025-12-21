import LambdaLab.Stlc.Ty

inductive Tm : Type where
| var : String → Tm
| app : Tm → Tm → Tm
| abs : String → Ty → Tm → Tm

prefix:90    "#"                    => Tm.var
notation:50  "ƛ" x ":" τ "=>" t:51  => Tm.abs x τ t
infixl:70    "⬝"                     => Tm.app

instance : ToString Tm where
  toString :=
    let rec h t :=
      match t with
      | .var x    => s!"{x}"
      | .app t s  => s!"({h t} {h s})"
      | .abs x α t => s!"λ {x} : {α} . {h t}"
    h


open Subst

def substTm (σ : Substitution Nat Ty) (t : Tm) : Tm :=
    match t with
    | .var x => .var x
    | .app t s => .app (substTm σ t) (substTm σ s)
    | .abs x α t => .abs x (subst σ α) (substTm σ t)

instance : Subst Nat Ty Tm where
  subst := substTm

open Nominal

instance : Nominal Tm where
  fresh :=
    let rec h t :=
    match t with
    | .var _ => 0
    | .app t s => max (h t) (h s)
    | .abs _ α t => max (fresh α) (h t)
    h

@[simp]
theorem subst_var {σ : Substitution Nat Ty} : subst σ (# x) = (# x) := by rfl

@[simp]
theorem subst_abs {σ : Substitution Nat Ty} : subst σ (ƛ x : α => t) = (ƛ x : (subst σ α) => (subst σ t)) := by rfl

@[simp]
theorem subst_app {σ : Substitution Nat Ty} : subst σ (t ⬝ s) = subst σ t ⬝ subst σ s := by rfl
