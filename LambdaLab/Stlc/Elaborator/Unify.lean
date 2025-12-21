import LambdaLab.Stlc.Ty

open Subst

namespace Stlc.Elaborator

def Equation := Ty × Ty

def toStringEquation (e  : Equation) := let ⟨ l, r ⟩ := e; s!"{l} ≐ {r}"

instance ToStringEquation : ToString Equation where
  toString := toStringEquation

def EquationSystem := List Equation

def toStringEquationSystem (e  : EquationSystem) :=
  match e with
  | []    => ""
  | e::[] => s!"{e}"
  | e::es => s!"{e}, {toStringEquationSystem es}"

instance ToStringEquationSystem : ToString EquationSystem where
  toString s := "{ " ++ toStringEquationSystem s ++ " }"


instance : Subst Nat Ty Equation where
  subst σ e := e.map (subst σ) (subst σ)

instance EquationSystemIsSubst : Subst Nat Ty EquationSystem where
  subst σ es := es.map (subst σ)


partial def unifySystem (es : EquationSystem) (σ : Substitution Nat Ty) : Option (Substitution Nat Ty) :=
  let tryStep (e : Equation) (es : EquationSystem) (σ : Substitution Nat Ty) : Option (Substitution Nat Ty) :=
    let elim (x : Nat) (r : Ty) := unifySystem (substOne x r es) (Std.TreeMap.insert (substOne x r σ) x r)
    match e with
    | ⟨ .var x₁, .var x₂ ⟩ => if x₁ == x₂ then unifySystem es σ
                              else elim x₁ (.var x₂)
    | ⟨ .atm s₁, .atm s₂ ⟩  => if s₁ == s₂ then unifySystem es σ else none
    | ⟨ .arr α₁ β₁, .arr α₂ β₂ ⟩  => unifySystem (⟨ α₁, α₂ ⟩::⟨ β₁, β₂ ⟩::es) σ
    | ⟨ l, .var x ⟩ => unifySystem (⟨ .var x, l ⟩::es) σ
    | ⟨ .var x₁, r ⟩ => if occurs x₁ r then none else elim x₁ r
    | _ => none

  match es with
  | []    => σ
  | e::es => tryStep e es σ

inductive UnificationResult (α β : Ty) where
| mgu    : (σ : Substitution Nat Ty) → subst σ α = subst σ β → UnificationResult α β

def mgu? (r : Option (UnificationResult α β)) : Option (Substitution Nat Ty) :=
    match r with
    | some (UnificationResult.mgu σ _) => σ
    | none => none

def unify (α β : Ty) : Option (UnificationResult α β) :=
  match unifySystem [⟨α, β⟩] ∅ with
  | some σ => some ⟨ σ, by sorry ⟩
  | none   => none

def unifyE (α β : Ty) : Except String (UnificationResult α β) :=
  match unify α β with
  | some r => .ok r
  | none => .error s!"unification of {α} with {β} failed"

end Stlc.Elaborator
