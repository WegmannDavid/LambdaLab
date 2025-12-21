import LambdaLab.Nominal.Subst

inductive BinderType
| prd
| abs

inductive Tm : Type where
| typ : Nat → Tm
| var : String → Tm
| app : Tm → Tm → Tm
| bnd : BinderType → String → Tm → Tm → Tm


prefix:90    "#"                    => Tm.var
notation:50  "ƛ" x ":" τ "=>" t:51  => Tm.bnd BinderType.abs x τ t
notation:50  "Π" x ":" τ "=>" t:51  => Tm.bnd BinderType.prd  x τ t
infixl:70    "⬝"                     => Tm.app

instance : ToString Tm where
  toString :=
    let rec h t :=
      match t with
      | .typ u          => s!"Type{u}"
      | .var x          => s!"{x}"
      | .app t s        => s!"({h t} {h s})"
      | .bnd .prd x α t => s!"λ {x} : {h α} . {h t}"
      | .bnd .abs x α t => s!"Π {x} : {h α} . {h t}"
    h


open Subst

def substTmVar (σ : Substitution String Tm) (t : Tm) : Tm :=
    match t with
    | .typ u       => .typ u
    | .var x       => .var x
    | .app t s     => .app (substTmVar σ t) (substTmVar σ s)
    | .bnd b x α t => .bnd b x (substTmVar σ α) (substTmVar σ t)

instance : Subst String Tm Tm where
  subst := substTmVar

open Nominal

instance : Nominal Tm where
  fresh :=
    let rec h t :=
    match t with
    | .typ _       => 0
    | .var _       => 0
    | .app t s     => max (h t) (h s)
    | .bnd _ _ α t => max (h α) (h t)
    h

@[simp]
theorem subst_abs {σ : Substitution String Tm} : subst σ (ƛ x : α => t) = (ƛ x : (subst σ α) => (subst σ t)) := by rfl

@[simp]
theorem subst_app {σ : Substitution String Tm} : subst σ (t ⬝ s) = subst σ t ⬝ subst σ s := by rfl
