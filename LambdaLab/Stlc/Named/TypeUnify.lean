import LambdaLab.Stlc.Named.Basic
import LambdaLab.Unification.Signature
import LambdaLab.Unification.Basic

/-! # Signature instance for Named.Ty

Specialization of the slim `Signature` typeclass for the named-STLC `Ty`
type, so that first-order unification works on STLC types directly.

* Variables (for unification) are `Ty.mvar`.
* Constructors:
  - `base`  (arity 0)
  - `arrow` (arity 2)
  - `inf`   (arity 0) — included only so the `construct`/`deconstruct`
    bijection is total. `Ty.inf` is replaced with a fresh `Ty.mvar`
    during elaboration and is not expected to reach the unifier.

This file is a scratchpad to validate that the slim Signature design
is actually pleasant to instantiate. Delete once the unifier is wired
into elaboration. -/

namespace LambdaLab.Stlc.Named

/-- Constructor labels for `Ty` viewed as a free term algebra. -/
inductive TyCtor where
  | base
  | arrow
  | inf
  deriving DecidableEq

@[reducible]
def TyCtor.arity : TyCtor → Nat
  | .base  => 0
  | .arrow => 2
  | .inf   => 0

/-- Signature size for `Ty`: `mvar`, `base`, `inf` count as 1; `arrow`
is 1 plus the sum of children. Distinct from the structural `Ty`
operations because `Signature` requires the specific size law
`size (construct ⟨c, args⟩) = 1 + Σᵢ size (args.get i)`. -/
def Ty.sigSize : Ty → Nat
  | .base        => 1
  | .arrow τ₁ τ₂ => 1 + τ₁.sigSize + τ₂.sigSize
  | .inf         => 1
  | .mvar _      => 1

/-- Reassemble a `Ty` from a variable index or a constructor application. -/
def Ty.sigConstruct :
    Nat ⊕ (Σ c : TyCtor, Vector Ty (TyCtor.arity c)) → Ty
  | .inl n               => .mvar n
  | .inr ⟨.base, _⟩      => .base
  | .inr ⟨.arrow, args⟩  => .arrow (args.get 0) (args.get 1)
  | .inr ⟨.inf, _⟩       => .inf

/-- Decompose a `Ty` into a variable index or a constructor application. -/
def Ty.sigDeconstruct :
    Ty → Nat ⊕ (Σ c : TyCtor, Vector Ty (TyCtor.arity c))
  | .base        => .inr ⟨.base,  ⟨#[], rfl⟩⟩
  | .arrow τ₁ τ₂ => .inr ⟨.arrow, ⟨#[τ₁, τ₂], rfl⟩⟩
  | .inf         => .inr ⟨.inf,   ⟨#[], rfl⟩⟩
  | .mvar n      => .inl n

instance : Signature Ty where
  Constructor := TyCtor
  arity := TyCtor.arity
  decEqConstructor := inferInstance
  construct := Ty.sigConstruct
  deconstruct := Ty.sigDeconstruct
  size := Ty.sigSize

  construct_deconstruct := by
    intro a
    rcases a with n | ⟨c, args⟩
    · rfl
    · cases c with
      | base =>
          have hv : (⟨#[], rfl⟩ : Vector Ty 0) = args := by
            apply Vector.ext; intro i hi; omega
          exact congrArg (fun (v : Vector Ty (TyCtor.arity .base)) =>
            (Sum.inr ⟨TyCtor.base, v⟩ :
              Nat ⊕ (Σ c : TyCtor, Vector Ty (TyCtor.arity c)))) hv
      | arrow =>
          have hv : (⟨#[args.get 0, args.get 1], rfl⟩ : Vector Ty 2) = args := by
            apply Vector.ext; intro i hi
            rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
            · rfl
            · rfl
          exact congrArg (fun (v : Vector Ty (TyCtor.arity .arrow)) =>
            (Sum.inr ⟨TyCtor.arrow, v⟩ :
              Nat ⊕ (Σ c : TyCtor, Vector Ty (TyCtor.arity c)))) hv
      | inf =>
          have hv : (⟨#[], rfl⟩ : Vector Ty 0) = args := by
            apply Vector.ext; intro i hi; omega
          exact congrArg (fun (v : Vector Ty (TyCtor.arity .inf)) =>
            (Sum.inr ⟨TyCtor.inf, v⟩ :
              Nat ⊕ (Σ c : TyCtor, Vector Ty (TyCtor.arity c)))) hv

  deconstruct_construct := by
    intro a
    cases a <;> rfl

  size_construct_var := by intro n; rfl

  size_construct := by
    intro c args
    cases c with
    | base => rfl
    | inf  => rfl
    | arrow =>
        show 1 + (args.get 0).sigSize + (args.get 1).sigSize
              = 1 + (List.finRange 2).foldr
                  (fun i acc => acc + (args.get i).sigSize) 0
        have hL : (List.finRange 2 : List (Fin 2)) = [(0 : Fin 2), (1 : Fin 2)] :=
          by decide
        rw [hL]
        simp only [List.foldr_cons, List.foldr_nil, Nat.zero_add]
        omega

/-! ## Sanity checks: drive the unifier on `Ty`. -/

/-- Empty equation set returns the empty unifier. -/
example : unify ([] : Equations Ty) = some [] := by native_decide

/-- A bare metavariable equated to a ground type elaborates to the
expected single binding. -/
example : unify [(Ty.mvar 0, Ty.base ⇒ Ty.base)] =
          some [(0, Ty.base ⇒ Ty.base)] := by native_decide

/-- Mismatched outermost constructors fail. -/
example : unify [(Ty.base, Ty.base ⇒ Ty.base)] = none := by native_decide

/-- Occurs check fires: `?0 ≐ ?0 ⇒ τ` is unsolvable. -/
example : unify [(Ty.mvar 0, Ty.mvar 0 ⇒ Ty.base)] = none := by native_decide

end LambdaLab.Stlc.Named
