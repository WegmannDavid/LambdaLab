import LambdaLab.Stlc.Named.Basic
import LambdaLab.Substitution.Unification.Basic

/-! # `Signature` instance for the named-STLC type language `Ty`

`Ty.mvar` is the variable position; `Ty.base`, `Ty.arrow`, and `Ty.inf`
are 0-, 2-, and 0-ary constructors respectively. With this instance,
type equations can be discharged by `unify` from the unification module.

`Ty.inf` is included as a nullary constructor for totality, but it is
intended as a placeholder that the elaborator replaces with a fresh
`Ty.mvar` before unification runs. Two surviving `Ty.inf` atoms unify
trivially with each other; with anything else they clash. -/

namespace LambdaLab.Stlc.Named

inductive TyConstructor : Type where
  | base
  | arrow
  | inf
  deriving DecidableEq

@[reducible] def TyConstructor.arity : TyConstructor → Nat
  | .base  => 0
  | .arrow => 2
  | .inf   => 0

def Ty.size : Ty → Nat
  | .mvar _    => 1
  | .base      => 1
  | .inf       => 1
  | .arrow a b => 1 + size a + size b

private def construct :
    Nat ⊕ (Σ c : TyConstructor, Vector Ty (TyConstructor.arity c)) → Ty
  | .inl n               => .mvar n
  | .inr ⟨.base, _⟩      => .base
  | .inr ⟨.arrow, args⟩  => .arrow (args.get 0) (args.get 1)
  | .inr ⟨.inf, _⟩       => .inf

private def deconstruct :
    Ty → Nat ⊕ (Σ c : TyConstructor, Vector Ty (TyConstructor.arity c))
  | .mvar n    => .inl n
  | .base      => .inr ⟨.base, Vector.ofFn Fin.elim0⟩
  | .arrow a b => .inr ⟨.arrow, Vector.ofFn (fun i =>
      match i with | 0 => a | 1 => b)⟩
  | .inf       => .inr ⟨.inf, Vector.ofFn Fin.elim0⟩

instance : Signature Ty where
  Constructor      := TyConstructor
  arity            := TyConstructor.arity
  decEqConstructor := inferInstance
  construct        := construct
  deconstruct      := deconstruct
  size             := Ty.size
  construct_deconstruct := by
    intro a
    rcases a with n | ⟨c, args⟩
    · rfl
    cases c
    · -- base, args : Vector Ty 0
      show deconstruct .base = _
      simp only [deconstruct]
      congr
      apply Vector.ext
      intro i hi
      exact absurd hi (Nat.not_lt_zero _)
    · -- arrow, args : Vector Ty 2
      show deconstruct (.arrow (args.get 0) (args.get 1)) = _
      simp only [deconstruct]
      congr
      apply Vector.ext
      intro i hi
      show ((Vector.ofFn _)[i]'hi) = args[i]'hi
      simp only [Vector.getElem_ofFn]
      match i, hi with
      | 0, _ => rfl
      | 1, _ => rfl
    · -- inf, args : Vector Ty 0
      show deconstruct .inf = _
      simp only [deconstruct]
      congr
      apply Vector.ext
      intro i hi
      exact absurd hi (Nat.not_lt_zero _)
  deconstruct_construct := by
    intro a
    cases a with
    | mvar n    => rfl
    | base      => rfl
    | arrow x y => rfl
    | inf       => rfl
  size_construct_var := by intro _; rfl
  size_construct := by
    intro c args
    cases c
    · -- base, arity 0
      show (1 : Nat) = 1 + (List.finRange 0).foldr _ 0
      rfl
    · -- arrow, arity 2
      show 1 + Ty.size (args.get 0) + Ty.size (args.get 1) =
            1 + (List.finRange 2).foldr
              (fun i acc => acc + Ty.size (args.get i)) 0
      simp [List.finRange, List.foldr]
      omega
    · -- inf, arity 0
      show (1 : Nat) = 1 + (List.finRange 0).foldr _ 0
      rfl

end LambdaLab.Stlc.Named
