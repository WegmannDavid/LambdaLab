import LambdaLab.Stlc.Named.Basic
import LambdaLab.Substitution.Unification.Basic

/-! # `Signature` instance for the named-STLC type language `Ty`

`Ty.mvar` is the variable position; `Ty.base` and `Ty.arrow` are
0- and 2-ary constructors. With this instance, type equations are
discharged by `unify` from the unification module. -/

namespace LambdaLab.Stlc.Named

inductive TyConstructor : Type where
  | base
  | arrow
  deriving DecidableEq

@[reducible] def TyConstructor.arity : TyConstructor → Nat
  | .base  => 0
  | .arrow => 2

def Ty.size : Ty → Nat
  | .mvar _    => 1
  | .base      => 1
  | .arrow a b => 1 + size a + size b

private def construct :
    Nat ⊕ (Σ c : TyConstructor, Vector Ty (TyConstructor.arity c)) → Ty
  | .inl n               => .mvar n
  | .inr ⟨.base, _⟩      => .base
  | .inr ⟨.arrow, args⟩  => .arrow (args.get 0) (args.get 1)

private def deconstruct :
    Ty → Nat ⊕ (Σ c : TyConstructor, Vector Ty (TyConstructor.arity c))
  | .mvar n    => .inl n
  | .base      => .inr ⟨.base, Vector.ofFn Fin.elim0⟩
  | .arrow a b => .inr ⟨.arrow, Vector.ofFn (fun i =>
      match i with | 0 => a | 1 => b)⟩

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
    · show deconstruct .base = _
      simp only [deconstruct]
      congr
      apply Vector.ext
      intro i hi
      exact absurd hi (Nat.not_lt_zero _)
    · show deconstruct (.arrow (args.get 0) (args.get 1)) = _
      simp only [deconstruct]
      congr
      apply Vector.ext
      intro i hi
      show ((Vector.ofFn _)[i]'hi) = args[i]'hi
      simp only [Vector.getElem_ofFn]
      match i, hi with
      | 0, _ => rfl
      | 1, _ => rfl
  deconstruct_construct := by
    intro a
    cases a with
    | mvar n    => rfl
    | base      => rfl
    | arrow x y => rfl
  size_construct_var := by intro _; rfl
  size_construct := by
    intro c args
    cases c
    · show (1 : Nat) = 1 + (List.finRange 0).foldr _ 0
      rfl
    · show 1 + Ty.size (args.get 0) + Ty.size (args.get 1) =
            1 + (List.finRange 2).foldr
              (fun i acc => acc + Ty.size (args.get i)) 0
      simp [List.finRange, List.foldr]
      omega

/-! ## `HasSubst Term Ty` — substitute `Ty.mvar`s in annotations.

The "variables" of a `Term` (for the purpose of a `Subst Ty`) are the
`Ty.mvar` indices that appear in its type annotations. `pSubst e σ`
walks `e`, applying `σ` to each annotation. -/

namespace Term

def tyIsFree : Term → Nat → Prop
  | .var _,        _ => False
  | .lam _ τ body, n => HasVars.isFree τ n ∨ tyIsFree body n
  | .app e₁ e₂,    n => tyIsFree e₁ n ∨ tyIsFree e₂ n

def tyFresh : Term → Nat
  | .var _        => 0
  | .lam _ τ body => max (HasVars.fresh τ) (tyFresh body)
  | .app e₁ e₂    => max (tyFresh e₁) (tyFresh e₂)

theorem tyFresh_gt_tyIsFree : ∀ (e : Term) (n : Nat),
    tyIsFree e n → n < tyFresh e := by
  intro e
  induction e with
  | var _ => intro _ h; cases h
  | lam x τ body ih =>
      intro n h
      simp only [tyFresh]
      rcases h with hτ | hb
      · exact Nat.lt_of_lt_of_le (HasVars.fresh_gt_free _ _ hτ) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih _ hb) (Nat.le_max_right _ _)
  | app e₁ e₂ ih₁ ih₂ =>
      intro n h
      simp only [tyFresh]
      rcases h with h₁ | h₂
      · exact Nat.lt_of_lt_of_le (ih₁ _ h₁) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih₂ _ h₂) (Nat.le_max_right _ _)

def tyPSubst : Term → Subst Ty → Term
  | .var x,        _ => .var x
  | .lam x τ body, σ => .lam x (HasSubst.pSubst τ σ) (tyPSubst body σ)
  | .app e₁ e₂,    σ => .app (tyPSubst e₁ σ) (tyPSubst e₂ σ)

end Term

instance : HasVars Term where
  isFree := Term.tyIsFree
  fresh  := Term.tyFresh
  fresh_gt_free := Term.tyFresh_gt_tyIsFree

instance : HasSubst Term Ty where
  pSubst := Term.tyPSubst

/-! ## `pSubst ∅` is the identity on `Term` and on `Ctx` (up to lookup).

For `Term`: structural. For `Ctx` (a `HashMap`): equality up to layout
doesn't hold, but every `get?` agrees, which is enough for typing
proofs (via `HasType.cong`). -/

@[simp] theorem Term.tyPSubst_empty (e : Term) :
    Term.tyPSubst e (∅ : Subst Ty) = e := by
  induction e with
  | var _ => rfl
  | lam _ τ body ih =>
      simp only [Term.tyPSubst, ih]
      congr 1
      exact Signature.pSubst_empty τ
  | app _ _ ih₁ ih₂ =>
      simp only [Term.tyPSubst, ih₁, ih₂]

theorem HashMap.pSubst_empty_get? (Γ : Std.HashMap String Ty) (x : String) :
    (HasSubst.pSubst Γ (∅ : Subst Ty)).get? x = Γ.get? x := by
  show (Γ.map (fun _ v => HasSubst.pSubst v (∅ : Subst Ty))).get? x = Γ.get? x
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map,
      ← Std.HashMap.get?_eq_getElem?]
  cases h : Γ.get? x with
  | none   => rfl
  | some τ => exact congrArg some (Signature.pSubst_empty τ)

end LambdaLab.Stlc.Named
