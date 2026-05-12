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

/-! ## `pSubst` unfolding lemmas for each `Ty` constructor. -/

@[simp] theorem Ty.pSubst_base (σ : Subst Ty) :
    HasSubst.pSubst Ty.base σ = Ty.base := by
  show Signature.pSubst Ty.base σ = _
  show Signature.pSubst (Signature.construct (Sum.inr
        ⟨TyConstructor.base, Vector.ofFn Fin.elim0⟩)) σ = _
  rw [Signature.pSubst_construct]
  rfl

@[simp] theorem Ty.pSubst_mvar (n : Nat) (σ : Subst Ty) :
    HasSubst.pSubst (Ty.mvar n) σ = σ.getD n (Ty.mvar n) := by
  show Signature.pSubst (Signature.var n : Ty) σ = _
  exact Signature.pSubst_var n σ

@[simp] theorem Ty.pSubst_arrow (a b : Ty) (σ : Subst Ty) :
    HasSubst.pSubst (Ty.arrow a b) σ =
      Ty.arrow (HasSubst.pSubst a σ) (HasSubst.pSubst b σ) := by
  show Signature.pSubst (Signature.construct (Sum.inr ⟨TyConstructor.arrow,
        Vector.ofFn (fun i : Fin 2 =>
          match i with | 0 => a | 1 => b)⟩)) σ = _
  rw [Signature.pSubst_construct]
  show Signature.construct (Sum.inr ⟨TyConstructor.arrow,
        Vector.ofFn fun i : Fin 2 => Signature.pSubst
          ((Vector.ofFn (fun j : Fin 2 =>
            match j with | 0 => a | 1 => b)).get i) σ⟩) = _
  show Ty.arrow ((Vector.ofFn _).get 0) ((Vector.ofFn _).get 1) = _
  have h0 : (Vector.ofFn (fun j : Fin 2 =>
            match j with | 0 => a | 1 => b)).get 0 = a := by
    show ((Vector.ofFn _)[(0 : Fin 2).val]'(0 : Fin 2).isLt) = _
    simp
  have h1 : (Vector.ofFn (fun j : Fin 2 =>
            match j with | 0 => a | 1 => b)).get 1 = b := by
    show ((Vector.ofFn _)[(1 : Fin 2).val]'(1 : Fin 2).isLt) = _
    simp
  show Ty.arrow (Signature.pSubst ((Vector.ofFn _).get 0) σ)
                (Signature.pSubst ((Vector.ofFn _).get 1) σ) = _
  rw [h0, h1]
  rfl

/-! ## How `pSubst` interacts with `Ctx` lookup. -/

/-- Looking up a key in a `σ`-substituted context returns the
`σ`-substituted value. -/
theorem HashMap.pSubst_get? (Γ : Std.HashMap String Ty) (σ : Subst Ty)
    (x : String) :
    (HasSubst.pSubst Γ σ).get? x =
      (Γ.get? x).map (fun τ => HasSubst.pSubst τ σ) := by
  show (Γ.map (fun _ v => HasSubst.pSubst v σ)).get? x = _
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map,
      ← Std.HashMap.get?_eq_getElem?]

end LambdaLab.Stlc.Named
