import LambdaLab.Stlc.DeBruijn.Basic
import LambdaLab.Nominal.Unification.Basic
import LambdaLab.Nominal.Instances

/-!
# `Signature` and substitution instances for the de Bruijn STLC

The mirror of `Stlc/Named/Typing/Unification.lean`'s instance layer, deliberately proved
*independently* rather than transported along `Ty.toDB`: the de Bruijn variant is the reference
the named formalization is checked against, so its instances must not be borrowed from the side
they are meant to audit. The two `Ty`s are the same first-order algebra — `mvar` the variable
position, `base` and `arrow` the 0- and 2-ary constructors — so the proofs are the named ones
with the constructors re-read, and that they go through unchanged is itself a small instance of
the mirroring the two variants exist for.

The term side substitutes type metavariables in *annotations*: the "variables" of a `Term` for a
`Subst Nat Ty` are the `Ty.mvar` indices under its `lam`s. One case shorter than the named
version everywhere, because `lam` carries no binder name.
-/

namespace LambdaLab.Stlc.DeBruijn

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

instance : Signature Nat Ty where
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

/-! ## `HasSubst Nat Term Ty` — substitute `Ty.mvar`s in annotations -/

namespace Term

def tyIsFree : Term → Nat → Prop
  | .var _,      _ => False
  | .lam τ body, n => HasVars.isFree τ n ∨ tyIsFree body n
  | .app e₁ e₂,  n => tyIsFree e₁ n ∨ tyIsFree e₂ n

/-- The type metavariables occurring in `e`'s annotations. -/
def tySupp : Term → List Nat
  | .var _      => []
  | .lam τ body => HasVars.supp (A := Nat) τ ++ tySupp body
  | .app e₁ e₂  => tySupp e₁ ++ tySupp e₂

theorem mem_tySupp_iff_tyIsFree : ∀ (e : Term) (n : Nat),
    n ∈ tySupp e ↔ tyIsFree e n := by
  intro e
  induction e with
  | var _ => intro n; simp only [tySupp, tyIsFree, List.not_mem_nil]
  | lam τ body ih =>
      intro n
      simp only [tySupp, tyIsFree, List.mem_append, HasVars.mem_supp_iff_isFree, ih]
  | app e₁ e₂ ih₁ ih₂ =>
      intro n
      simp only [tySupp, tyIsFree, List.mem_append, ih₁, ih₂]

def tyPSubst : Term → Subst Nat Ty → Term
  | .var x,      _ => .var x
  | .lam τ body, σ => .lam (HasSubst.pSubst τ σ) (tyPSubst body σ)
  | .app e₁ e₂,  σ => .app (tyPSubst e₁ σ) (tyPSubst e₂ σ)

end Term

instance : HasVars Nat Term where
  isFree := Term.tyIsFree
  supp := Term.tySupp
  mem_supp_iff_isFree := Term.mem_tySupp_iff_tyIsFree

instance : HasSubst Nat Term Ty where
  pSubst := Term.tyPSubst

end LambdaLab.Stlc.DeBruijn
