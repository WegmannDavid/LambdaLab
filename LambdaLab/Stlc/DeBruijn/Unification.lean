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

/-! ## `pSubst` unfolding lemmas for each `Ty` constructor

The `Signature`-derived `pSubst` recurses by well-founded recursion through `deconstruct`, so it
does not reduce on the constructors; these are the closed forms, as on the named side. -/

@[simp] theorem Ty.pSubst_base (σ : Subst Nat Ty) :
    HasSubst.pSubst Ty.base σ = Ty.base := by
  show Signature.pSubst Ty.base σ = _
  show Signature.pSubst (Signature.construct (Sum.inr
        ⟨TyConstructor.base, Vector.ofFn Fin.elim0⟩)) σ = _
  rw [Signature.pSubst_construct]
  rfl

@[simp] theorem Ty.pSubst_mvar (n : Nat) (σ : Subst Nat Ty) :
    HasSubst.pSubst (Ty.mvar n) σ = σ.getD n (Ty.mvar n) := by
  show Signature.pSubst (Signature.var n : Ty) σ = _
  exact Signature.pSubst_var n σ

@[simp] theorem Ty.pSubst_arrow (a b : Ty) (σ : Subst Nat Ty) :
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

/-! ## The substitution laws, term level

The three mixins `LawfulMVars` bundles, proved by the inductions the named side has — one case
shorter each, `lam` carrying no name. -/

theorem Term.pSubst_ground {e : Term} (σ : Subst Nat Ty)
    (h : HasVars.Ground (A := Nat) e) : HasSubst.pSubst e σ = e := by
  show Term.tyPSubst e σ = e
  induction e with
  | var x => rfl
  | lam τ body ih =>
      have hτ : HasVars.Ground (A := Nat) τ := fun n hn => h n (Or.inl hn)
      have hb : HasVars.Ground (A := Nat) body := fun n hn => h n (Or.inr hn)
      show Term.lam (HasSubst.pSubst τ σ) (Term.tyPSubst body σ) = _
      rw [GroundStable.pSubst_ground σ hτ, ih hb]
  | app e₁ e₂ ih₁ ih₂ =>
      have h₁ : HasVars.Ground (A := Nat) e₁ := fun n hn => h n (Or.inl hn)
      have h₂ : HasVars.Ground (A := Nat) e₂ := fun n hn => h n (Or.inr hn)
      show Term.app (Term.tyPSubst e₁ σ) (Term.tyPSubst e₂ σ) = _
      rw [ih₁ h₁, ih₂ h₂]

instance : GroundStable Nat Term Ty where
  pSubst_ground σ h := Term.pSubst_ground σ h

theorem Term.pSubst_comp (e : Term) (σ τ : Subst Nat Ty) :
    HasSubst.pSubst e (Subst.comp σ τ) = HasSubst.pSubst (HasSubst.pSubst e τ) σ := by
  show Term.tyPSubst e _ = Term.tyPSubst (Term.tyPSubst e τ) σ
  induction e with
  | var x => rfl
  | lam τa body ih =>
      show Term.lam (HasSubst.pSubst τa (Subst.comp σ τ)) (Term.tyPSubst body _)
        = Term.lam (HasSubst.pSubst (HasSubst.pSubst τa τ) σ) (Term.tyPSubst (Term.tyPSubst body τ) σ)
      rw [LawfulComp.pSubst_comp τa σ τ, ih]
  | app e₁ e₂ ih₁ ih₂ =>
      show Term.app _ _ = Term.app _ _
      rw [ih₁, ih₂]

instance : LawfulComp Nat Term Ty where
  pSubst_comp := Term.pSubst_comp

theorem Term.pSubst_restrictTo (e : Term) (σ : Subst Nat Ty) (s : List Nat)
    (h : ∀ a, HasVars.isFree e a → a ∈ s) :
    HasSubst.pSubst e (Subst.restrictTo σ s) = HasSubst.pSubst e σ := by
  show Term.tyPSubst e _ = Term.tyPSubst e σ
  induction e with
  | var x => rfl
  | lam τa body ih =>
      show Term.lam _ _ = Term.lam _ _
      rw [LawfulRestrict.pSubst_restrictTo τa σ s (fun a ha => h a (Or.inl ha)),
        ih (fun a ha => h a (Or.inr ha))]
  | app e₁ e₂ ih₁ ih₂ =>
      show Term.app _ _ = Term.app _ _
      rw [ih₁ (fun a ha => h a (Or.inl ha)), ih₂ (fun a ha => h a (Or.inr ha))]

instance : LawfulRestrict Nat Term Ty where
  pSubst_restrictTo := Term.pSubst_restrictTo

end LambdaLab.Stlc.DeBruijn
