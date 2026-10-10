import LambdaLab.Stlc.DeBruijn.Substitution

/-!
# Parallel substitution

A `Subst` is a function `Nat → Term` assigning a term to every de Bruijn
index. Applying a `Subst σ` to a term substitutes every free variable
simultaneously, lifting `σ` when crossing a binder.
-/

namespace LambdaLab.Stlc.DeBruijn

/-! ## Definitions -/

abbrev Subst := Nat → Term

def Subst.id : Subst := fun n => .var n

def Subst.cons (v : Term) (σ : Subst) : Subst
  | 0 => v
  | n + 1 => σ n

def Subst.lift (σ : Subst) : Subst
  | 0 => .var 0
  | n + 1 => (σ n).shift 0

def Term.psubst (σ : Subst) : Term → Term
  | .var n => σ n
  | .lam τ e => .lam τ (e.psubst σ.lift)
  | .app e₁ e₂ => .app (e₁.psubst σ) (e₂.psubst σ)

/-! ## Definitional unfoldings (for `simp`) -/

@[simp] theorem Subst.cons_zero (v : Term) (σ : Subst) :
    Subst.cons v σ 0 = v := rfl

@[simp] theorem Subst.cons_succ (v : Term) (σ : Subst) (n : Nat) :
    Subst.cons v σ (n + 1) = σ n := rfl

@[simp] theorem Subst.lift_zero (σ : Subst) : Subst.lift σ 0 = .var 0 := rfl

@[simp] theorem Subst.lift_succ (σ : Subst) (n : Nat) :
    Subst.lift σ (n + 1) = (σ n).shift 0 := rfl

/-! ## Identity substitution -/

@[simp] theorem Subst.lift_id : Subst.id.lift = Subst.id := by
  funext n
  cases n with
  | zero => rfl
  | succ m => simp [Subst.id, Subst.lift, Term.shift]

theorem Term.psubst_id (e : Term) : e.psubst Subst.id = e := by
  induction e with
  | var n => rfl
  | lam τ e ih =>
      simp only [Term.psubst, Subst.lift_id]
      rw [ih]
  | app e₁ e₂ ih₁ ih₂ =>
      simp only [Term.psubst]
      rw [ih₁, ih₂]

/-! ## Pushing a single substitution through a parallel one

The key composition lemma: applying `σ` then a single `subst k v` is the
same as applying the substitution that, for each variable, first applies
`σ` and then `subst k v`.
-/

theorem Term.psubst_subst (e : Term) :
    ∀ (σ : Subst) (k : Nat) (v : Term),
    (e.psubst σ).subst k v = e.psubst (fun n => (σ n).subst k v) := by
  induction e with
  | var n =>
      intro σ k v
      simp [Term.psubst]
  | lam τ body ih =>
      intro σ k v
      simp only [Term.psubst, Term.subst]
      congr 1
      rw [ih σ.lift (k+1) (v.shift 0)]
      congr 1
      funext n
      cases n with
      | zero => simp [Subst.lift, Term.subst]
      | succ m =>
          simp only [Subst.lift]
          exact (Term.shift_subst_le (σ m) v (Nat.zero_le k)).symm
  | app e₁ e₂ ih₁ ih₂ =>
      intro σ k v
      simp only [Term.psubst, Term.subst]
      rw [ih₁ σ k v, ih₂ σ k v]

/-! ## Single subst as a parallel subst -/

theorem Term.subst_zero_eq_psubst (e v : Term) :
    e.subst 0 v = e.psubst (Subst.cons v Subst.id) := by
  have key := Term.psubst_subst e Subst.id 0 v
  rw [Term.psubst_id] at key
  rw [key]
  congr 1
  funext n
  cases n with
  | zero => simp [Subst.id, Term.subst]
  | succ m => simp [Subst.id, Term.subst]

/-! ## The β-redex lemma needed for SN -/

/-- Going under a binder via `lift`, then β-reducing with `v`, equals the
parallel substitution `cons v σ`. -/
theorem Term.psubst_lift_beta (e : Term) (σ : Subst) (v : Term) :
    (e.psubst σ.lift).subst 0 v = e.psubst (Subst.cons v σ) := by
  rw [Term.psubst_subst]
  congr 1
  funext n
  cases n with
  | zero => simp [Subst.lift, Term.subst]
  | succ m =>
      simp only [Subst.lift, Subst.cons]
      exact Term.shift_subst_cancel (σ m) 0 v

end LambdaLab.Stlc.DeBruijn
