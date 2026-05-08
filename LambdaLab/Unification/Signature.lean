import LambdaLab.Unification.Substitution

abbrev Equation α := (α × α)
abbrev Equations α := List (Equation α)

/-- A first-order signature, abstracted as a typeclass over a host type
`α` of terms. Provides:

* an injection `var : Nat → α` and projection `isVar` for variables,
* a `decomp` operation that does one step of constructor matching,
* a decidable `occurs` check (must agree with `HasVars.isFree`),
* a syntactic `size` that strictly drops under decomposition.

Variables and constructors are required not to overlap (`decomp` does
not fire on variables), and the variable injection/projection are
inverse on the variable subset. -/
class Signature (α : Type) extends HasSubst α α where
  /-- Build a term that is exactly the variable with the given index. -/
  var : Nat → α
  /-- Detect whether a term is a variable, and if so which one. -/
  isVar : α → Option Nat
  /-- Decompose two non-variable terms into subgoals. `none` if their
  outermost constructors don't match. -/
  decomp : α → α → Option (Equations α)
  /-- Decidable occurs check. -/
  occurs : Nat → α → Bool
  /-- Syntactic size. -/
  size : α → Nat

  /-- `var n` is detected as variable `n`. -/
  isVar_var : ∀ n, isVar (var n) = some n
  /-- A variable-detected term is exactly `var n`. -/
  var_of_isVar : ∀ a n, isVar a = some n → a = var n
  /-- `decomp` does not fire when its left argument is a variable. -/
  decomp_var_left : ∀ n y, decomp (var n) y = none
  /-- `decomp` does not fire when its right argument is a variable. -/
  decomp_var_right : ∀ x n, decomp x (var n) = none

  /-- The decidable occurs check matches `HasVars.isFree`. -/
  occurs_iff_isFree : ∀ n a, occurs n a = true ↔ HasVars.isFree a n
  /-- A variable has size one. -/
  size_var : ∀ n, size (var n) = 1
  /-- Decomposition strictly reduces total size. -/
  size_decomp : ∀ x y eqs, decomp x y = some eqs →
    eqs.foldr (fun p acc => acc + size p.1 + size p.2) 0 < size x + size y

  /-- Variables are free at exactly themselves. -/
  var_isFree : ∀ n m, HasVars.isFree (var n) m ↔ m = n
  /-- Substituting a variable with a singleton binding for it yields the
  binding's value. -/
  pSubst_var_eq : ∀ n s,
    HasSubst.pSubst (var n) ((∅ : Subst α).insert n s) = s
  /-- A singleton substitution at an off-free-vars index is the
  identity. -/
  single_off : ∀ (t : α) (n : Nat) (s : α),
    ¬ HasVars.isFree t n → HasSubst.single t n s = t
  /-- Structural soundness of decomposition: if `decomp x y = some xs`
  and every pair in `xs` is propositionally equal, then `x = y`. -/
  decomp_struct_sound : ∀ x y xs,
    decomp x y = some xs → (∀ p ∈ xs, p.1 = p.2) → x = y
  /-- Decomposition commutes with single-binding substitution: if
  `decomp x y = some xs` then substituting `[n ↦ s]` on both sides
  decomposes the same way, with each pair in `xs` substituted. -/
  decomp_single : ∀ x y xs n s,
    decomp x y = some xs →
    decomp (HasSubst.single x n s) (HasSubst.single y n s) =
      some (xs.map (fun p => (HasSubst.single p.1 n s, HasSubst.single p.2 n s)))
  /-- Free variables under single substitution: a variable `m` is free in
  `single t n s` iff either it was already free in `t` at a position other
  than `n`, or `n` was free in `t` and `m` is free in `s`. The standard
  free-variables-after-substitution characterization. -/
  single_isFree : ∀ (t : α) (n : Nat) (s : α) (m : Nat),
    HasVars.isFree (HasSubst.single t n s) m ↔
      (m ≠ n ∧ HasVars.isFree t m) ∨ (HasVars.isFree t n ∧ HasVars.isFree s m)
  /-- Decomposition does not introduce free variables: if a variable is
  free somewhere in the subgoals produced by `decomp x y`, it was already
  free in `x` or in `y`. -/
  decomp_isFree : ∀ x y xs n,
    decomp x y = some xs → HasVars.isFree xs n →
      HasVars.isFree x n ∨ HasVars.isFree y n
  /-- Substituting a variable for itself is the identity. -/
  single_var_self : ∀ (t : α) (n : Nat), HasSubst.single t n (var n) = t
  /-- **Absorption.** If a sequence of single substitutions identifies
  `var n` with `s`, then it absorbs an inner `single n s`: prepending
  `single n s` doesn't change the result. The fundamental MGU lemma at
  the iterated-single (i.e., `Unifier.apply`) level. -/
  unifier_absorb : ∀ (l : List (Nat × α)) (t : α) (n : Nat) (s : α),
    l.foldl (fun acc p => HasSubst.single acc p.1 p.2) (var n) =
      l.foldl (fun acc p => HasSubst.single acc p.1 p.2) s →
    l.foldl (fun acc p => HasSubst.single acc p.1 p.2) (HasSubst.single t n s) =
      l.foldl (fun acc p => HasSubst.single acc p.1 p.2) t
  /-- **Decomposition under unifier**: if a sequence of single
  substitutions equates `x` and `y`, and `decomp x y = some xs`, then it
  also equates each pair in `xs`. The reverse direction of
  `decomp_apply_sound`. -/
  decomp_unifier_sound : ∀ (x y : α) (xs : Equations α) (l : List (Nat × α)),
    decomp x y = some xs →
    l.foldl (fun acc p => HasSubst.single acc p.1 p.2) x =
      l.foldl (fun acc p => HasSubst.single acc p.1 p.2) y →
    ∀ p ∈ xs,
      l.foldl (fun acc p => HasSubst.single acc p.1 p.2) p.1 =
        l.foldl (fun acc p => HasSubst.single acc p.1 p.2) p.2
  /-- **Occurs-check completeness.** If `t` mentions variable `n` but is
  not just `var n`, no sequence of single substitutions can equate
  `var n` with `t`. The structural fact behind the occurs check. -/
  occurs_no_unifier : ∀ (t : α) (n : Nat) (l : List (Nat × α)),
    HasVars.isFree t n → isVar t ≠ some n →
    l.foldl (fun acc p => HasSubst.single acc p.1 p.2) (var n) ≠
      l.foldl (fun acc p => HasSubst.single acc p.1 p.2) t
  /-- **Decomposition-failure completeness.** If `x` and `y` are both
  non-variable and have mismatched outermost constructors (`decomp` is
  `none`), no sequence of single substitutions can equate them. -/
  decomp_none_no_unifier : ∀ (x y : α) (l : List (Nat × α)),
    isVar x = none → isVar y = none → decomp x y = none →
    l.foldl (fun acc p => HasSubst.single acc p.1 p.2) x ≠
      l.foldl (fun acc p => HasSubst.single acc p.1 p.2) y

/-- `MoreGeneral σ σ'` says σ is at least as general as σ': there exists
some τ such that, on every term, applying σ' is the same as applying σ
then τ. Reflexive (witness τ = `∅`, modulo `pSubst t ∅ = t`); the name
covers both strictly-more-general and equally-general cases.

Stated extensionally over the action on terms of type α — this is the
classical unification-theory definition and avoids committing to an
algebraic notion of substitution composition. -/
def MoreGeneral {α : Type} [HasSubst α α] (σ σ' : Subst α) : Prop :=
  ∃ τ : Subst α, ∀ t : α,
    HasSubst.pSubst t σ' = HasSubst.pSubst (HasSubst.pSubst t σ) τ

abbrev Unifier α := List (Nat × α)
