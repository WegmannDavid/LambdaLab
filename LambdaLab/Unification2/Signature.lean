import LambdaLab.Unification2.Substitution

/-! # Slim first-order signature

`Signature α` declares that `α` is the free term algebra over `Nat`-many
variables for the operation set `Constructor` (with arities given by
`arity`). Variables and constructor applications are unified into a
single bijection `Nat ⊕ (Σ c, Vector α (arity c)) ≃ α`.

`HasSubst α α` is **derived** from `Signature α` (see the instance at
the bottom of the file): all of `isFree`, `fresh`, and `pSubst` are
forced by structural recursion on `deconstruct`, so the substitution
semantics cannot disagree with the term structure. -/

class Signature (α : Type) where
  Constructor : Type
  arity : Constructor → Nat
  decEqConstructor : DecidableEq Constructor
  construct : Nat ⊕ (Σ c : Constructor, Vector α (arity c)) → α
  deconstruct : α → Nat ⊕ (Σ c : Constructor, Vector α (arity c))
  size : α → Nat

  construct_deconstruct : ∀ a, deconstruct (construct a) = a
  deconstruct_construct : ∀ a, construct (deconstruct a) = a
  size_construct_var : ∀ n, size (construct (Sum.inl n)) = 1
  size_construct : ∀ c args,
    size (construct (Sum.inr ⟨c, args⟩)) =
      1 + (List.finRange (arity c)).foldr
        (fun i acc => acc + size (args.get i)) 0

attribute [reducible] Signature.decEqConstructor
attribute [instance] Signature.decEqConstructor
attribute [simp] Signature.construct_deconstruct Signature.deconstruct_construct

abbrev Equation (α : Type) := α × α
abbrev Equations (α : Type) := List (Equation α)

/-- A bound index of a list contributes at most the running fold value
when the running fold sums values produced by `f`. -/
private theorem List.le_foldr_sumIdx {β : Type} (f : β → Nat) :
    ∀ (l : List β) (a : β), a ∈ l →
      f a ≤ l.foldr (fun i acc => acc + f i) 0 := by
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons x xs ih =>
      intro a h
      rcases List.mem_cons.mp h with rfl | hxs
      · simp only [List.foldr]; omega
      · have := ih a hxs
        simp only [List.foldr]; omega

namespace Signature
variable {α : Type} [Signature α]

/-- Each child has size strictly less than its parent. -/
theorem size_lt_of_get {t : α} {c : Constructor α}
    {args : Vector α (Signature.arity c)}
    (h : Signature.deconstruct t = Sum.inr ⟨c, args⟩)
    (i : Fin (Signature.arity c)) :
    Signature.size (args.get i) < Signature.size t := by
  have ht : t = Signature.construct (Sum.inr ⟨c, args⟩) := by
    have := Signature.deconstruct_construct (α := α) t
    rw [h] at this
    exact this.symm
  rw [ht, Signature.size_construct]
  have hmem : i ∈ List.finRange (Signature.arity c) := List.mem_finRange i
  have hbound := List.le_foldr_sumIdx (fun j : Fin (Signature.arity c) =>
              Signature.size (args.get j))
            (List.finRange (Signature.arity c)) i hmem
  simp only at hbound
  omega

/-! ## Derived operations -/

/-- Build the term that is exactly variable `n`. -/
@[inline] def var (n : Nat) : α := Signature.construct (Sum.inl n)

/-- Detect whether a term is a variable, and if so which one. -/
@[inline] def isVar (t : α) : Option Nat :=
  match Signature.deconstruct t with
  | Sum.inl n => some n
  | Sum.inr _ => none

set_option linter.unusedVariables false in
/-- Decidable occurs check. -/
def occurs (n : Nat) (t : α) : Bool :=
  match h : Signature.deconstruct t with
  | Sum.inl m => decide (m = n)
  | Sum.inr ⟨c, args⟩ =>
      (List.finRange (Signature.arity c)).any (fun (i : Fin (Signature.arity c)) =>
        occurs n (args.get i))
  termination_by Signature.size t
  decreasing_by
    apply size_lt_of_get <;> assumption

/-- Fresh variable index: 1 + max free-variable index in `t`,
    or 0 if `t` has no free variables. -/
def fresh (t : α) : Nat :=
  match h : Signature.deconstruct t with
  | Sum.inl n => n + 1
  | Sum.inr ⟨c, args⟩ =>
      (List.finRange (Signature.arity c)).foldr
        (fun (i : Fin (Signature.arity c)) (acc : Nat) =>
          max acc (fresh (args.get i)))
        0
  termination_by Signature.size t
  decreasing_by
    apply size_lt_of_get <;> assumption

set_option linter.unusedVariables false in
/-- Apply a parallel substitution. Variables look themselves up in the
    substitution (default: keep the variable); constructors recurse
    structurally. -/
def pSubst (t : α) (σ : Subst α) : α :=
  match h : Signature.deconstruct t with
  | Sum.inl n => σ.getD n t
  | Sum.inr ⟨c, args⟩ =>
      Signature.construct (Sum.inr ⟨c, Vector.ofFn (fun (i : Fin (Signature.arity c)) =>
        pSubst (args.get i) σ)⟩)
  termination_by Signature.size t
  decreasing_by
    apply size_lt_of_get <;> assumption

/-! ## Equational unfolding for the derived operations

The recursive defs use `match h :` for termination, which makes plain
`rw` choke on the dependent match. We unfold via `simp only` with the
relevant `Signature` law as a rewrite rule — `simp` can rewrite under
dependent matches by reducing the discriminant. -/

theorem occurs_var (n m : Nat) :
    occurs (α := α) n (var m) = decide (m = n) := by
  unfold occurs var
  split
  · rename_i m' h
    rw [Signature.construct_deconstruct] at h
    cases h; rfl
  · rename_i c args h
    rw [Signature.construct_deconstruct] at h
    nomatch h

theorem occurs_construct (n : Nat) (c : Constructor α)
    (args : Vector α (Signature.arity c)) :
    occurs n (Signature.construct (Sum.inr ⟨c, args⟩)) =
      (List.finRange (Signature.arity c)).any (fun i => occurs n (args.get i)) := by
  rw [occurs.eq_def]
  split
  · rename_i m h
    rw [Signature.construct_deconstruct] at h
    nomatch h
  · rename_i c' args' h
    rw [Signature.construct_deconstruct] at h
    cases h; rfl

theorem fresh_var (n : Nat) : fresh (var n : α) = n + 1 := by
  unfold fresh var
  split
  · rename_i m h
    rw [Signature.construct_deconstruct] at h
    cases h; rfl
  · rename_i c args h
    rw [Signature.construct_deconstruct] at h
    nomatch h

theorem fresh_construct (c : Constructor α) (args : Vector α (Signature.arity c)) :
    fresh (Signature.construct (Sum.inr ⟨c, args⟩)) =
      (List.finRange (Signature.arity c)).foldr
        (fun i acc => max acc (fresh (args.get i))) 0 := by
  rw [fresh.eq_def]
  split
  · rename_i n h
    rw [Signature.construct_deconstruct] at h
    nomatch h
  · rename_i c' args' h
    rw [Signature.construct_deconstruct] at h
    cases h; rfl

theorem pSubst_var (n : Nat) (σ : Subst α) :
    pSubst (var n) σ = σ.getD n (var n) := by
  unfold pSubst var
  split
  · rename_i m h
    rw [Signature.construct_deconstruct] at h
    cases h; rfl
  · rename_i c args h
    rw [Signature.construct_deconstruct] at h
    nomatch h

theorem pSubst_construct (c : Constructor α)
    (args : Vector α (Signature.arity c)) (σ : Subst α) :
    pSubst (Signature.construct (Sum.inr ⟨c, args⟩)) σ =
      Signature.construct (Sum.inr ⟨c, Vector.ofFn (fun i => pSubst (args.get i) σ)⟩) := by
  rw [pSubst.eq_def]
  split
  · rename_i m h
    rw [Signature.construct_deconstruct] at h
    nomatch h
  · rename_i c' args' h
    rw [Signature.construct_deconstruct] at h
    cases h; rfl

/-! ## `fresh` strictly dominates every free variable. -/

theorem fresh_gt_occurs : ∀ (t : α) (n : Nat),
    occurs n t = true → n < fresh t := by
  intro t n
  induction hk : Signature.size t using Nat.strongRecOn generalizing t with
  | _ k ih =>
    intro hocc
    match hd : Signature.deconstruct t with
    | Sum.inl m =>
        have ht : t = var m := by
          have := Signature.deconstruct_construct (α := α) t
          rw [hd] at this
          exact this.symm
        rw [ht] at hocc
        rw [occurs_var] at hocc
        have hmn : m = n := of_decide_eq_true hocc
        rw [ht, fresh_var]
        omega
    | Sum.inr ⟨c, args⟩ =>
        have ht : t = Signature.construct (Sum.inr ⟨c, args⟩) := by
          have := Signature.deconstruct_construct (α := α) t
          rw [hd] at this
          exact this.symm
        rw [ht] at hocc
        rw [occurs_construct] at hocc
        rw [List.any_eq_true] at hocc
        obtain ⟨i, _, hi⟩ := hocc
        have hsz : Signature.size (args.get i) < Signature.size t :=
          size_lt_of_get hd i
        have hsz' : Signature.size (args.get i) < k := hk ▸ hsz
        have ihi : n < fresh (args.get i) :=
          ih (Signature.size (args.get i)) hsz' (args.get i) rfl hi
        rw [ht, fresh_construct]
        clear hsz hsz' ih hk
        have hmem : i ∈ List.finRange (Signature.arity c) := List.mem_finRange i
        revert hmem
        induction List.finRange (Signature.arity c) with
        | nil => intro h; cases h
        | cons j js ihl =>
            intro hmem
            simp only [List.foldr]
            rcases List.mem_cons.mp hmem with rfl | hj
            · exact Nat.lt_of_lt_of_le ihi (Nat.le_max_right _ _)
            · exact Nat.lt_of_lt_of_le (ihl hj) (Nat.le_max_left _ _)

/-! ## Derived `HasSubst α α` instance -/

instance instHasVars : HasVars α where
  isFree t n := occurs n t = true
  fresh := fresh
  fresh_gt_free := fresh_gt_occurs

instance instHasSubst : HasSubst α α where
  pSubst := pSubst

/-! ## Basic lemmas about `var` / `isVar` / `size` -/

theorem isVar_var (n : Nat) : isVar (var n : α) = some n := by
  unfold isVar var
  simp

theorem var_of_isVar (t : α) (n : Nat) : isVar t = some n → t = var n := by
  unfold isVar var
  intro h
  split at h
  · rename_i m hd
    cases h
    have := Signature.deconstruct_construct (α := α) t
    rw [hd] at this
    exact this.symm
  · cases h

theorem size_var (n : Nat) : Signature.size (var n : α) = 1 := by
  unfold var
  exact Signature.size_construct_var n

theorem var_isFree (n m : Nat) : HasVars.isFree (var n : α) m ↔ m = n := by
  show occurs m (var n) = true ↔ m = n
  rw [occurs_var]
  constructor
  · intro h; exact (of_decide_eq_true h).symm
  · intro h; subst h; simp

/-! ## Decomposition

`decomp x y` matches the outermost constructors of `x` and `y`. If they
match, returns the per-argument subgoals; otherwise `none`. Does not
fire on variables. -/

/-- One step of constructor matching: pair up children when heads agree. -/
def decomp (x y : α) : Option (Equations α) :=
  match Signature.deconstruct x, Signature.deconstruct y with
  | Sum.inr ⟨cx, argsx⟩, Sum.inr ⟨cy, argsy⟩ =>
      if h : cx = cy then
        some ((List.finRange (Signature.arity cx)).map
          (fun i => (argsx.get i, argsy.get (h ▸ i))))
      else none
  | _, _ => none

theorem decomp_var_left (n : Nat) (y : α) : decomp (var n) y = none := by
  unfold decomp var
  simp

theorem decomp_var_right (x : α) (n : Nat) : decomp x (var n) = none := by
  unfold decomp var
  split <;> simp_all

end Signature

/-! ## Most-generality and the unifier API -/

/-- `MoreGeneral σ σ'` says σ is at least as general as σ': there exists
some τ such that, on every term, applying σ' is the same as applying σ
then τ. Reflexive (witness τ = `∅`, modulo `pSubst t ∅ = t`); the name
covers both strictly-more-general and equally-general cases. -/
def MoreGeneral {α : Type} [Signature α] (σ σ' : Subst α) : Prop :=
  ∃ τ : Subst α, ∀ t : α,
    HasSubst.pSubst t σ' = HasSubst.pSubst (HasSubst.pSubst t σ) τ

/-- A unifier as an iterated single-binding sequence. The MGU computed
by `unify` is returned in this form, with bindings applied left-to-right
via `Unifier.apply`. -/
abbrev Unifier (α : Type) := List (Nat × α)

namespace Unifier

/-- Apply a unifier to a term: each `(n, s)` binding is applied as a
single substitution, in order from the head. -/
def apply {α : Type} [Signature α] (u : Unifier α) (t : α) : α :=
  u.foldl (fun acc p => HasSubst.single acc p.1 p.2) t

@[simp] theorem apply_nil {α : Type} [Signature α] (t : α) :
    apply [] t = t := rfl

@[simp] theorem apply_cons {α : Type} [Signature α] (n : Nat) (s : α)
    (rest : Unifier α) (t : α) :
    apply ((n, s) :: rest) t = apply rest (HasSubst.single t n s) := rfl

@[simp] theorem apply_append {α : Type} [Signature α]
    (u₁ u₂ : Unifier α) (t : α) :
    (u₁ ++ u₂).apply t = u₂.apply (u₁.apply t) := by
  show List.foldl _ _ _ = _
  rw [List.foldl_append]
  rfl

end Unifier

/-- A unifier (in the algebraic sense) of an equation set: makes every
equation true under `Unifier.apply`. -/
abbrev Unifier.Unifies {α : Type} [Signature α]
    (σ : Unifier α) (eqs : Equations α) : Prop :=
  ∀ p ∈ eqs, σ.apply p.1 = σ.apply p.2

/-! ## Trivial bridge lemmas about substitution-on-equations.

The deeper bridge lemmas connecting `unify`-style unifiers to
constructor decomposition (`unifier_absorb`, `decomp_unifier_sound`,
`occurs_no_unifier`, …) are proved later as theorems about the slim
`Signature` typeclass. -/

/-- Substitution on an equation set is pointwise on each component. -/
theorem Equations.single_eq {α : Type} [Signature α]
    (eqs : Equations α) (n : Nat) (s : α) :
    HasSubst.single eqs n s =
      eqs.map (fun p => (HasSubst.single p.1 n s, HasSubst.single p.2 n s)) :=
  rfl
