import LambdaLab.Nominal.Unification.Subst

/-! # Slim first-order signature

`Signature α` declares that `α` is the free term algebra over `Nat`-many
variables for the operation set `Constructor` (with arities given by
`arity`). Variables and constructor applications are unified into a
single bijection `Nat ⊕ (Σ c, Vector α (arity c)) ≃ α`.

`HasSubst α α` is **derived** from `Signature α` (see the instance at
the bottom of the file): all of `isFree`, `fresh`, and `pSubst` are
forced by structural recursion on `deconstruct`, so the substitution
semantics cannot disagree with the term structure. -/

open LambdaLab.Nominal

class Signature (A : outParam Type) (α : Type) [Atom A] where
  Constructor : Type
  arity : Constructor → Nat
  decEqConstructor : DecidableEq Constructor
  construct : A ⊕ (Σ c : Constructor, Vector α (arity c)) → α
  deconstruct : α → A ⊕ (Σ c : Constructor, Vector α (arity c))
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
variable {A α : Type} [Atom A] [Signature A α]

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
@[inline] def var (n : A) : α := Signature.construct (Sum.inl n)

/-- Detect whether a term is a variable, and if so which one. -/
@[inline] def isVar (t : α) : Option A :=
  match Signature.deconstruct t with
  | Sum.inl n => some n
  | Sum.inr _ => none

set_option linter.unusedVariables false in
/-- Decidable occurs check. -/
def occurs (n : A) (t : α) : Bool :=
  match h : Signature.deconstruct t with
  | Sum.inl m => decide (m = n)
  | Sum.inr ⟨c, args⟩ =>
      (List.finRange (Signature.arity c)).any (fun (i : Fin (Signature.arity c)) =>
        occurs n (args.get i))
  termination_by Signature.size t
  decreasing_by
    apply size_lt_of_get <;> assumption

set_option linter.unusedVariables false in
/-- The variables occurring in `t`, with multiplicity.

The order-free counterpart of `fresh`: where `fresh` bounds the variables in `Nat`'s order, this
lists them. Everything the termination measure actually needs is *how many distinct variables
there are*, which is a fact about the list and not about the order — see
`Unification/Measure.lean`. -/
def vars (t : α) : List A :=
  match h : Signature.deconstruct t with
  | Sum.inl n => [n]
  | Sum.inr ⟨c, args⟩ =>
      (List.finRange (Signature.arity c)).flatMap (fun (i : Fin (Signature.arity c)) =>
        vars (args.get i))
  termination_by Signature.size t
  decreasing_by
    apply size_lt_of_get <;> assumption

set_option linter.unusedVariables false in
/-- Apply a parallel substitution. Variables look themselves up in the
    substitution (default: keep the variable); constructors recurse
    structurally. -/
def pSubst (t : α) (σ : Subst A α) : α :=
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

theorem occurs_var (n m : A) :
    occurs (α := α) n (var m) = decide (m = n) := by
  unfold occurs var
  split
  · rename_i m' h
    rw [Signature.construct_deconstruct] at h
    cases h; rfl
  · rename_i c args h
    rw [Signature.construct_deconstruct] at h
    nomatch h

theorem occurs_construct (n : A) (c : Constructor α)
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

/-! ## Structural induction on terms.

Any property that holds for variables and is preserved by constructor
application (assuming it holds for all children) holds for every term.
The "subterms have strictly smaller size" fact (`size_lt_of_get`) makes
this well-founded. -/

theorem term_ind {motive : α → Prop}
    (var_case : ∀ n, motive (var n))
    (construct_case : ∀ (c : Constructor α) (args : Vector α (arity c)),
       (∀ i : Fin (arity c), motive (args.get i)) →
       motive (construct (Sum.inr ⟨c, args⟩))) :
    ∀ t : α, motive t := by
  intro t
  induction hk : size t using Nat.strongRecOn generalizing t with
  | _ k ih =>
    match hd : deconstruct t with
    | Sum.inl m =>
        have ht : t = var m := by
          have := deconstruct_construct (α := α) t
          rw [hd] at this
          exact this.symm
        rw [ht]
        exact var_case m
    | Sum.inr ⟨c, args⟩ =>
        have ht : t = construct (Sum.inr ⟨c, args⟩) := by
          have := deconstruct_construct (α := α) t
          rw [hd] at this
          exact this.symm
        rw [ht]
        apply construct_case
        intro i
        have hsz : size (args.get i) < size t := size_lt_of_get hd i
        have hsz' : size (args.get i) < k := hk ▸ hsz
        exact ih _ hsz' _ rfl

theorem vars_var (n : A) : vars (var n : α) = [n] := by
  unfold vars var
  split
  · rename_i m h
    rw [Signature.construct_deconstruct] at h
    cases h; rfl
  · rename_i c args h
    rw [Signature.construct_deconstruct] at h
    nomatch h

theorem vars_construct (c : Constructor α) (args : Vector α (Signature.arity c)) :
    vars (Signature.construct (Sum.inr ⟨c, args⟩)) =
      (List.finRange (Signature.arity c)).flatMap (fun i => vars (args.get i)) := by
  rw [vars.eq_def]
  split
  · rename_i n h
    rw [Signature.construct_deconstruct] at h
    nomatch h
  · rename_i c' args' h
    rw [Signature.construct_deconstruct] at h
    cases h; rfl

/-- **`vars` and `occurs` agree.** The bridge that lets a measure count list membership instead of
searching an initial segment of `Nat`. -/
theorem mem_vars_iff_occurs (n : A) (t : α) : n ∈ vars t ↔ occurs n t = true := by
  induction t using term_ind with
  | var_case m =>
      rw [vars_var, occurs_var]
      simp [eq_comm]
  | construct_case c args ih =>
      rw [vars_construct, occurs_construct]
      simp only [List.mem_flatMap, List.any_eq_true]
      constructor
      · rintro ⟨i, hi, hmem⟩
        exact ⟨i, hi, (ih i).mp hmem⟩
      · rintro ⟨i, hi, hocc⟩
        exact ⟨i, hi, (ih i).mpr hocc⟩

theorem pSubst_var (n : A) (σ : Subst A α) :
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
    (args : Vector α (Signature.arity c)) (σ : Subst A α) :
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

/-! ## Derived `HasSubst α α` instance -/

instance instHasVars : HasVars A α where
  isFree t n := occurs n t = true
  supp := vars
  mem_supp_iff_isFree t n := mem_vars_iff_occurs n t

instance instHasSubst : HasSubst A α α where
  pSubst := pSubst

/-- `isFree` on a signature's own type is the occurs check, definitionally — as in the old
class. What is new is that `vars` lists exactly those atoms (`mem_vars_iff_occurs`), which is what
the instance's `mem_supp_iff_isFree` field is discharged by. -/
theorem isFree_iff_occurs (t : α) (n : A) :
    HasVars.isFree (A := A) t n ↔ occurs n t = true := Iff.rfl

/-! ## Basic lemmas about `var` / `isVar` / `size` -/

theorem isVar_var (n : A) : isVar (var n : α) = some n := by
  unfold isVar var
  simp

theorem var_of_isVar (t : α) (n : A) : isVar t = some n → t = var n := by
  unfold isVar var
  intro h
  split at h
  · rename_i m hd
    cases h
    have := Signature.deconstruct_construct (α := α) t
    rw [hd] at this
    exact this.symm
  · cases h

theorem size_var (n : A) : Signature.size (var n : α) = 1 := by
  unfold var
  exact Signature.size_construct_var n

theorem var_isFree (n m : A) : HasVars.isFree (A := A) (var n : α) m ↔ m = n := by
  rw [isFree_iff_occurs, occurs_var]
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

theorem decomp_var_left (n : A) (y : α) : decomp (var n) y = none := by
  unfold decomp var
  simp

theorem decomp_var_right (x : α) (n : A) : decomp x (var n) = none := by
  unfold decomp var
  split <;> simp_all

end Signature

/-! ## Unifier API

`MoreGeneral` (the parallel-`Subst` version) lives in
`Subst.lean` since it only needs `HasSubst`. The `Unifier`
namespace below adds the list-form companion. -/

/-- A unifier as an iterated single-binding sequence. The MGU computed
by `unify` is returned in this form, with bindings applied left-to-right
via `Unifier.apply`. -/
abbrev Unifier (A α : Type) := List (A × α)

namespace Unifier

/-- Apply a unifier to a term: each `(n, s)` binding is applied as a
single substitution, in order from the head. -/
def apply {A α : Type} [Atom A] [Signature A α] (u : Unifier A α) (t : α) : α :=
  u.foldl (fun acc p => HasSubst.single acc p.1 p.2) t

@[simp] theorem apply_nil {A α : Type} [Atom A] [Signature A α] (t : α) :
    apply [] t = t := rfl

@[simp] theorem apply_cons {A α : Type} [Atom A] [Signature A α] (n : A) (s : α)
    (rest : Unifier A α) (t : α) :
    apply ((n, s) :: rest) t = apply rest (HasSubst.single t n s) := rfl

@[simp] theorem apply_append {A α : Type} [Atom A] [Signature A α]
    (u₁ u₂ : Unifier A α) (t : α) :
    (u₁ ++ u₂).apply t = u₂.apply (u₁.apply t) := by
  show List.foldl _ _ _ = _
  rw [List.foldl_append]
  rfl

/-- Compress a unifier list into a single parallel `Subst α` with the
same semantic effect. Each binding `(n, s)` is recorded with the *rest*
of the unifier already pushed into `s`, so that one parallel pass agrees
with the iterated `apply`. See `apply_eq_pSubst_toSubst`. -/
def toSubst {A α : Type} [Atom A] [Signature A α] : Unifier A α → Subst A α
  | [] => ∅
  | (n, s) :: rest =>
      let σ := toSubst rest
      σ.insert n (HasSubst.pSubst s σ)

@[simp] theorem toSubst_nil {A α : Type} [Atom A] [Signature A α] :
    toSubst ([] : Unifier A α) = (∅ : Subst A α) := rfl

@[simp] theorem toSubst_cons {A α : Type} [Atom A] [Signature A α]
    (n : A) (s : α) (rest : Unifier A α) :
    toSubst ((n, s) :: rest) =
      (toSubst rest).insert n (HasSubst.pSubst s (toSubst rest)) := rfl

end Unifier

/-- A unifier (in the algebraic sense) of an equation set: makes every
equation true under `Unifier.apply`. -/
abbrev Unifier.Unifies {A α : Type} [Atom A] [Signature A α]
    (σ : Unifier A α) (eqs : Equations α) : Prop :=
  ∀ p ∈ eqs, σ.apply p.1 = σ.apply p.2

/-- Pull out the head equation from a unifier of `(x, y) :: eqs'`. -/
theorem Unifier.Unifies.head_eq {A α : Type} [Atom A] [Signature A α]
    {σ : Unifier A α} {x y : α} {eqs' : Equations α}
    (hσ : σ.Unifies ((x, y) :: eqs')) : σ.apply x = σ.apply y := by
  simpa using hσ (x, y) List.mem_cons_self

/-! ## Trivial bridge lemmas about substitution-on-equations.

The deeper bridge lemmas connecting `unify`-style unifiers to
constructor decomposition (`unifier_absorb`, `decomp_unifier_sound`,
`occurs_no_unifier`, …) are proved later as theorems about the slim
`Signature` typeclass. -/

/-- Substitution on an equation set is pointwise on each component. -/
theorem Equations.single_eq {A α : Type} [Atom A] [Signature A α]
    (eqs : Equations α) (n : A) (s : α) :
    HasSubst.single eqs n s =
      eqs.map (fun p => (HasSubst.single p.1 n s, HasSubst.single p.2 n s)) :=
  rfl

