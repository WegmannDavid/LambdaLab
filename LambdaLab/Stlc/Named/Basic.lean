/-!
# Simply Typed Lambda Calculus (STLC), named-variable presentation

Variables are `String`s. Substitution is *capture-avoiding*: when entering a
binder whose bound variable would capture a free variable of the substituted
value, the binder is α-renamed to a fresh name first.

Termination of `Term.subst` is by term size, not structural recursion: in
the α-renaming branch, we recurse on `body.rename y z` whose size equals
`body.size` (proved by `Term.rename_size`).
-/

namespace LambdaLab.Stlc.Named

/-! ## Types -/

/-- Types include unification metavariables:
* `mvar n` — unification metavariable, identified by a unique `Nat`.
  Created by the parser (fresh per `_`) and the elaborator's app rule;
  eliminated by substitution. -/
inductive Ty where
  | base : Ty
  | arrow : Ty → Ty → Ty
  | mvar : Nat → Ty
  deriving DecidableEq, Repr

infixr:25 " ⇒ " => Ty.arrow

/-- A type is *ground* when it contains no `mvar`. The kernel typing
relation `HasType` and the bridge to the de Bruijn variant only expect
ground types. -/
def Ty.isGround : Ty → Bool
  | .base       => true
  | .arrow a b  => a.isGround && b.isGround
  | .mvar _     => false

abbrev Ty.Ground (τ : Ty) : Prop := τ.isGround = true

@[simp] theorem Ty.Ground.base : Ty.base.Ground := rfl

@[simp] theorem Ty.Ground.arrow {a b : Ty} :
    (a ⇒ b).Ground ↔ a.Ground ∧ b.Ground := by
  simp [Ty.Ground, Ty.isGround]

@[simp] theorem Ty.Ground.mvar (n : Nat) : ¬ (Ty.mvar n).Ground := by
  simp [Ty.Ground, Ty.isGround]

/-! ## Terms -/

inductive Term where
  | var : String → Term
  | lam : String → Ty → Term → Term
  | app : Term → Term → Term
  deriving Repr

/-- Every type annotation inside `e` is ground (no `.mvar`). -/
def Term.AnnotsGround : Term → Prop
  | .var _        => True
  | .lam _ τ body => τ.Ground ∧ body.AnnotsGround
  | .app e₁ e₂    => e₁.AnnotsGround ∧ e₂.AnnotsGround

/-! ## Free variables and term size -/

def Term.freeVars : Term → List String
  | .var x        => [x]
  | .lam y _ body => body.freeVars.filter (· ≠ y)
  | .app e₁ e₂    => e₁.freeVars ++ e₂.freeVars

/-- All variables (free and bound) appearing in a term — used to pick a
fresh name that's also fresh from binders, not just free variables. -/
def Term.allVars : Term → List String
  | .var x        => [x]
  | .lam y _ body => y :: body.allVars
  | .app e₁ e₂    => e₁.allVars ++ e₂.allVars

def Term.size : Term → Nat
  | .var _        => 1
  | .lam _ _ body => 1 + body.size
  | .app e₁ e₂    => 1 + e₁.size + e₂.size

/-- Every free variable is also an `allVars` entry. -/
theorem Term.freeVars_subset_allVars (e : Term) (x : String) :
    x ∈ e.freeVars → x ∈ e.allVars := by
  induction e <;> grind [Term.freeVars, Term.allVars]

/-! ## Fresh-variable generator

`freshFor used` returns a string strictly longer than every string in `used`,
hence not present in `used`.
-/

def freshFor (used : List String) : String :=
  String.ofList (List.replicate ((used.map String.length).foldr max 0 + 1) 'a')

/-- Every element of `l` is bounded above by `l.foldr max 0`. -/
private theorem le_foldr_max :
    ∀ (l : List Nat) (a : Nat), a ∈ l → a ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro a hl; cases hl
  | cons x xs ih =>
      intro a hl
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hl with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih a h) (Nat.le_max_right _ _)

/-- `freshFor used` is not in `used`: it has length strictly greater than
every string in `used`. -/
theorem freshFor_not_in (used : List String) : freshFor used ∉ used := by
  intro h_in
  have h_len_in : (freshFor used).length ∈ used.map String.length :=
    List.mem_map.mpr ⟨freshFor used, h_in, rfl⟩
  have h_le : (freshFor used).length ≤ (used.map String.length).foldr max 0 :=
    le_foldr_max _ _ h_len_in
  have h_eq : (freshFor used).length = (used.map String.length).foldr max 0 + 1 := by
    show (String.ofList
        (List.replicate ((used.map String.length).foldr max 0 + 1) 'a')).length = _
    rw [String.length_ofList]
    exact List.length_replicate
  omega

/-! ## Renaming (var-for-var, structurally recursive) -/

def Term.rename : Term → String → String → Term
  | .var x,        y, z => if x = y then .var z else .var x
  | .lam x τ body, y, z =>
      if x = y then .lam x τ body
      else .lam x τ (body.rename y z)
  | .app e₁ e₂,    y, z => .app (e₁.rename y z) (e₂.rename y z)

theorem Term.rename_size (e : Term) (y z : String) :
    (e.rename y z).size = e.size := by
  induction e with
  | var x =>
      simp only [Term.rename]
      split <;> rfl
  | lam x τ body ih =>
      simp only [Term.rename]
      split <;> simp [Term.size, ih]
  | app e₁ e₂ ih₁ ih₂ =>
      simp only [Term.rename, Term.size, ih₁, ih₂]

/-! ## Capture-avoiding substitution

`e.subst x v` replaces every free occurrence of `x` in `e` with `v`. When
crossing a binder `λy:τ. body` whose `y` would capture a free variable of
`v`, we α-rename `y` to a fresh `z` before recursing.
-/

def Term.subst (e : Term) (x : String) (v : Term) : Term :=
  match e with
  | .var y => if x = y then v else .var y
  | .lam y τ body =>
      if x = y then .lam y τ body
      else if y ∈ v.freeVars then
        let z := freshFor (v.freeVars ++ body.allVars ++ [x])
        .lam z τ ((body.rename y z).subst x v)
      else .lam y τ (body.subst x v)
  | .app e₁ e₂ => .app (e₁.subst x v) (e₂.subst x v)
  termination_by e.size
  decreasing_by
    all_goals simp_wf
    all_goals simp only [Term.size, Term.rename_size]
    all_goals omega

end LambdaLab.Stlc.Named

/-! ## Example terms -/

namespace LambdaLab.Stlc.Named.Examples

open LambdaLab.Stlc.Named

/-- `λx:ι. x` -/
def idBase : Term := .lam "x" .base (.var "x")

/-- `λf:ι⇒ι. f` -/
def idArr : Term := .lam "f" (.base ⇒ .base) (.var "f")

/-- `(λf:ι⇒ι. f) (λx:ι. x)` -/
def app1 : Term := .app idArr idBase

end LambdaLab.Stlc.Named.Examples
