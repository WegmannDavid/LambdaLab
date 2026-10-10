import LambdaLab.Nominal.Atom

/-!
# Simply Typed Lambda Calculus (STLC), named-variable presentation

Variables are drawn from any `Atom N`: the development only decides equality of names and
generates fresh ones (`Term.subst`'s α-renaming branch). `String` is the usual instance, but
reduction, typing, subject reduction and elaboration are all stated at `Term N`; only the
de Bruijn-mediated results that traffic in binder *lists* — confluence, normalization, `eval` —
remain pinned at `String`. A *parser* can therefore pick a name type whose values are already
valid surface tokens, so a parsed term needs no separate surface AST, and it still reaches the
whole metatheory.

Originally variables were `String`s. Substitution is *capture-avoiding*: when entering a
binder whose bound variable would capture a free variable of the substituted
value, the binder is α-renamed to a fresh name first.

Termination of `Term.subst` is by term size, not structural recursion: in
the α-renaming branch, we recurse on `body.rename y z` whose size equals
`body.size` (proved by `Term.rename_size`).
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Nominal (Atom freshFor freshFor_not_in)

variable {N : Type} [Atom N]

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

/-- A type is *ground* when it contains no `mvar`.

Neither `HasType` nor the de Bruijn bridge requires this any more: the judgement never inspects a
type beyond equality, and `Ty.toDB` carries `mvar` across injectively (`Translation.lean`), so the
round trip no longer has to know it lost nothing. What wants groundness is the layer above —
the elaborator, which must not leave a metavariable behind, and the vernacular, whose declarations
are commitments. `Ty.ground_iff` (`Typing/Unification.lean`) is the bridge from this structural
check to the interface's `HasVars.Ground`, and it is what decides that class field. -/
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

inductive Term (N : Type) where
  | var : N → Term N
  | lam : N → Ty → Term N → Term N
  | app : Term N → Term N → Term N
  deriving Repr

/-- Every type annotation inside `e` is ground (no `.mvar`). -/
def Term.AnnotsGround : Term N → Prop
  | .var _        => True
  | .lam _ τ body => τ.Ground ∧ body.AnnotsGround
  | .app e₁ e₂    => e₁.AnnotsGround ∧ e₂.AnnotsGround

/-! ## Free variables and term size -/

def Term.freeVars : Term N → List N
  | .var x        => [x]
  | .lam y _ body => body.freeVars.filter (· ≠ y)
  | .app e₁ e₂    => e₁.freeVars ++ e₂.freeVars

/-- All variables (free and bound) appearing in a term — used to pick a
fresh name that's also fresh from binders, not just free variables. -/
def Term.allVars : Term N → List N
  | .var x        => [x]
  | .lam y _ body => y :: body.allVars
  | .app e₁ e₂    => e₁.allVars ++ e₂.allVars

def Term.size : Term N → Nat
  | .var _        => 1
  | .lam _ _ body => 1 + body.size
  | .app e₁ e₂    => 1 + e₁.size + e₂.size

/-- Every free variable is also an `allVars` entry. -/
theorem Term.freeVars_subset_allVars (e : Term N) (x : N) :
    x ∈ e.freeVars → x ∈ e.allVars := by
  induction e <;> grind [Term.freeVars, Term.allVars]

/-! ## Renaming (var-for-var, structurally recursive) -/

def Term.rename : Term N → N → N → Term N
  | .var x,        y, z => if x = y then .var z else .var x
  | .lam x τ body, y, z =>
      if x = y then .lam x τ body
      else .lam x τ (body.rename y z)
  | .app e₁ e₂,    y, z => .app (e₁.rename y z) (e₂.rename y z)

theorem Term.rename_size (e : Term N) (y z : N) :
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

def Term.subst (e : Term N) (x : N) (v : Term N) : Term N :=
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
def idBase : Term String := .lam "x" .base (.var "x")

/-- `λf:ι⇒ι. f` -/
def idArr : Term String := .lam "f" (.base ⇒ .base) (.var "f")

/-- `(λf:ι⇒ι. f) (λx:ι. x)` -/
def app1 : Term String := .app idArr idBase

end LambdaLab.Stlc.Named.Examples
