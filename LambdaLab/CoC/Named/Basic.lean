import LambdaLab.CoC.Basic
import LambdaLab.Nominal.Atom

/-!
# The Calculus of Constructions, named-variable presentation

The named mirror of `CoC/DeBruijn/Basic.lean`, on `Stlc/Named`'s idioms — capture-avoiding
substitution by `Atom.freshFor`, termination by size through the renaming lemma — and the
collapse pays a second time: where named System F needed **two** alphabets and five operations
(`freeVars`/`tyFreeVars`, `rename`/`tyRename`, `subst` avoiding capture twice over, `tsubst`),
named CoC needs one alphabet and one of each. Two constructors bind (`Π` and `λ`), but they
bind the *same kind* of variable, so one renaming and one substitution serve both.

The one clause shape without an STLC ancestor: a binder's **annotation is outside its scope**.
`Π x:A. B` binds `x` in `B` only, so `subst` and `rename` always descend into `A` — even when
the binder shadows and the body is left alone.
-/

namespace LambdaLab.CoC.Named

open LambdaLab.CoC (Srt)
open LambdaLab.Nominal (Atom freshFor freshFor_not_in)

variable {N : Type} [Atom N]

/-- One syntactic category: sorts, variables, `Π x:A. B`, `λ x:A. b`, application. -/
inductive Term (N : Type) where
  | sort : Srt → Term N
  | var  : N → Term N
  | pi   : N → Term N → Term N → Term N
  | lam  : N → Term N → Term N → Term N
  | app  : Term N → Term N → Term N
  deriving Repr

/-- Free variables: annotations contribute unconditionally, bodies minus their binder. -/
def Term.freeVars : Term N → List N
  | .sort _    => []
  | .var x     => [x]
  | .pi y A B  => A.freeVars ++ B.freeVars.filter (· ≠ y)
  | .lam y A b => A.freeVars ++ b.freeVars.filter (· ≠ y)
  | .app f a   => f.freeVars ++ a.freeVars

/-- All variables, binders included — freshness must clear them too. -/
def Term.allVars : Term N → List N
  | .sort _    => []
  | .var x     => [x]
  | .pi y A B  => y :: A.allVars ++ B.allVars
  | .lam y A b => y :: A.allVars ++ b.allVars
  | .app f a   => f.allVars ++ a.allVars

def Term.size : Term N → Nat
  | .sort _    => 1
  | .var _     => 1
  | .pi _ A B  => 1 + A.size + B.size
  | .lam _ A b => 1 + A.size + b.size
  | .app f a   => 1 + f.size + a.size

/-- Renaming: the annotation always renames (it is outside the binder's scope); the body only
when the binder does not shadow. -/
def Term.rename : Term N → N → N → Term N
  | .sort s,    _, _ => .sort s
  | .var x,     y, z => if x = y then .var z else .var x
  | .pi w A B,  y, z =>
      if w = y then .pi w (A.rename y z) B
      else .pi w (A.rename y z) (B.rename y z)
  | .lam w A b, y, z =>
      if w = y then .lam w (A.rename y z) b
      else .lam w (A.rename y z) (b.rename y z)
  | .app f a,   y, z => .app (f.rename y z) (a.rename y z)

theorem Term.rename_size (e : Term N) (y z : N) : (e.rename y z).size = e.size := by
  induction e with
  | sort s => rfl
  | var x => simp only [Term.rename]; split <;> rfl
  | pi w A B ihA ihB => simp only [Term.rename]; split <;> simp [Term.size, ihA, ihB]
  | lam w A b ihA ihb => simp only [Term.rename]; split <;> simp [Term.size, ihA, ihb]
  | app f a ihf iha => simp only [Term.rename, Term.size, ihf, iha]

/-- Capture-avoiding substitution — one operation for the one alphabet, serving both binding
constructors. Annotations substitute unconditionally; a shadowing binder stops the body; a
binder free in the value renames fresh first. -/
def Term.subst (e : Term N) (x : N) (v : Term N) : Term N :=
  match e with
  | .sort s => .sort s
  | .var y => if x = y then v else .var y
  | .pi y A B =>
      if x = y then .pi y (A.subst x v) B
      else if y ∈ v.freeVars then
        let z := freshFor (v.freeVars ++ B.allVars ++ [x])
        .pi z (A.subst x v) ((B.rename y z).subst x v)
      else .pi y (A.subst x v) (B.subst x v)
  | .lam y A b =>
      if x = y then .lam y (A.subst x v) b
      else if y ∈ v.freeVars then
        let z := freshFor (v.freeVars ++ b.allVars ++ [x])
        .lam z (A.subst x v) ((b.rename y z).subst x v)
      else .lam y (A.subst x v) (b.subst x v)
  | .app f a => .app (f.subst x v) (a.subst x v)
  termination_by e.size
  decreasing_by
    all_goals simp_wf
    all_goals simp only [Term.size]
    all_goals first
      | omega
      | (rw [Term.rename_size]; omega)

end LambdaLab.CoC.Named

/-! ## Example terms -/

namespace LambdaLab.CoC.Named.Examples

open LambdaLab.CoC.Named

/-- `λ(A:*). λ(x:A). x`. -/
def polyId : Term String := .lam "A" (.sort .prop) (.lam "x" (.var "A") (.var "x"))

/-- `Π(A:*). Π(x:A). A`. -/
def polyIdTy : Term String := .pi "A" (.sort .prop) (.pi "x" (.var "A") (.var "A"))

end LambdaLab.CoC.Named.Examples
