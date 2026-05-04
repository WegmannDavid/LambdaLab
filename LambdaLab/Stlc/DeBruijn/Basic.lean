/-!
# Simply Typed Lambda Calculus (STLC)

A locally-nameless-free presentation using de Bruijn indices.
-/

namespace LambdaLab.Stlc.DeBruijn

/-! ## Types -/

inductive Ty where
  | base : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

infixr:25 " ⇒ " => Ty.arrow

/-! ## Terms

Variables are de Bruijn indices: `var 0` is the nearest enclosing binder.
Lambdas carry the type annotation of their argument. -/

inductive Term where
  | var : Nat → Term
  | lam : Ty → Term → Term
  | app : Term → Term → Term
  deriving Repr

/-! ## Shifting and substitution

`shift c e` increments every free variable in `e` whose index is `≥ c`.
`subst n v e` replaces variable `n` in `e` with `v`, decrementing larger
indices to account for the binder being eliminated. -/

def Term.shift (c : Nat) : Term → Term
  | .var n     => if n < c then .var n else .var (n + 1)
  | .lam τ e   => .lam τ (e.shift (c + 1))
  | .app e₁ e₂ => .app (e₁.shift c) (e₂.shift c)

def Term.subst : Term → Nat → Term → Term
  | .var m,     n, v =>
      if m = n then v
      else if m > n then .var (m - 1)
      else .var m
  | .lam τ e,   n, v => .lam τ (e.subst (n + 1) (v.shift 0))
  | .app e₁ e₂, n, v => .app (e₁.subst n v) (e₂.subst n v)

end LambdaLab.Stlc.DeBruijn

/-! ## Example terms -/

namespace LambdaLab.Stlc.DeBruijn.Examples

open LambdaLab.Stlc.DeBruijn

/-- `λx:ι. x` -/
def idBase : Term := .lam .base (.var 0)

/-- `λf:ι⇒ι. f` -/
def idArr : Term := .lam (.base ⇒ .base) (.var 0)

/-- `(λf:ι⇒ι. f) (λx:ι. x)` -/
def app1 : Term := .app idArr idBase

end LambdaLab.Stlc.DeBruijn.Examples
