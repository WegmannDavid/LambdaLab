import LambdaLab.Stlc.Named.Typing
import LambdaLab.Stlc.Named.Unification

/-! # Monomorphic Hindley–Milner inference for the named STLC.

Walks a `Term`, collecting type equations. The accumulated equations
are solved by `unify` from the unification module; the solving
substitution is applied to the inferred type. Annotations that need
to be "inferred me" come in already represented as `Ty.mvar` (the
parser produces fresh mvar indices for surface `_` tokens).

No `let`-polymorphism yet: types stay first-order, free `Ty.mvar`s in
the final type are left in place (they represent unconstrained type
parameters, e.g. the identity function's type). -/

namespace LambdaLab.Stlc.Named

inductive InferError where
  | unbound : String → InferError
  | unifyFail : Equations Ty → InferError
  deriving Repr

structure InferState where
  counter : Nat
  eqs     : Equations Ty

abbrev InferM := StateT InferState (Except InferError)

/-- Allocate a fresh `Ty.mvar`. -/
def fresh : InferM Ty := do
  let s ← get
  set { s with counter := s.counter + 1 }
  return .mvar s.counter

/-- Push a `τ₁ = τ₂` constraint onto the pile. -/
def constrain (τ₁ τ₂ : Ty) : InferM Unit :=
  modify fun s => { s with eqs := (τ₁, τ₂) :: s.eqs }

/-- Monomorphic constraint-based inference. -/
def Term.inferHM (Γ : Ctx) : Term → InferM Ty
  | .var x =>
      match Γ.get? x with
      | none   => throw (.unbound x)
      | some τ => pure τ
  | .lam x τ₁ body => do
      let τ₂ ← inferHM (Γ.cons x τ₁) body
      pure (τ₁ ⇒ τ₂)
  | .app e₁ e₂ => do
      let τf ← inferHM Γ e₁
      let τa ← inferHM Γ e₂
      let α  ← fresh
      constrain τf (τa ⇒ α)
      pure α

/-- Run inference under `Γ`, solve the collected equations, and apply
the solution to the inferred type. The fresh counter is initialised to
`HasVars.fresh e` so that newly-allocated mvars never collide with
ones already present in the input. Free mvars in the result represent
unconstrained type parameters. -/
def Term.infer? (Γ : Ctx) (e : Term) : Except InferError Ty := do
  let (τ, s) ← (e.inferHM Γ).run { counter := HasVars.fresh e, eqs := [] }
  match unify s.eqs with
  | none   => throw (.unifyFail s.eqs)
  | some σ => pure (HasSubst.pSubst τ σ)

/-- Closed-term entry point. -/
def Term.infer?Closed (e : Term) : Except InferError Ty :=
  e.infer? Ctx.empty

end LambdaLab.Stlc.Named
