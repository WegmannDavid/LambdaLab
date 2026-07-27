import LambdaLab.Stlc.Named.Translation
import LambdaLab.Stlc.DeBruijn.Confluence

/-!
# Confluence for the named-variable variant via translation

The named system's reduction generates fresh binder names, so two
reduction paths from the same term yield α-equivalent but syntactically
distinct results — confluence cannot be stated as joint convergence on
named terms without an α-equivalence relation.

We sidestep that by translating named terms into de Bruijn (via
`LambdaLab.Stlc.Named.Translation`) and inheriting confluence from
`Stlc.DeBruijn.MStep.confluent`.
-/

namespace LambdaLab.Stlc.Named

/-- Two reduction paths from a named term `e` converge in the de Bruijn
world: their translations multi-step to a common de Bruijn term.

We do not claim joint convergence on named terms — that would require
α-equivalence, since freshness choices in `Term.subst` make β
nondeterministic on syntactic terms. -/
theorem MStep.confluent : ∀ {e e₁ e₂ : (Term String)} (Γ : List String),
    (∀ w ∈ e.freeVars, w ∈ Γ) →
    e ⟶* e₁ → e ⟶* e₂ →
    ∃ d, Stlc.DeBruijn.MStep (e₁.toDB Γ) d ∧
         Stlc.DeBruijn.MStep (e₂.toDB Γ) d := by
  intro e e₁ e₂ Γ hfv h₁ h₂
  have m₁ := MStep.toDB_step Γ hfv h₁
  have m₂ := MStep.toDB_step Γ hfv h₂
  exact Stlc.DeBruijn.MStep.confluent m₁ m₂

end LambdaLab.Stlc.Named
