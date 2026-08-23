import LambdaLab.Stlc.Named.Basic
import LambdaLab.TypeSystem.Named.Basic

/-!
# Full single-step beta reduction (named variables)

Same shape as the de Bruijn variant, but the β-rule names the bound
variable explicitly: `(λx:τ. body) v ⟶ body[x := v]` using the naive
substitution from `Basic.lean`.
-/

namespace LambdaLab.Stlc.Named

inductive Step {N : Type} [LambdaLab.TypeSystem.Named.NameAlphabet N] : Term N → Term N → Prop where
  | beta : Step (.app (.lam x τ body) v) (body.subst x v)
  | lam  : Step e e' → Step (.lam x τ e) (.lam x τ e')
  | appL : Step e₁ e₁' → Step (.app e₁ e₂) (.app e₁' e₂)
  | appR : Step e₂ e₂' → Step (.app e₁ e₂) (.app e₁ e₂')

instance instStep {N : Type} [LambdaLab.TypeSystem.Named.NameAlphabet N] :
    LambdaLab.TypeSystem.Named.Step (Term N) where
  Step := Step

end LambdaLab.Stlc.Named
