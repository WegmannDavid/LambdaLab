import LambdaLab.Stlc.Named.Basic

/-!
# Full single-step beta reduction (named variables)

Same shape as the de Bruijn variant, but the β-rule names the bound
variable explicitly: `(λx:τ. body) v ⟶ body[x := v]` using the naive
substitution from `Basic.lean`.
-/

namespace LambdaLab.Stlc.Named

inductive Step : Term → Term → Prop where
  | beta : Step (.app (.lam x τ body) v) (body.subst x v)
  | lam  : Step e e' → Step (.lam x τ e) (.lam x τ e')
  | appL : Step e₁ e₁' → Step (.app e₁ e₂) (.app e₁' e₂)
  | appR : Step e₂ e₂' → Step (.app e₁ e₂) (.app e₁ e₂')

infix:50 " ⟶ " => Step

end LambdaLab.Stlc.Named
