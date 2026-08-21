import LambdaLab.Stlc.DeBruijn.Basic
import LambdaLab.TypeSystem.Basic

/-!
# Full single-step beta reduction

Reduce anywhere — under lambdas and on either side of an application —
with no value restriction on redex arguments.
-/

namespace LambdaLab.Stlc.DeBruijn

inductive Step : Term → Term → Prop where
  | beta : Step (.app (.lam τ e₁) e₂) (e₁.subst 0 e₂)
  | lam  : Step e e' → Step (.lam τ e) (.lam τ e')
  | appL : Step e₁ e₁' → Step (.app e₁ e₂) (.app e₁' e₂)
  | appR : Step e₂ e₂' → Step (.app e₁ e₂) (.app e₁ e₂')

instance instStep : LambdaLab.TypeSystem.Step Term where
  Step := Step

end LambdaLab.Stlc.DeBruijn
