import LambdaLab.SysF.DeBruijn.Basic
import LambdaLab.TypeSystem.Named.Basic

/-!
# Full β-reduction for System F

Two β-rules now — term application against `lam`, type application against `Λ` — and congruence
everywhere, including under both binders. As in STLC, no value restriction.
-/

namespace LambdaLab.SysF.DeBruijn

inductive Step : Term → Term → Prop where
  | beta  : Step (.app (.lam τ e) v) (e.subst 0 v)
  | tbeta : Step (.tapp (.tlam e) σ) (e.tsubst 0 σ)
  | lam   : Step e e' → Step (.lam τ e) (.lam τ e')
  | appL  : Step e₁ e₁' → Step (.app e₁ e₂) (.app e₁' e₂)
  | appR  : Step e₂ e₂' → Step (.app e₁ e₂) (.app e₁ e₂')
  | tlam  : Step e e' → Step (.tlam e) (.tlam e')
  | tapp  : Step e e' → Step (.tapp e τ) (.tapp e' τ)

instance instStep : LambdaLab.TypeSystem.Named.Step Term where
  Step := Step

end LambdaLab.SysF.DeBruijn
