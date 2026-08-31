import LambdaLab.SysF.Named.Basic
import LambdaLab.TypeSystem.Named.Basic

/-!
# Full β-reduction for named System F

The de Bruijn rules with the substitutions swapped for their capture-avoiding twins: `beta` is
`Term.subst`, `tbeta` is `Term.tsubst`, congruence everywhere including under both binders.
-/

namespace LambdaLab.SysF.Named

open LambdaLab.Nominal (Atom)

variable {N TN : Type} [Atom N] [Atom TN]

inductive Step : Term N TN → Term N TN → Prop where
  | beta  : Step (.app (.lam x τ e) v) (e.subst x v)
  | tbeta : Step (.tapp (.tlam a e) σ) (e.tsubst a σ)
  | lam   : Step e e' → Step (.lam x τ e) (.lam x τ e')
  | appL  : Step e₁ e₁' → Step (.app e₁ e₂) (.app e₁' e₂)
  | appR  : Step e₂ e₂' → Step (.app e₁ e₂) (.app e₁ e₂')
  | tlam  : Step e e' → Step (.tlam a e) (.tlam a e')
  | tapp  : Step e e' → Step (.tapp e τ) (.tapp e' τ)

instance instStep : LambdaLab.TypeSystem.Named.Step (Term N TN) where
  Step := Step

end LambdaLab.SysF.Named
