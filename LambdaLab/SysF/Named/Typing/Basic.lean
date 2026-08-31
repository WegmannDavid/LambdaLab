import LambdaLab.SysF.Named.Basic
import LambdaLab.TypeSystem.Named.Context

/-!
# The named System F typing judgement

Contexts are the tower's — `Context N (Ty TN)`, keyed by term names, type names invisible to
the interface — and the two rules the de Bruijn side handled by shifting are handled here by
the named discipline's usual currency, freshness:

* `tlam` carries the side condition `CtxTyFresh a Γ`: the generalized type variable must not
  occur free in any type the context assigns. The de Bruijn `Γ.map (Ty.shift 0)` and this
  condition are the same fact in two representations — there the context's variables move out
  of the binder's way, here the binder must already be out of theirs.
* `tapp` instantiates by the capture-avoiding `Ty.subst`.

Free type variables are atom-like here as on the de Bruijn side: no rule checks that a `tvar`
is bound. `CtxTyFresh` is stated through `get?`, the only handle a hashmap context offers.
-/

namespace LambdaLab.SysF.Named

open LambdaLab.Nominal (Atom)
open LambdaLab.TypeSystem.Named (Context)

variable {N TN : Type} [Atom N] [Atom TN]

/-- The generalized variable is fresh for the context: no assigned type mentions it. -/
def CtxTyFresh (a : TN) (Γ : Context N (Ty TN)) : Prop :=
  ∀ (x : N) (τ : Ty TN), Γ.get? x = some τ → a ∉ τ.freeVars

/-- The judgement. -/
inductive HasType : Context N (Ty TN) → Term N TN → Ty TN → Prop where
  | var : Γ.get? x = some τ → HasType Γ (.var x) τ
  | lam : HasType (Γ.cons x τ₁) e τ₂ → HasType Γ (.lam x τ₁ e) (τ₁ ⇒ τ₂)
  | app : HasType Γ e₁ (τ₁ ⇒ τ₂) → HasType Γ e₂ τ₁ → HasType Γ (.app e₁ e₂) τ₂
  /-- Generalization, guarded by freshness: the named form of the de Bruijn context shift. -/
  | tlam : CtxTyFresh a Γ → HasType Γ e τ → HasType Γ (.tlam a e) (.all a τ)
  /-- `∀`-elimination, by capture-avoiding instantiation. -/
  | tapp : HasType Γ e (.all a τ) → HasType Γ (.tapp e σ) (τ.subst a σ)

end LambdaLab.SysF.Named
