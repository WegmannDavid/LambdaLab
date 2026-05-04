import LambdaLab.Stlc.Named.Basic

/-!
# Typing (named variables, function-based context)

The context is a `String → Option Ty`. Using a function makes shadowing
and exchange free (it's just a function update / `funext`), which lets
the substitution proof avoid awkward list bookkeeping.
-/

namespace LambdaLab.Stlc.Named

abbrev Ctx := String → Option Ty

def Ctx.empty : Ctx := fun _ => none

def Ctx.cons (x : String) (τ : Ty) (Γ : Ctx) : Ctx :=
  fun y => if x = y then some τ else Γ y

inductive HasType : Ctx → Term → Ty → Prop where
  | var : Γ x = some τ → HasType Γ (.var x) τ
  | lam : HasType (Γ.cons x τ₁) body τ₂ →
          HasType Γ (.lam x τ₁ body) (τ₁ ⇒ τ₂)
  | app : HasType Γ e₁ (τ₁ ⇒ τ₂) → HasType Γ e₂ τ₁ →
          HasType Γ (.app e₁ e₂) τ₂

notation:40 Γ " ⊢ " e " : " τ => HasType Γ e τ

end LambdaLab.Stlc.Named
