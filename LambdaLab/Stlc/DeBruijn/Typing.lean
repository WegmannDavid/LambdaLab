import LambdaLab.Stlc.DeBruijn.Basic

/-!
# Typing
-/

namespace LambdaLab.Stlc.DeBruijn

abbrev Ctx := List Ty

inductive Lookup : Ctx → Nat → Ty → Prop where
  | here  : Lookup (τ :: Γ) 0 τ
  | there : Lookup Γ n τ → Lookup (τ' :: Γ) (n + 1) τ

inductive HasType : Ctx → Term → Ty → Prop where
  | var : Lookup Γ n τ → HasType Γ (.var n) τ
  | lam : HasType (τ₁ :: Γ) e τ₂ → HasType Γ (.lam τ₁ e) (τ₁ ⇒ τ₂)
  | app : HasType Γ e₁ (τ₁ ⇒ τ₂) → HasType Γ e₂ τ₁ → HasType Γ (.app e₁ e₂) τ₂

notation:40 Γ " ⊢ " e " : " τ => HasType Γ e τ

end LambdaLab.Stlc.DeBruijn

namespace LambdaLab.Stlc.DeBruijn.Examples

open LambdaLab.Stlc.DeBruijn

example : [] ⊢ idBase : (.base ⇒ .base) :=
  .lam (.var .here)

example : [] ⊢ idArr : ((.base ⇒ .base) ⇒ (.base ⇒ .base)) :=
  .lam (.var .here)

example : [] ⊢ app1 : (.base ⇒ .base) :=
  .app (.lam (.var .here)) (.lam (.var .here))

end LambdaLab.Stlc.DeBruijn.Examples
