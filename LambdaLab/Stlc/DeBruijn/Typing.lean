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

/-- De Bruijn keeps its own turnstile: its context is a `List Ty`, which cannot instantiate
`TypeSystem.Named.HasType` (stated over a `Context N Ty`), so there is nothing to share the class
notation with. Argument levels are pinned so that `Γ ⊢ e : τ → P` splits at the arrow instead of
parsing `τ → P` as the type — the class notation pins them for the same reason. -/
notation:40 Γ:41 " ⊢ " e:41 " : " τ:41 => HasType Γ e τ

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
