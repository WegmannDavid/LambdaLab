import LambdaLab.Stlc.DeBruijn.Typing.Basic

/-!
# Properties of typing

## Type uniqueness

A term has at most one type in a given context. This rests on the fact
that de Bruijn lookup is functional.
-/

namespace LambdaLab.Stlc.DeBruijn

theorem Lookup.unique : Lookup Γ n τ₁ → Lookup Γ n τ₂ → τ₁ = τ₂
  | .here,     .here     => rfl
  | .there h₁, .there h₂ => Lookup.unique h₁ h₂

theorem HasType.unique : HasType Γ e τ₁ → HasType Γ e τ₂ → τ₁ = τ₂
  | .var l₁,   .var l₂   => Lookup.unique l₁ l₂
  | .lam d₁,   .lam d₂   => by rw [HasType.unique d₁ d₂]
  | .app f₁ _, .app f₂ _ => by
      have h := HasType.unique f₁ f₂
      cases h; rfl

end LambdaLab.Stlc.DeBruijn
