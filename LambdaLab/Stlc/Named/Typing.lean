import LambdaLab.Stlc.Named.Basic
import Std.Data.HashMap

/-!
# Typing (named variables, hashmap context)

The context is a `Std.HashMap String Ty`. Shadowing is `insert`
(overrides). Lookup is `get?`.
-/

namespace LambdaLab.Stlc.Named

abbrev Ctx := Std.HashMap String Ty

def Ctx.empty : Ctx := ∅

def Ctx.cons (x : String) (τ : Ty) (Γ : Ctx) : Ctx :=
  Γ.insert x τ

@[simp] theorem Ctx.get?_empty (x : String) :
    Ctx.empty.get? x = (none : Option Ty) := by
  simp [Ctx.empty]

@[simp] theorem Ctx.get?_cons (Γ : Ctx) (x : String) (τ : Ty) (y : String) :
    (Γ.cons x τ).get? y = if x = y then some τ else Γ.get? y := by
  rw [Ctx.cons, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hbeq : (x == y) = false := by simp [hxy]
    rw [hbeq]
    simp only [Bool.false_eq_true, ↓reduceIte, hxy]
    rw [← Std.HashMap.get?_eq_getElem?]

inductive HasType : Ctx → Term → Ty → Prop where
  | var : Γ.get? x = some τ → HasType Γ (.var x) τ
  | lam : HasType (Γ.cons x τ₁) body τ₂ →
          HasType Γ (.lam x τ₁ body) (τ₁ ⇒ τ₂)
  | app : HasType Γ e₁ (τ₁ ⇒ τ₂) → HasType Γ e₂ τ₁ →
          HasType Γ (.app e₁ e₂) τ₂

notation:40 Γ " ⊢ " e " : " τ => HasType Γ e τ

/-- A typing context is *ground* if every type it assigns is ground. -/
def Ctx.Ground (Γ : Ctx) : Prop := ∀ x τ, Γ.get? x = some τ → τ.Ground

theorem Ctx.Ground.empty : Ctx.empty.Ground := by
  intro x τ h
  simp [Ctx.empty] at h

theorem Ctx.Ground.cons {Γ : Ctx} {x : String} {τ : Ty}
    (hΓ : Γ.Ground) (hτ : τ.Ground) : (Γ.cons x τ).Ground := by
  intro y σ h
  rw [Ctx.get?_cons] at h
  by_cases hxy : x = y
  · simp [hxy] at h; exact h ▸ hτ
  · simp [hxy] at h; exact hΓ y σ h

/-- Under a ground context and ground annotations, the inferred type
is ground. Used to discharge the existential `τ₁` in app-cases when
bridging to the de Bruijn variant. -/
theorem HasType.ground_result : ∀ {e : Term} {Γ : Ctx} {τ : Ty},
    Γ.Ground → e.AnnotsGround → HasType Γ e τ → τ.Ground := by
  intro e
  induction e with
  | var x =>
      intro Γ τ hΓ _ ht
      cases ht with
      | var heq => exact hΓ x τ heq
  | lam x τ₁ body ih =>
      intro Γ τ hΓ hag ht
      cases ht with
      | lam hb =>
          obtain ⟨h₁, hbg⟩ := hag
          have h₂ := ih (Ctx.Ground.cons hΓ h₁) hbg hb
          exact Ty.Ground.arrow.mpr ⟨h₁, h₂⟩
  | app e₁ e₂ ih₁ _ =>
      intro Γ τ hΓ hag ht
      cases ht with
      | app hf _ =>
          obtain ⟨h₁ag, _⟩ := hag
          have h₁₂ := ih₁ hΓ h₁ag hf
          exact (Ty.Ground.arrow.mp h₁₂).2

end LambdaLab.Stlc.Named
