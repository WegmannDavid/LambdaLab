import LambdaLab.Stlc.Named.Basic
import LambdaLab.TypeSystem.Named.Context
import LambdaLab.TypeSystem.Named.Basic

/-!
# Typing (named variables, hashmap context)

The context is `TypeSystem.Named.Context N Ty` — a `Std.HashMap N Ty`. Shadowing is `insert`
(overrides). Lookup is `get?`.

## Parametric in the atoms

`Term` is parametric in its names (`Stlc/Named/Basic.lean`), so the judgement typing it has to be
too: a *parsed* term is named by the tokens the grammar admits, and a `String`-keyed context
cannot receive one without a conversion at the boundary.

`Ctx N` is therefore literally `TypeSystem.Named.Context N Ty`, not a copy of it. That is deliberate:
the `TypeSystem` classes are all stated over a `TypeSystem.Named.Context`, so anything short of
definitional equality would put a bridge on the interface boundary, which is exactly what the name
parameter exists to remove.

Everything downstream of this file (`Properties`, `W`, `Translation`, …) stays stated at
`Ctx String`, the usual instance. Nothing in them is `String`-specific; they are pinned rather
than generalized because pinning is free and generalizing costs a sweep through every proof.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Nominal (Atom)
open LambdaLab.TypeSystem.Named (Context)

variable {N : Type} [Atom N]

/-- A typing context: variable names to types. -/
abbrev Ctx (N : Type) [Atom N] : Type := Context N Ty

abbrev Ctx.empty : Ctx N := Context.empty

abbrev Ctx.cons (x : N) (τ : Ty) (Γ : Ctx N) : Ctx N := Context.cons x τ Γ

theorem Ctx.get?_empty (x : N) :
    (Ctx.empty (N := N)).get? x = (none : Option Ty) :=
  Context.get?_empty x

theorem Ctx.get?_cons (Γ : Ctx N) (x : N) (τ : Ty) (y : N) :
    (Γ.cons x τ).get? y = if x = y then some τ else Γ.get? y :=
  Context.get?_cons Γ x τ y

/-- **The typing judgement**: `Γ ⊢ e : τ` — under `Γ`, the term `e` has type `τ`.

One rule per constructor of `Term`, and no rule mentioning `Ty.mvar`. Metavariables are not
*forbidden* here — `Γ ⊢ λ x : ?0 . x : ?0 ⇒ ?0` is derivable, and a context may perfectly well
assign one — they are simply never introduced or solved by typing, which is what makes inference
a separate concern (`Typing/W.lean`) and groundness a separate condition (`Ctx.Ground`,
`Term.AnnotsGround`, and `HasType.ground_result` relating the three). -/
inductive HasType {N : Type} [Atom N] : Ctx N → Term N → Ty → Prop where
  | var : Γ.get? x = some τ → HasType Γ (.var x) τ
  | lam : HasType (Γ.cons x τ₁) body τ₂ →
          HasType Γ (.lam x τ₁ body) (τ₁ ⇒ τ₂)
  | app : HasType Γ e₁ (τ₁ ⇒ τ₂) → HasType Γ e₂ τ₁ →
          HasType Γ (.app e₁ e₂) τ₂

/-- Typing is parametric in the atoms: nothing in the judgement inspects a name. Declared
here rather than in `Named/TypeSystem.lean` so that `Γ ⊢ e : τ` — the class notation, and now the
only one — reads at the judgement itself, exactly as `instStep` sits beside `Step`. -/
instance instHasType : TypeSystem.Named.HasType N (Term N) Ty where
  HasType := HasType

/-- A typing context is *ground* if every type it assigns is ground. -/
def Ctx.Ground (Γ : Ctx N) : Prop := ∀ x τ, Γ.get? x = some τ → τ.Ground

theorem Ctx.Ground.empty : (Ctx.empty (N := N)).Ground := by
  intro x τ h
  simp [Ctx.empty, Context.empty] at h

theorem Ctx.Ground.cons {Γ : Ctx N} {x : N} {τ : Ty}
    (hΓ : Γ.Ground) (hτ : τ.Ground) : (Γ.cons x τ).Ground := by
  intro y σ h
  rw [Ctx.get?_cons] at h
  by_cases hxy : x = y
  · simp [hxy] at h; exact h ▸ hτ
  · simp [hxy] at h; exact hΓ y σ h

/-- Under a ground context and ground annotations, the inferred type
is ground. Used to discharge the existential `τ₁` in app-cases when
bridging to the de Bruijn variant. -/
theorem HasType.ground_result : ∀ {e : Term N} {Γ : Ctx N} {τ : Ty},
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
