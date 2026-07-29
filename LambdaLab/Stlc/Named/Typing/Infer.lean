import LambdaLab.Stlc.Named.Typing.Basic

/-!
# Type checking without inference

`HasType` is decidable, by a plain structural walk. Binder annotations are mandatory in `Term`,
so nothing has to be guessed: a lambda's domain is written down, and the body determines the
codomain. No unification, no metavariable solving, no substitution — the whole of `W.lean` is
unnecessary for deciding this judgement.

That is not an accident of the implementation, it is what the surface syntax buys. The elaborator
in `W.lean` exists for a *different* surface, one where a binder may be left unannotated; STLC's
`Language` grammar (`Stlc/Named/Lang.lean`) deliberately does not admit that yet.

`infer` also gives uniqueness of types for free (`HasType.det`), since it is a function.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Language (NameAlphabet)

variable {N : Type} [NameAlphabet N]

/-- **Type synthesis.** Structural on the term; the context varies, so it is an argument rather
than a parameter. -/
def infer : (Γ : Ctx N) → Term N → Option Ty
  | Γ, .var x => Γ.get? x
  | Γ, .lam x α body => (infer (Γ.cons x α) body).map (α ⇒ ·)
  | Γ, .app e₁ e₂ =>
      match infer Γ e₁, infer Γ e₂ with
      | some (α ⇒ β), some α' => if α = α' then some β else none
      | _, _ => none

theorem infer_sound : ∀ {Γ : Ctx N} {e : Term N} {τ : Ty}, infer Γ e = some τ → HasType Γ e τ := by
  intro Γ e
  induction e generalizing Γ with
  | var x => intro τ h; exact .var h
  | lam x α body ih =>
      intro τ h
      rw [infer, Option.map_eq_some_iff] at h
      obtain ⟨β, hβ, rfl⟩ := h
      exact .lam (ih hβ)
  | app e₁ e₂ ih₁ ih₂ =>
      intro τ h
      rw [infer] at h
      split at h
      · rename_i α β α' h₁ h₂
        split at h
        · rename_i hα; cases h; exact .app (ih₁ h₁) (hα ▸ ih₂ h₂)
        · cases h
      · cases h

theorem infer_complete : ∀ {Γ : Ctx N} {e : Term N} {τ : Ty}, HasType Γ e τ → infer Γ e = some τ := by
  intro Γ e τ h
  induction h with
  | var hget => exact hget
  | lam _ ih => rw [infer, ih]; rfl
  | app _ _ ih₁ ih₂ => rw [infer, ih₁, ih₂]; simp

/-- Types are unique: `infer` is a function, so two derivations for one term agree. -/
theorem HasType.det {Γ : Ctx N} {e : Term N} {τ₁ τ₂ : Ty}
    (h₁ : HasType Γ e τ₁) (h₂ : HasType Γ e τ₂) : τ₁ = τ₂ := by
  have := (infer_complete h₁).symm.trans (infer_complete h₂)
  exact (Option.some.injEq _ _ ▸ this)

instance (Γ : Ctx N) (e : Term N) (τ : Ty) : Decidable (HasType Γ e τ) :=
  decidable_of_iff (infer Γ e = some τ) ⟨infer_sound, infer_complete⟩

/-! ## Deciding groundness

`Term.AnnotsGround` is a `Prop` recursion; this is the same recursion in `Bool`, so a language can
*demand* that no metavariable survives elaboration.
-/

/-- Every type annotation inside `e` is ground, decidably. -/
def Term.annotsGround : Term N → Bool
  | .var _        => true
  | .lam _ τ body => τ.isGround && body.annotsGround
  | .app e₁ e₂    => e₁.annotsGround && e₂.annotsGround

@[simp] theorem Term.annotsGround_iff : ∀ {e : Term N}, e.annotsGround = true ↔ e.AnnotsGround := by
  intro e
  induction e with
  | var x => simp [Term.annotsGround, Term.AnnotsGround]
  | lam x τ body ih => simp [Term.annotsGround, Term.AnnotsGround, ih, Ty.Ground]
  | app e₁ e₂ ih₁ ih₂ => simp [Term.annotsGround, Term.AnnotsGround, ih₁, ih₂]

instance (e : Term N) : Decidable e.AnnotsGround :=
  decidable_of_iff (e.annotsGround = true) Term.annotsGround_iff

end LambdaLab.Stlc.Named
