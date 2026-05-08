import LambdaLab.Stlc.Named.Translation
import LambdaLab.Stlc.Named.Properties

/-!
# Subject reduction (named-variable variant), via the de Bruijn translation

We inherit subject reduction from the de Bruijn variant by chaining the
translation lemmas in `LambdaLab.Stlc.Named.Translation`:

1. **Forward typing translation** (`HasType.toDB`): `Γ ⊢ e : τ` ⟶
   `db_ctx ⊢ e.toDB binders : τ.toDB`.
2. **Step simulation** (`Step.toDB_step`): `e ⟶ e'` ⟶
   `e.toDB binders ⟶* e'.toDB binders`.
3. **Multi-step DB preservation** (`Stlc.DeBruijn.MStep.preservation`).
4. **Backward typing translation** (`HasType.fromDB`):
   `db_ctx ⊢ e'.toDB binders : τ.toDB` ⟶ `Γ ⊢ e' : Ty.fromDB τ.toDB`,
   which equals `τ` after `Ty.fromDB_toDB`.
-/

namespace LambdaLab.Stlc.Named

/-- Subject reduction: typing is preserved under a single β-step.

Ground/AnnotsGround preconditions are bridge-only — the de Bruijn
correspondence is meaningful only for fully-elaborated terms (no
`inf`/`mvar`). The caller must also supply that the reduct's
annotations are ground (`hag'`); β-reduction can substitute a term
into many positions, so this is shown separately. -/
theorem HasType.preservation : ∀ {Γ : Ctx} {e e' : Term} {τ : Ty},
    Γ.Ground → e.AnnotsGround → e'.AnnotsGround →
    HasType Γ e τ → e ⟶ e' → HasType Γ e' τ := by
  intro Γ e e' τ hΓ hag hag' ht hs
  let binders := e.freeVars
  have hbound : ∀ x ∈ binders, ∃ σ, Γ x = some σ ∧ σ.Ground := by
    intro x hx
    obtain ⟨σ, heq⟩ := HasType.freeVars_in_ctx e ht x hx
    exact ⟨σ, heq, hΓ x σ heq⟩
  let db_ctx := Ctx.toDB Γ binders
  have hcompat : CtxCompat Γ binders db_ctx := CtxCompat.fromCtx Γ binders hbound
  have hfv : ∀ x ∈ e.freeVars, x ∈ binders := fun x hx => hx
  have hdb : Stlc.DeBruijn.HasType db_ctx (e.toDB binders) τ.toDB :=
    HasType.toDB e hΓ hag ht binders db_ctx hfv hcompat
  have hsim : Stlc.DeBruijn.MStep (e.toDB binders) (e'.toDB binders) :=
    Step.toDB_step binders hfv hs
  have hdb' : Stlc.DeBruijn.HasType db_ctx (e'.toDB binders) τ.toDB :=
    Stlc.DeBruijn.MStep.preservation hdb hsim
  have hfv' : ∀ x ∈ e'.freeVars, x ∈ binders := fun x hx =>
    Step.preserves_freeVars hs x hx
  have h_named : HasType Γ e' (Ty.fromDB τ.toDB) :=
    HasType.fromDB e' binders db_ctx τ.toDB hag' hfv' hcompat hdb'
  have hτg : τ.Ground := HasType.ground_result hΓ hag ht
  rw [Ty.fromDB_toDB hτg] at h_named
  exact h_named

end LambdaLab.Stlc.Named
