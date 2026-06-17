import LambdaLab.Stlc.Named.Translation
import LambdaLab.Stlc.Named.Typing.Properties
import LambdaLab.Stlc.DeBruijn.Reducibility

/-!
# Strong normalization (named-variable variant), via the de Bruijn translation

We define `Named.SN` analogously to the de Bruijn `SN`, then transfer
the result `Stlc.DeBruijn.HasType.sn` through the translation. The key
fact is `Step.toDB_pos` (in `Translation.lean`): every named single-step
contains at least one DB single-step. So an infinite named reduction
sequence would translate to an infinite DB reduction, contradicting
`DB.SN`.

The chain:

1. `Γ ⊢ e : τ` ⟶ `db_ctx ⊢ e.toDB binders : τ.toDB`
   (`HasType.toDB` from `Translation.lean`).
2. `db_ctx ⊢ d : τ.toDB` ⟶ `Stlc.DeBruijn.SN d`
   (`Stlc.DeBruijn.HasType.sn` from `Reducibility.lean`).
3. `Stlc.DeBruijn.SN (e.toDB binders)` ⟶ `Named.SN e`
   (`Named.SN.fromDB`, the new transfer lemma).
-/

namespace LambdaLab.Stlc.Named

/-! ## Named SN (mirroring the DB definition) -/

inductive SN : Term → Prop where
  | intro : (∀ e', Step e e' → SN e') → SN e

theorem SN.unfold : ∀ {e e'}, SN e → Step e e' → SN e'
  | _, _, .intro h, hs => h _ hs

/-! ## DB strong normalization is preserved by multi-step -/

theorem Stlc.DeBruijn.SN.mstep : ∀ {d d' : Stlc.DeBruijn.Term},
    Stlc.DeBruijn.SN d → Stlc.DeBruijn.MStep d d' → Stlc.DeBruijn.SN d' := by
  intro d d' hsn hms
  induction hms with
  | refl => exact hsn
  | head s _ ih => exact ih (hsn.unfold s)

/-! ## Transfer: DB strong normalization ⟹ Named strong normalization

We induct on `DB.SN d` with a motive closed under `MStep`: the IH gives
us `Named.SN e` whenever `e.toDB binders` `MStep`s to a strict reduct
of `d`. This lets us advance through the (potentially multi-step) DB
trace produced by a single named step. -/

private theorem SN.fromDB_aux : ∀ {d : Stlc.DeBruijn.Term}, Stlc.DeBruijn.SN d →
    ∀ (e : Term) (binders : List String),
    (∀ x ∈ e.freeVars, x ∈ binders) →
    Stlc.DeBruijn.MStep d (e.toDB binders) →
    SN e := by
  intro d hsn
  induction hsn with
  | intro hStep ihStep =>
      intro e binders hfv hms
      apply SN.intro
      intro e' hs
      have hfv' : ∀ x ∈ e'.freeVars, x ∈ binders :=
        fun x hx => hfv x (Step.preserves_freeVars hs x hx)
      have hsim := Step.toDB_step binders hfv hs
      cases hms with
      | refl =>
          -- d = e.toDB binders. Use Step.toDB_pos to get a single DB head step.
          obtain ⟨d_mid, h_step_db, h_rest⟩ := Step.toDB_pos binders hfv hs
          exact ihStep d_mid h_step_db e' binders hfv' h_rest
      | head h_step_d rest_d =>
          rename_i d_mid_d
          exact ihStep d_mid_d h_step_d e' binders hfv' (rest_d.trans hsim)

theorem SN.fromDB : ∀ (e : Term) (binders : List String),
    (∀ x ∈ e.freeVars, x ∈ binders) →
    Stlc.DeBruijn.SN (e.toDB binders) → SN e :=
  fun e binders hfv hsn =>
    SN.fromDB_aux hsn e binders hfv Stlc.DeBruijn.MStep.refl

/-! ## Strong normalization for the named system -/

/-- Every well-typed named term is strongly normalizing.

Bridge preconditions: Γ and e's annotations must be ground. -/
theorem HasType.sn : ∀ {Γ : Ctx} {e : Term} {τ : Ty},
    Γ.Ground → e.AnnotsGround → HasType Γ e τ → SN e := by
  intro Γ e τ hΓ hag ht
  let binders := e.freeVars
  have hbound : ∀ x ∈ binders, ∃ σ, Γ.get? x = some σ ∧ σ.Ground := by
    intro x hx
    obtain ⟨σ, heq⟩ := HasType.freeVars_in_ctx e ht x hx
    exact ⟨σ, heq, hΓ x σ heq⟩
  let db_ctx := Ctx.toDB Γ binders
  have hcompat : CtxCompat Γ binders db_ctx := CtxCompat.fromCtx Γ binders hbound
  have hfv : ∀ x ∈ e.freeVars, x ∈ binders := fun x hx => hx
  have hdb : Stlc.DeBruijn.HasType db_ctx (e.toDB binders) τ.toDB :=
    HasType.toDB e hΓ hag ht binders db_ctx hfv hcompat
  have hsn_db : Stlc.DeBruijn.SN (e.toDB binders) :=
    Stlc.DeBruijn.HasType.sn hdb
  exact SN.fromDB e binders hfv hsn_db

end LambdaLab.Stlc.Named
