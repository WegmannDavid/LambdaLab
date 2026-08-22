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

/-! ## Named SN

`LambdaLab.SN` at this `Step`, not a copy of it: `Relation/Normalization.lean` owns the inductive
and `TypeSystem.StronglyNormalizing` asks for it in that form, so an instance for this language is
`HasType.sn` and nothing else. `SN.intro`, `SN.unfold` and `induction h with | intro` all read as
before, through the abbreviation. -/

abbrev SN : (Term String) → Prop := LambdaLab.SN Step

/-! ## Why `SN e` and not well-foundedness of `Step`

`HasType.sn` claims termination for the term its derivation is about. The stronger reading — that
`Step` is well-founded, i.e. *every* named term terminates — is false, and stays refuted here
because `TypeSystem.StronglyNormalizing`'s field shape depends on it: `Term String` contains the
untypable divergent terms, `Ω` among them. -/

/-- `λx:⋆. x x` — self-application: untypable, and the engine of `Ω`. -/
def selfApp : Term String := .lam "x" .base (.app (.var "x") (.var "x"))

/-- `Ω = (λx:⋆. x x) (λx:⋆. x x)`, which β-reduces to itself. -/
def omega : Term String := .app selfApp selfApp

theorem omega_step : Step omega omega := by
  have h : ((Term.app (Term.var "x") (Term.var "x")).subst "x" selfApp) = omega := by
    simp [Term.subst, omega]
  show Step (.app (.lam "x" .base (.app (.var "x") (.var "x"))) selfApp) omega
  exact h ▸ Step.beta

/-- **`Ω` is not strongly normalizing**, so no language can be asked for well-foundedness of its
reduction relation — only for `SN` of the terms it can type. -/
theorem omega_not_sn : ¬ SN omega := by
  have key : ∀ e : Term String, SN e → e = omega → False := by
    intro e h
    induction h with
    | intro _ ih => rintro rfl; exact ih omega omega_step rfl
  exact fun h => key omega h rfl

/-! ## DB strong normalization is preserved by multi-step -/

theorem Stlc.DeBruijn.SN.mstep : ∀ {d d' : Stlc.DeBruijn.Term},
    Stlc.DeBruijn.SN d → Stlc.DeBruijn.MStep d d' → Stlc.DeBruijn.SN d' := by
  intro d d' hsn hms
  induction hms with
  | refl => exact hsn
  | tail _ s ih => exact ih.unfold s

/-! ## Transfer: DB strong normalization ⟹ Named strong normalization

We induct on `DB.SN d` with a motive closed under `MStep`: the IH gives
us `Named.SN e` whenever `e.toDB binders` `MStep`s to a strict reduct
of `d`. This lets us advance through the (potentially multi-step) DB
trace produced by a single named step. -/

private theorem SN.fromDB_aux : ∀ {d : Stlc.DeBruijn.Term}, Stlc.DeBruijn.SN d →
    ∀ (e : (Term String)) (binders : List String),
    (∀ x ∈ e.freeVars, x ∈ binders) →
    Stlc.DeBruijn.MStep d (e.toDB binders) →
    SN e := by
  intro d hsn
  induction hsn with
  | intro hStep ihStep =>
      intro e binders hfv hms
      apply LambdaLab.SN.intro
      intro e' hs
      have hfv' : ∀ x ∈ e'.freeVars, x ∈ binders :=
        fun x hx => hfv x (Step.preserves_freeVars hs x hx)
      have hsim := Step.toDB_step binders hfv hs
      rcases RTC.cases_head hms with heq | ⟨d_mid_d, h_step_d, rest_d⟩
      · -- d = e.toDB binders. Use Step.toDB_pos to get a single DB head step.
        subst heq
        obtain ⟨d_mid, h_step_db, h_rest⟩ := Step.toDB_pos binders hfv hs
        exact ihStep d_mid h_step_db e' binders hfv' h_rest
      · exact ihStep d_mid_d h_step_d e' binders hfv' (rest_d.trans hsim)

theorem SN.fromDB : ∀ (e : (Term String)) (binders : List String),
    (∀ x ∈ e.freeVars, x ∈ binders) →
    Stlc.DeBruijn.SN (e.toDB binders) → SN e :=
  fun e binders hfv hsn =>
    SN.fromDB_aux hsn e binders hfv .refl

/-! ## Strong normalization for the named system -/

/-- **Every well-typed named term is strongly normalizing.** Unconditionally — the groundness
preconditions this used to carry were paying for the de Bruijn detour, not for normalization, and
went away when `Ty.toDB` became a bijection. -/
theorem HasType.sn : ∀ {Γ : Ctx String} {e : (Term String)} {τ : Ty},
    HasType Γ e τ → SN e := by
  intro Γ e τ ht
  let binders := e.freeVars
  have hbound : ∀ x ∈ binders, ∃ σ, Γ.get? x = some σ := by
    intro x hx
    obtain ⟨σ, heq⟩ := HasType.freeVars_in_ctx e ht x hx
    exact ⟨σ, heq⟩
  let db_ctx := Ctx.toDB Γ binders
  have hcompat : CtxCompat Γ binders db_ctx := CtxCompat.fromCtx Γ binders hbound
  have hfv : ∀ x ∈ e.freeVars, x ∈ binders := fun x hx => hx
  have hdb : Stlc.DeBruijn.HasType db_ctx (e.toDB binders) τ.toDB :=
    HasType.toDB e ht binders db_ctx hfv hcompat
  have hsn_db : Stlc.DeBruijn.SN (e.toDB binders) :=
    Stlc.DeBruijn.HasType.sn hdb
  exact SN.fromDB e binders hfv hsn_db

end LambdaLab.Stlc.Named
