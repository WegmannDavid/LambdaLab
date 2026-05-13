import LambdaLab.Stlc.Named.Typing
import LambdaLab.Stlc.Named.Unification
import LambdaLab.Stlc.Named.Properties
import LambdaLab.Substitution.Unification.Soundness
import LambdaLab.Language.Basic

/-! # Monomorphic Hindley–Milner inference for the named STLC.

Walks a `Term`, collecting type equations. The accumulated equations
are solved by `unify` from the unification module; the solving
substitution is applied to the inferred type. Annotations that need
to be "inferred me" come in already represented as `Ty.mvar` (the
parser produces fresh mvar indices for surface `_` tokens).

No `let`-polymorphism yet: types stay first-order, free `Ty.mvar`s in
the final type are left in place (they represent unconstrained type
parameters, e.g. the identity function's type). -/

namespace LambdaLab.Stlc.Named

inductive InferError where
  | unbound : String → InferError
  | unifyFail : Equations Ty → InferError
  deriving Repr

structure InferState where
  counter : Nat
  eqs     : Equations Ty

/-- Pure constraint-based inference: walks the term with an explicit
state (counter + accumulated equations) and returns the inferred type
plus the updated state. -/
def Term.inferHM (Γ : Ctx) : Term → InferState → Except InferError (Ty × InferState)
  | .var x,        s =>
      match Γ.get? x with
      | none   => .error (.unbound x)
      | some τ => .ok (τ, s)
  | .lam x τ₁ body, s =>
      match Term.inferHM (Γ.cons x τ₁) body s with
      | .error err     => .error err
      | .ok (τ₂, s')   => .ok (τ₁ ⇒ τ₂, s')
  | .app e₁ e₂,     s =>
      match Term.inferHM Γ e₁ s with
      | .error err      => .error err
      | .ok (τf, s₁)    =>
          match Term.inferHM Γ e₂ s₁ with
          | .error err      => .error err
          | .ok (τa, s₂)    =>
              let α := Ty.mvar s₂.counter
              let s₃ : InferState :=
                { counter := s₂.counter + 1
                  eqs     := (τf, τa ⇒ α) :: s₂.eqs }
              .ok (α, s₃)

/-! ## Supporting lemmas for verification. -/

/-- `cons` and `pSubst` commute under `get?` — substituting an extended
context agrees, key-by-key, with extending a substituted context. Used
via `HasType.cong` to bridge `pSubst (Γ.cons x τ) σ` and
`(pSubst Γ σ).cons x (pSubst τ σ)`. -/
theorem Ctx.pSubst_cons_get? (Γ : Ctx) (σ : Subst Ty)
    (x : String) (τ : Ty) (y : String) :
    (HasSubst.pSubst (Γ.cons x τ) σ).get? y =
      ((HasSubst.pSubst Γ σ).cons x (HasSubst.pSubst τ σ)).get? y := by
  rw [HashMap.pSubst_get?, Ctx.get?_cons, Ctx.get?_cons]
  rw [HashMap.pSubst_get?]
  by_cases hxy : x = y
  · subst hxy; simp
  · simp [hxy]

/-- A substitution `σ` *satisfies* a list of equations when applying it
to each side gives the same term. -/
def SatisfiesEqs (σ : Subst Ty) (eqs : Equations Ty) : Prop :=
  ∀ p ∈ eqs, HasSubst.pSubst p.1 σ = HasSubst.pSubst p.2 σ

theorem SatisfiesEqs.mono {σ : Subst Ty} {eqs eqs' : Equations Ty}
    (h : SatisfiesEqs σ eqs') (hsub : eqs ⊆ eqs') :
    SatisfiesEqs σ eqs :=
  fun p hp => h p (hsub hp)

/-! ## Soundness of `inferHM`.

If `σ` satisfies all the equations accumulated by `inferHM Γ e s`, then
`HasType` derives on the σ-substituted triple. -/

/-- `inferHM` is monotone in its accumulated equations: the final state
contains every equation from the initial state. -/
theorem inferHM_eqs_mono (Γ : Ctx) (e : Term) :
    ∀ {s s' : InferState} {τ : Ty},
    Term.inferHM Γ e s = .ok (τ, s') → s.eqs ⊆ s'.eqs := by
  induction e generalizing Γ with
  | var x =>
      intro s s' τ h
      unfold Term.inferHM at h
      split at h
      · cases h
      · cases h; exact fun _ hp => hp
  | lam x τ₁ body ih =>
      intro s s' τ h
      unfold Term.inferHM at h
      split at h
      · cases h
      · rename_i τ₂ s₁ h_inner
        cases h
        exact ih (Γ.cons x τ₁) h_inner
  | app e₁ e₂ ih₁ ih₂ =>
      intro s s' τ h
      unfold Term.inferHM at h
      split at h
      · cases h
      · rename_i τf s₁ h_e1
        split at h
        · cases h
        · rename_i τa s₂ h_e2
          cases h
          have h₁ := ih₁ Γ h_e1
          have h₂ := ih₂ Γ h_e2
          intro p hp
          exact List.mem_cons_of_mem _ (h₂ (h₁ hp))

/-- **Soundness of HM.** If `σ` satisfies all the equations accumulated
by `inferHM Γ e s`, then `HasType` derives on the σ-substituted triple. -/
theorem inferHM_sound (Γ : Ctx) (e : Term) :
    ∀ {s s' : InferState} {τ : Ty},
    Term.inferHM Γ e s = .ok (τ, s') →
    ∀ (σ : Subst Ty), SatisfiesEqs σ s'.eqs →
    HasType (HasSubst.pSubst Γ σ)
            (HasSubst.pSubst e σ)
            (HasSubst.pSubst τ σ) := by
  induction e generalizing Γ with
  | var x =>
      intro s s' τ h σ _
      unfold Term.inferHM at h
      split at h
      · cases h
      · rename_i τ' h_get
        cases h
        -- want HasType (pSubst Γ σ) (pSubst (var x) σ) (pSubst τ' σ)
        -- pSubst (var x) σ = var x
        show HasType _ (Term.tyPSubst (Term.var x) σ) _
        show HasType _ (Term.var x) _
        apply HasType.var
        rw [HashMap.pSubst_get?, h_get]
        rfl
  | lam x τ₁ body ih =>
      intro s s' τ h σ hSat
      unfold Term.inferHM at h
      split at h
      · cases h
      · rename_i τ₂ s₁ h_inner
        cases h
        show HasType _ (Term.tyPSubst (Term.lam x τ₁ body) σ)
              (HasSubst.pSubst (τ₁ ⇒ τ₂) σ)
        rw [Ty.pSubst_arrow]
        show HasType _ (Term.lam x (HasSubst.pSubst τ₁ σ)
                          (Term.tyPSubst body σ)) _
        apply HasType.lam
        have hbody := ih (Γ.cons x τ₁) h_inner σ hSat
        exact HasType.cong (fun y => Ctx.pSubst_cons_get? Γ σ x τ₁ y) hbody
  | app e₁ e₂ ih₁ ih₂ =>
      intro s s' τ h σ hSat
      unfold Term.inferHM at h
      split at h
      · cases h
      · rename_i τf s₁ h_e1
        split at h
        · cases h
        · rename_i τa s₂ h_e2
          cases h
          -- After cases, the returned τ = mvar s₂.counter, s'.eqs = (τf, τa ⇒ mvar s₂.counter) :: s₂.eqs
          -- σ satisfies s'.eqs ⊇ {(τf, τa ⇒ α)} ∪ s₂.eqs (mono) ∪ s₁.eqs (mono).
          have hα_constraint :
              HasSubst.pSubst τf σ =
              HasSubst.pSubst (τa ⇒ Ty.mvar s₂.counter) σ :=
            hSat (τf, τa ⇒ Ty.mvar s₂.counter) List.mem_cons_self
          have hSat₂ : SatisfiesEqs σ s₂.eqs := by
            intro p hp
            exact hSat p (List.mem_cons_of_mem _ hp)
          have hSat₁ : SatisfiesEqs σ s₁.eqs :=
            hSat₂.mono (inferHM_eqs_mono Γ e₂ h_e2)
          have hf := ih₁ Γ h_e1 σ hSat₁
          have ha := ih₂ Γ h_e2 σ hSat₂
          -- Goal: HasType (pSubst Γ σ) (pSubst (app e₁ e₂) σ) (pSubst (mvar s₂.counter) σ)
          show HasType _ (Term.tyPSubst (Term.app e₁ e₂) σ) _
          show HasType _ (Term.app (HasSubst.pSubst e₁ σ) (HasSubst.pSubst e₂ σ))
                (HasSubst.pSubst (Ty.mvar s₂.counter) σ)
          -- hα_constraint : pSubst τf σ = (pSubst τa σ) ⇒ (pSubst (mvar s₂.counter) σ)
          rw [Ty.pSubst_arrow] at hα_constraint
          rw [hα_constraint] at hf
          exact HasType.app hf ha

/-! ## TODO: completeness / MGU.

Standard HM completeness ("any σ' that makes the term type-check is more
general than HM's σ") requires the standard *principal types* /
*fresh-mvar extension* trick:

- The HM algorithm allocates fresh mvars (e.g. the `α` in the `app`
  case). The user's σ' has no entry for those — it never saw them.
- To get σ' to satisfy the HM-generated constraint `(τf, τa ⇒ α)`, we
  have to extend σ' with bindings `α ↦ <the type of the result>` etc.
- Then `unify_mgu` says HM's σ is more general than the *extended* σ';
  the extension itself is more general than σ' (it's an extension), so
  by transitivity HM's σ is more general than σ'.

This is the textbook HM completeness proof — sound in spirit, but the
extension construction + `MoreGeneral` transitivity proof is a real
chunk of work (~200 LOC). Deferred. -/

/-! ## Public verified elaborator. -/

open LambdaLab.Language in
/-- Walks the term collecting type constraints, calls `unify` to solve
them, and packages the result as an `ElaborateResult`. The `ok` carries
the *raw* inferred type τ — the user-visible resolved form is
`HasSubst.pSubst τ σ`. The `hSat` witness chains `inferHM_sound` with
`unify_unifies`. The `mgu` witness is still pending (`sorry`). -/
def Term.elaborate (Γ : Ctx) (e : Term) : ElaborateResult HasType Γ e :=
  match h_run : Term.inferHM Γ e { counter := HasVars.fresh e, eqs := [] } with
  | .error (.unbound x) =>
      .error (.unbound x) (by
        -- ¬ Elaborable HasType Γ e for unbound x. Same theorem family
        -- as MGU (HM completeness — typing-existence implies
        -- HM-doesn't-fail).
        sorry)
  | .error (.unifyFail _) =>
      .error (.unbound "internal: inferHM returned unifyFail") (by sorry)
  | .ok (τ, s) =>
      match h_unify : unify s.eqs with
      | none =>
          .error (.mismatch τ τ) (by
            -- ¬ Elaborable: HM completeness says any typing σ' would
            -- satisfy the collected constraints, but `unify` says they're
            -- unsatisfiable. Same theorem family as MGU.
            sorry)
      | some σ =>
          .ok τ ⟨σ,
            inferHM_sound Γ e h_run σ (unify_unifies s.eqs σ h_unify),
            by
              -- MGU witness — see the comment block earlier in this file
              -- for the proof sketch (fresh-mvar extension + transitivity).
              sorry⟩

/-- Closed-term entry point. -/
def Term.elaborateClosed (e : Term) :
    LambdaLab.Language.ElaborateResult HasType Ctx.empty e :=
  e.elaborate Ctx.empty

end LambdaLab.Stlc.Named
