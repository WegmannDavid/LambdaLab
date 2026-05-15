import LambdaLab.Stlc.Named.Typing
import LambdaLab.Stlc.Named.Unification
import LambdaLab.Stlc.Named.Properties
import LambdaLab.Substitution.Unification.Soundness
import LambdaLab.Substitution.Unification.MGU
import LambdaLab.Language.Basic

namespace LambdaLab.Stlc.Named

/-- Pick a `Nat` larger than the free metavariable indices of `Γ`,
`body`, `α`, and `τ`. Used by `W` and by `HasTypeW` to name the
yet-to-be-inferred body type in the lam case so that the resulting
substitution is determined (and, together with the unifier being an MGU,
is itself an MGU). -/
def freshIdxLam (Γ : Ctx) (body : Term) (α τ : Ty) : Nat :=
  max (HasVars.fresh Γ) (max (HasVars.fresh body)
    (max (HasVars.fresh α) (HasVars.fresh τ)))

/-- Pick a `Nat` larger than the free metavariable indices of `Γ`,
`e₁`, `e₂`, and `τ`. Used by `W` and by `HasTypeW` to name the
yet-to-be-inferred argument type in the app case. -/
def freshIdxApp (Γ : Ctx) (e₁ e₂ : Term) (τ : Ty) : Nat :=
  max (HasVars.fresh Γ) (max (HasVars.fresh e₁)
    (max (HasVars.fresh e₂) (HasVars.fresh τ)))

/-- A relational, bidirectional "algorithm-W"-style typing judgment.
`HasTypeW Γ e τ σ` says: when we ran algorithm W on `e` in `Γ` checking
against the expected type `τ`, it succeeded with witness substitution
`σ`. The intended invariant is `HasType (Γ[σ]) (e[σ]) (τ[σ])`, discharged
by `HasTypeW.toHasType` below.

Freshness is **baked into the relation**: the lam case names the body's
unknown type `Ty.mvar (freshIdxLam Γ body α τ)`, and the app case names
the argument type `Ty.mvar (freshIdxApp Γ e₁ e₂ τ)`. Combined with `unify`
being an MGU operation, this means `HasTypeW Γ e τ σ` admits exactly one
σ for each `(Γ, e, τ)` (when it admits any) — that σ is W's output,
which is the principal/most-general substitution.

The constructors mirror standard W:

* `var`: look up `x` in `Γ`, get `τ'`, unify the expected `τ` with `τ'`.
* `lam x α body`: type-check the body in the extended context against
  the fresh mvar `Ty.mvar (freshIdxLam Γ body α τ)`, then unify the
  expected `τ` with the inferred function type `α ⇒ Ty.mvar (…)`
  (under σ_body).
* `e₁ e₂`: type-check `e₁` against `Ty.mvar (freshIdxApp Γ e₁ e₂ τ) ⇒ τ`,
  getting σ₁; then type-check `e₂` *in the σ₁-refined context, against
  the σ₁-refined argument type, on the σ₁-substituted term*. Refining
  the second premise via σ₁ is what makes soundness composable —
  otherwise σ₁ and σ₂ might disagree on shared metavariables. -/
inductive HasTypeW : Ctx → Term → Ty → Subst Ty → Prop where
  | var {Γ x τ τ' σ} :
      Γ.get? x = some τ' →
      unify [(τ, τ')] = some σ →
      HasTypeW Γ (Term.var x) τ σ
  | lam {Γ x α body τ σ_body σ_unify} :
      HasTypeW (Γ.cons x α) body
               (Ty.mvar (freshIdxLam Γ body α τ)) σ_body →
      unify [(HasSubst.pSubst τ σ_body,
              HasSubst.pSubst (α ⇒ Ty.mvar (freshIdxLam Γ body α τ))
                              σ_body)] = some σ_unify →
      HasTypeW Γ (Term.lam x α body) τ (Subst.comp σ_unify σ_body)
  | app {Γ e₁ e₂ τ σ₁ σ₂} :
      HasTypeW Γ e₁ (Ty.mvar (freshIdxApp Γ e₁ e₂ τ) ⇒ τ) σ₁ →
      HasTypeW (HasSubst.pSubst Γ σ₁)
               (HasSubst.pSubst e₂ σ₁)
               (HasSubst.pSubst (Ty.mvar (freshIdxApp Γ e₁ e₂ τ)) σ₁)
               σ₂ →
      HasTypeW Γ (Term.app e₁ e₂) τ (Subst.comp σ₂ σ₁)

/-- **Soundness of `HasTypeW`.** If algorithm W succeeded with witness
σ, then the σ-substituted triple `(Γ[σ], e[σ], τ[σ])` has a `HasType`
derivation. The three constructor cases use, in order:

* `var`: `unify_unifies` (so the looked-up `τ'` agrees with `τ` under σ).
* `lam`: `HasType.subst` is not needed here — σ is unchanged across the
  premise — so this is just `HasType.cong` to bridge `pSubst (cons …) σ`
  with `cons (pSubst …) (pSubst …)`.
* `app`: lift the first IH via `HasType.subst` to `σ₂`, then rewrite both
  IHs through `Term.pSubst_comp`/`Ty.pSubst_comp` to make their
  substitutions agree at `comp σ₂ σ₁`, then combine via `HasType.app`
  and `HasType.cong` (for the context, which is only `get?`-extensional
  under the composition law). -/
theorem HasTypeW.toHasType : ∀ {Γ : Ctx} {e : Term} {τ : Ty} {σ : Subst Ty},
    HasTypeW Γ e τ σ →
    HasType (HasSubst.pSubst Γ σ)
            (HasSubst.pSubst e σ)
            (HasSubst.pSubst τ σ) := by
  intro Γ e τ σ h
  induction h with
  | var h_get h_unify =>
      apply HasType.var
      rw [HashMap.pSubst_get?, h_get]
      have heq := unify_unifies _ _ h_unify _ List.mem_cons_self
      exact congrArg some heq.symm
  | @lam Γ x α body τ σ_body σ_unify _ h_unify ih =>
      -- β := Ty.mvar (freshIdxLam Γ body α τ) baked into the constructor.
      -- ih : HasType ((Γ.cons x α)[σ_body]) (body[σ_body]) ((Ty.mvar k)[σ_body])
      -- Step 1: rewrite goal type τ[comp] → (α ⇒ Ty.mvar k)[comp] via the unifier.
      have h_eq : HasSubst.pSubst τ (Subst.comp σ_unify σ_body)
                = HasSubst.pSubst (α ⇒ Ty.mvar (freshIdxLam Γ body α τ))
                                  (Subst.comp σ_unify σ_body) := by
        rw [Ty.pSubst_comp, Ty.pSubst_comp]
        exact unify_unifies _ _ h_unify _ List.mem_cons_self
      rw [h_eq, Ty.pSubst_arrow]
      -- Step 2: apply HasType.lam (term position reduces by defn).
      apply HasType.lam
      -- Step 3: lift ih via σ_unify and bridge via cong + comp_get?.
      have ih_lifted := HasType.subst ih σ_unify
      rw [← Term.pSubst_comp, ← Ty.pSubst_comp] at ih_lifted
      apply HasType.cong _ ih_lifted
      intro y
      calc (HasSubst.pSubst (HasSubst.pSubst (Γ.cons x α) σ_body) σ_unify).get? y
          = (HasSubst.pSubst (Γ.cons x α) (Subst.comp σ_unify σ_body)).get? y :=
            (Ctx.pSubst_comp_get? (Γ.cons x α) σ_unify σ_body y).symm
        _ = ((HasSubst.pSubst Γ (Subst.comp σ_unify σ_body)).cons x
              (HasSubst.pSubst α (Subst.comp σ_unify σ_body))).get? y :=
            Ctx.pSubst_cons_get? Γ (Subst.comp σ_unify σ_body) x α y
  | @app Γ e₁ e₂ τ σ₁ σ₂ _ _ ih₁ ih₂ =>
      -- α := Ty.mvar (freshIdxApp Γ e₁ e₂ τ) baked into the constructor.
      -- ih₁ : HasType (Γ[σ₁]) (e₁[σ₁]) ((Ty.mvar k ⇒ τ)[σ₁])
      -- ih₂ : HasType ((Γ[σ₁])[σ₂]) ((e₂[σ₁])[σ₂]) (((Ty.mvar k)[σ₁])[σ₂])
      have ih₁' := HasType.subst ih₁ σ₂
      -- ih₁' : HasType ((Γ[σ₁])[σ₂]) ((e₁[σ₁])[σ₂]) (((α ⇒ τ)[σ₁])[σ₂])
      rw [← Term.pSubst_comp, ← Ty.pSubst_comp] at ih₁'
      rw [← Term.pSubst_comp, ← Ty.pSubst_comp] at ih₂
      -- ih₁' : HasType ((Γ[σ₁])[σ₂]) (e₁[comp σ₂ σ₁]) ((α ⇒ τ)[comp σ₂ σ₁])
      rw [Ty.pSubst_arrow] at ih₁'
      -- Combine into an app, in the doubly-substituted context.
      have h_app := HasType.app ih₁' ih₂
      -- Goal expects context Γ[comp σ₂ σ₁]; use cong via the comp lemma.
      exact HasType.cong
        (fun y => (Ctx.pSubst_comp_get? Γ σ₂ σ₁ y).symm) h_app



/-- **Algorithm W.** Given a context, a term, and an expected type,
return a substitution σ witnessing `HasTypeW Γ e τ σ` (when type-checking
succeeds). Three cases mirror the `HasTypeW` constructors:

* `var x`: look up `x` and unify the lookup with `τ`.
* `lam x α body`: pick a fresh `β`, recurse on `body` at `β`, then unify
  `τ[σ_body]` with `(α ⇒ β)[σ_body]`.
* `e₁ e₂`: pick a fresh `α`, recurse on `e₁` at `α ⇒ τ` to get `σ₁`, then
  recurse on `e₂[σ₁]` in `Γ[σ₁]` at `α[σ₁]`. -/
def W : (Γ : Ctx) → (e : Term) → (τ : Ty) → Option (Subst Ty)
  | Γ, .var x, τ =>
      match Γ.get? x with
      | none    => none
      | some τ' => unify [(τ, τ')]
  | Γ, .lam x α body, τ =>
      match W (Γ.cons x α) body (Ty.mvar (freshIdxLam Γ body α τ)) with
      | none        => none
      | some σ_body =>
          match unify [(HasSubst.pSubst τ σ_body,
                        HasSubst.pSubst (α ⇒ Ty.mvar (freshIdxLam Γ body α τ))
                                        σ_body)] with
          | none          => none
          | some σ_unify  => some (Subst.comp σ_unify σ_body)
  | Γ, .app e₁ e₂, τ =>
      match W Γ e₁ (Ty.mvar (freshIdxApp Γ e₁ e₂ τ) ⇒ τ) with
      | none    => none
      | some σ₁ =>
          match W (HasSubst.pSubst Γ σ₁)
                  (HasSubst.pSubst e₂ σ₁)
                  (HasSubst.pSubst (Ty.mvar (freshIdxApp Γ e₁ e₂ τ)) σ₁) with
          | none    => none
          | some σ₂ => some (Subst.comp σ₂ σ₁)
  termination_by _ e _ => e.size
  decreasing_by
    all_goals simp_wf
    · -- body for lam
      simp only [Term.size]; omega
    · -- e₁ for app
      simp only [Term.size]; omega
    · -- pSubst e₂ σ₁ for app
      show (Term.tyPSubst e₂ σ₁).size < _
      rw [Term.tyPSubst_size]
      simp only [Term.size]; omega

/-- **Correctness of `W`.** If `W` succeeds with σ, then `HasTypeW`
holds at the same triple. Recursive proof, descending on `Term.size`
along the same well-founded relation `W` itself uses. -/
theorem W_correct : ∀ (Γ : Ctx) (e : Term) (τ : Ty) (σ : Subst Ty),
    W Γ e τ = some σ → HasTypeW Γ e τ σ
  | Γ, .var x, τ, σ, h_W => by
      simp only [W] at h_W
      split at h_W
      · cases h_W
      · rename_i τ' h_get
        exact HasTypeW.var h_get h_W
  | Γ, .lam x α body, τ, σ, h_W => by
      simp only [W] at h_W
      split at h_W
      · cases h_W
      · rename_i σ_body h_body
        split at h_W
        · cases h_W
        · rename_i σ_unify h_unify
          rw [Option.some.injEq] at h_W
          subst h_W
          have ih := W_correct (Γ.cons x α) body _ σ_body h_body
          exact HasTypeW.lam ih h_unify
  | Γ, .app e₁ e₂, τ, σ, h_W => by
      simp only [W] at h_W
      split at h_W
      · cases h_W
      · rename_i σ₁ h_e1
        split at h_W
        · cases h_W
        · rename_i σ₂ h_e2
          rw [Option.some.injEq] at h_W
          subst h_W
          have ih₁ := W_correct Γ e₁ _ σ₁ h_e1
          have ih₂ := W_correct _ _ _ σ₂ h_e2
          exact HasTypeW.app ih₁ ih₂
  termination_by Γ e _ _ _ => e.size
  decreasing_by
    all_goals (simp_wf; first
      | (simp only [Term.size]; omega)
      | (show (Term.tyPSubst _ _).size < _
         rw [Term.tyPSubst_size]; simp only [Term.size]; omega))

/-- Source-fresh threshold: any `k ≥ srcFresh Γ e τ` is not free in
any of `Γ`, `e`, `τ`. Used by `W_principal` to prune W's internal
fresh-mvar bindings from the substitution exposed at the elaboration
boundary. -/
def srcFresh (Γ : Ctx) (e : Term) (τ : Ty) : Nat :=
  max (HasVars.fresh Γ) (max (HasVars.fresh e) (HasVars.fresh τ))

/-- **Principal types theorem for W (option D form).** For any σ' that
types the σ'-substituted triple, W succeeds with some σ, and **σ
restricted to source mvars** is at least as general as σ'.

Why the restriction? σ's full domain may include W's internal fresh
mvars (introduced by `freshIdxLam`/`freshIdxApp`), to which σ' is
freshness-blind. Quantifying `MoreGeneral` over *all* `t` then fails at
`t = mvar k` for those internal `k` — σ commits to a concrete type but
σ' is undefined. Pruning σ before quoting MoreGeneral removes the
internal bindings, recovering the universal-`t` form.

**Status:** statement updated; proofs are all `sorry`. Lifting the
old var/lam/app sketches to the pruned form is the next task. -/
theorem W_principal : ∀ (Γ : Ctx) (e : Term) (τ : Ty) (σ' : Subst Ty),
    HasType (HasSubst.pSubst Γ σ')
            (HasSubst.pSubst e σ')
            (HasSubst.pSubst τ σ') →
    ∃ σ, W Γ e τ = some σ ∧
         MoreGeneral (Subst.restrictBelow σ (srcFresh Γ e τ)) σ' := by
  -- Recursion structure: induct on `Term.size` to match W's recursion.
  -- All three cases sorried until the option-D proof is filled in.
  intro Γ e τ σ' _h
  sorry

/-- W succeeds whenever any substitution makes the triple well-typed. -/
theorem W_complete {Γ : Ctx} {e : Term} {τ : Ty} {σ' : Subst Ty}
    (h : HasType (HasSubst.pSubst Γ σ')
                 (HasSubst.pSubst e σ')
                 (HasSubst.pSubst τ σ')) :
    W Γ e τ ≠ none := by
  obtain ⟨σ, h_W, _⟩ := W_principal Γ e τ σ' h
  rw [h_W]
  exact Option.some_ne_none σ

/-- Corollary of `W_principal` once W's returned σ is fixed. Returns
the pruned-σ form (option D). -/
theorem W_principal_of_eq {Γ : Ctx} {e : Term} {τ : Ty} {σ σ' : Subst Ty}
    (h_W : W Γ e τ = some σ)
    (h : HasType (HasSubst.pSubst Γ σ')
                 (HasSubst.pSubst e σ')
                 (HasSubst.pSubst τ σ')) :
    MoreGeneral (Subst.restrictBelow σ (srcFresh Γ e τ)) σ' := by
  obtain ⟨σ₀, h_W₀, h_mgu⟩ := W_principal Γ e τ σ' h
  rw [h_W] at h_W₀
  have : σ = σ₀ := by injection h_W₀
  rw [this]
  exact h_mgu

/-- The σ exposed to elaboration consumers: W's output pruned to keys
strictly below the source-fresh threshold. The unpruned σ may bind W's
internal scaffolding mvars; the pruned form drops those so the
`MoreGeneral` field's `∀ t` quantifier works against arbitrary σ'. -/
private def elabσ (Γ : Ctx) (e : Term) (τ : Ty) (σ_full : Subst Ty) : Subst Ty :=
  Subst.restrictBelow σ_full (srcFresh Γ e τ)

def Term.elaborate :
    (Γ : Ctx) → (e : Term) → (τ : Ty) → Language.ElaborationResult HasType Γ e τ
  | Γ, e, τ =>
      match Heq : W Γ e τ with
      | none   =>
          Language.ElaborationResult.error
            (fun ⟨_σ', hSat, _⟩ => W_complete hSat Heq)
      | some σ_full =>
          Language.ElaborationResult.ok
          { σ := elabσ Γ e τ σ_full
            hSat := by
              -- HasType on (Γ[σ_pruned], e[σ_pruned], τ[σ_pruned]) from
              -- HasType on (Γ[σ_full], …) via pSubst_restrictBelow on
              -- Γ, e, τ (whose fresh is bounded by srcFresh). Needs
              -- Term/Ctx specializations of pSubst_restrictBelow.
              sorry
            mgu := fun σ' h_σ' => W_principal_of_eq Heq h_σ' }

end LambdaLab.Stlc.Named
