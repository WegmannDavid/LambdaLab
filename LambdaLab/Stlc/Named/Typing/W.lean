import LambdaLab.Stlc.Named.Typing.Basic
import LambdaLab.Stlc.Named.Typing.Unification
import LambdaLab.Stlc.Named.Typing.Properties
import LambdaLab.Substitution.Unification.Soundness
import LambdaLab.Substitution.Unification.MGU

namespace LambdaLab.Stlc.Named

open LambdaLab.TypedLanguage (NameAlphabet)

variable {N : Type} [NameAlphabet N] [HasVars N]

/-- Pick a `Nat` larger than the free metavariable indices of `Γ`,
`body`, `α`, and `τ`. Used by `W` and by `HasTypeW` to name the
yet-to-be-inferred body type in the lam case so that the resulting
substitution is determined (and, together with the unifier being an MGU,
is itself an MGU). -/
def freshIdxLam (Γ : Ctx N) (body : (Term N)) (α τ : Ty) : Nat :=
  max (HasVars.fresh Γ) (max (HasVars.fresh body)
    (max (HasVars.fresh α) (HasVars.fresh τ)))

/-- Pick a `Nat` larger than the free metavariable indices of `Γ`,
`e₁`, `e₂`, and `τ`. Used by `W` and by `HasTypeW` to name the
yet-to-be-inferred argument type in the app case. -/
def freshIdxApp (Γ : Ctx N) (e₁ e₂ : (Term N)) (τ : Ty) : Nat :=
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
inductive HasTypeW : Ctx N → (Term N) → Ty → Subst Ty → Prop where
  | var {Γ : Ctx N} {x : N} {τ τ' σ} :
      Γ.get? x = some τ' →
      unify [(τ, τ')] = some σ →
      HasTypeW Γ (Term.var x) τ σ
  | lam {Γ : Ctx N} {x : N} {α body τ σ_body σ_unify} :
      HasTypeW (Γ.cons x α) body
               (Ty.mvar (freshIdxLam Γ body α τ)) σ_body →
      unify [(HasSubst.pSubst τ σ_body,
              HasSubst.pSubst (α ⇒ Ty.mvar (freshIdxLam Γ body α τ))
                              σ_body)] = some σ_unify →
      HasTypeW Γ (Term.lam x α body) τ (Subst.comp σ_unify σ_body)
  | app {Γ : Ctx N} {e₁ e₂ τ σ₁ σ₂} :
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
theorem HasTypeW.toHasType : ∀ {Γ : Ctx N} {e : (Term N)} {τ : Ty} {σ : Subst Ty},
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
def W : (Γ : Ctx N) → (e : (Term N)) → (τ : Ty) → Option (Subst Ty)
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
theorem W_correct : ∀ (Γ : Ctx N) (e : (Term N)) (τ : Ty) (σ : Subst Ty),
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
def srcFresh (Γ : Ctx N) (e : (Term N)) (τ : Ty) : Nat :=
  max (HasVars.fresh Γ) (max (HasVars.fresh e) (HasVars.fresh τ))

/-- W's internal fresh index for a lambda *is* the source threshold of the whole lambda: both are
the max over `Γ`, `α`, `body`, `τ`. So the recursive call's threshold is exactly one higher. -/
theorem freshIdxLam_eq_srcFresh (Γ : Ctx N) (x : N) (α τ : Ty) (body : Term N) :
    freshIdxLam Γ body α τ = srcFresh Γ (Term.lam x α body) τ := by
  simp only [freshIdxLam, srcFresh]
  have h : HasVars.fresh (Term.lam x α body) = max (HasVars.fresh α) (HasVars.fresh body) := rfl
  rw [h]; omega

/-- Same for application. -/
theorem freshIdxApp_eq_srcFresh (Γ : Ctx N) (e₁ e₂ : Term N) (τ : Ty) :
    freshIdxApp Γ e₁ e₂ τ = srcFresh Γ (Term.app e₁ e₂) τ := by
  simp only [freshIdxApp, srcFresh]
  have h : HasVars.fresh (Term.app e₁ e₂) = max (HasVars.fresh e₁) (HasVars.fresh e₂) := rfl
  rw [h]; omega

/-! ## Towards `W_principal`: the cases, in source-restricted form

`W_principal` as stated below cannot be inducted on directly (see its docstring). The workable form
prunes the *quantifier* rather than `σ`:

```
∃ σ, W Γ e τ = some σ ∧ ∃ ρ, ∀ t, fresh t ≤ srcFresh Γ e τ → t[σ'] = (t[σ])[ρ]
```

Two of the three cases are discharged below, as standalone steps taking the recursive results as
hypotheses, so they are checked without any `sorry`. What is missing is the `app` step; the note
after them records why it is not merely more of the same.
-/

/-- **Principality at a variable.** No threshold is needed here: `W` on a variable is a single
`unify`, so the answer is most general against *every* substitution, not just on the source
fragment. This is the base case of `W_principal`. -/
theorem W_principal_var (Γ : Ctx N) (x : N) (τ : Ty) (σ' : Subst Ty)
    (h : HasType (HasSubst.pSubst Γ σ') (HasSubst.pSubst (Term.var x) σ')
                 (HasSubst.pSubst τ σ')) :
    ∃ σ, W Γ (Term.var x) τ = some σ ∧ MoreGeneral σ σ' := by
  -- the term is unchanged by substitution, so the derivation is a context lookup
  have hlook : (HasSubst.pSubst Γ σ').get? x = some (HasSubst.pSubst τ σ') :=
    HasType.var_inv h
  rw [HashMap.pSubst_get?] at hlook
  obtain ⟨τ₀, h₀, hτ₀⟩ := Option.map_eq_some_iff.mp hlook
  -- σ' already unifies the one equation W poses
  have huni : Subst.Unifies σ' [(τ, τ₀)] := by
    intro p hp
    rcases List.mem_singleton.mp hp with rfl
    exact hτ₀.symm
  have hne : unify [(τ, τ₀)] ≠ none := unify_complete _ σ' huni
  obtain ⟨σ, hσ⟩ := Option.ne_none_iff_exists'.mp hne
  refine ⟨σ, ?_, unify_mgu _ σ hσ σ' huni⟩
  rw [W, h₀]
  exact hσ

/-- `fresh t ≤ k` says `k` itself is not free in `t`. -/
theorem not_isFree_of_fresh_le' {t : Ty} {k : Nat} (h : HasVars.fresh t ≤ k) :
    ¬ HasVars.isFree t k := fun hf => absurd (HasVars.fresh_gt_free t k hf) (by omega)

/-- **Principality at a lambda**, given the recursive result for the body. `k` is W's internal
fresh index, which `freshIdxLam_eq_srcFresh` identifies with the *outer* threshold. -/
theorem W_principal_lam_step (Γ : Ctx N) (x : N) (α τ : Ty) (body : Term N) (σ' : Subst Ty)
    (β : Ty) (k : Nat) (hk : freshIdxLam Γ body α τ = k)
    (hτβ : HasSubst.pSubst τ σ' = Ty.arrow (HasSubst.pSubst α σ') β)
    (σ_body ρ₁ : Subst Ty)
    (hW : W (Γ.cons x α) body (Ty.mvar k) = some σ_body)
    (hρ₁ : ∀ t : Ty, HasVars.fresh t ≤ srcFresh (Γ.cons x α) body (Ty.mvar k) →
        HasSubst.pSubst t (σ'.insert k β) = HasSubst.pSubst (HasSubst.pSubst t σ_body) ρ₁) :
    ∃ σ, W Γ (Term.lam x α body) τ = some σ ∧
      ∃ ρ, ∀ t : Ty, HasVars.fresh t ≤ srcFresh Γ (Term.lam x α body) τ →
        HasSubst.pSubst t σ' = HasSubst.pSubst (HasSubst.pSubst t σ) ρ := by
  have hfv : HasVars.fresh (Ty.mvar k) = k + 1 := Signature.fresh_var k
  -- the outer threshold *is* k; the inner one is at least k+1
  have hkout : srcFresh Γ (Term.lam x α body) τ = k := by
    rw [← freshIdxLam_eq_srcFresh Γ x α τ body]; exact hk
  have hk1 : k + 1 ≤ srcFresh (Γ.cons x α) body (Ty.mvar k) := by
    simp only [srcFresh, hfv]; omega
  have hτk : HasVars.fresh τ ≤ k := by simp only [freshIdxLam] at hk; omega
  have hαk : HasVars.fresh α ≤ k := by simp only [freshIdxLam] at hk; omega
  have hmvk : HasSubst.pSubst (Ty.mvar k) (σ'.insert k β) = β := by
    rw [Ty.pSubst_mvar, Std.HashMap.getD_insert]; simp
  -- ρ₁ unifies exactly the equation W poses at this step
  have hcheck : HasSubst.pSubst (HasSubst.pSubst τ σ_body) ρ₁
              = HasSubst.pSubst (HasSubst.pSubst (α ⇒ Ty.mvar k) σ_body) ρ₁ := by
    rw [← hρ₁ τ (by omega),
        Signature.pSubst_insert_fresh σ' k β τ (not_isFree_of_fresh_le' hτk), hτβ,
        Ty.pSubst_arrow, Ty.pSubst_arrow,
        ← hρ₁ α (by omega), ← hρ₁ (Ty.mvar k) (by omega),
        Signature.pSubst_insert_fresh σ' k β α (not_isFree_of_fresh_le' hαk), hmvk]
  have huni : Subst.Unifies ρ₁ [(HasSubst.pSubst τ σ_body,
                                 HasSubst.pSubst (α ⇒ Ty.mvar k) σ_body)] := by
    intro p hp; rcases List.mem_singleton.mp hp with rfl; exact hcheck
  obtain ⟨σ_unify, hu⟩ := Option.ne_none_iff_exists'.mp (unify_complete _ ρ₁ huni)
  obtain ⟨ρ₂, hρ₂⟩ := unify_mgu _ σ_unify hu ρ₁ huni
  refine ⟨Subst.comp σ_unify σ_body, ?_, ρ₂, fun t ht => ?_⟩
  · simp only [W, hk, hW, hu]
  · rw [hkout] at ht
    calc HasSubst.pSubst t σ'
        = HasSubst.pSubst t (σ'.insert k β) :=
          (Signature.pSubst_insert_fresh σ' k β t (not_isFree_of_fresh_le' ht)).symm
      _ = HasSubst.pSubst (HasSubst.pSubst t σ_body) ρ₁ := hρ₁ t (by omega)
      _ = HasSubst.pSubst (HasSubst.pSubst (HasSubst.pSubst t σ_body) σ_unify) ρ₂ :=
          hρ₂ (HasSubst.pSubst t σ_body)
      _ = HasSubst.pSubst (HasSubst.pSubst t (Subst.comp σ_unify σ_body)) ρ₂ := by
          rw [Ty.pSubst_comp]


/-! ### Why `app` does not follow the same way

The chain wanted at an application is

```
t[σ'] = t[σ'.insert j τ₁] = (t[σ₁])[ρ_a] = ((t[σ₁])[σ₂])[ρ_b] = (t[comp σ₂ σ₁])[ρ_b]
```

and the third step applies the *second* recursive result at `t[σ₁]`, so it needs
`fresh (t[σ₁]) ≤ srcFresh (Γ[σ₁]) (e₂[σ₁]) ((mvar j)[σ₁])`. That inner threshold is computed from
the σ₁-substituted arguments, and there is no reason for it to dominate `t[σ₁]`: take `t = mvar i`
with `i < j` a variable occurring in neither `Γ`, `e₂` nor `σ₁ j`. Then `fresh (t[σ₁]) = i + 1`
while the threshold can be far smaller, and the hypothesis says nothing there.

This is not a gap in the bookkeeping — support bounds (`SupportedBelow`, `unify_keys`,
`unify_range`) do not help, because the offending variable is small, not large. It is a property of
*this* `W`: `freshIdxLam`/`freshIdxApp` derive freshness from the arguments at hand, so an index
consumed in one subcall can be re-consumed in a sibling whose arguments happen not to mention it.
The standard treatments avoid this by threading a monotone fresh-variable supply through the
recursion and stating principality relative to a variable *set* that the supply is disjoint from.

So finishing this most likely means changing `W` to thread a counter — a change to the algorithm,
not only to the proof — after which the `app` case becomes the same shape as `lam` above.
-/

/-- **Principal types theorem for W (option D form).** For any σ' that
types the σ'-substituted triple, W succeeds with some σ, and **σ
restricted to source mvars** is at least as general as σ'.

Why the restriction? σ's full domain may include W's internal fresh
mvars (introduced by `freshIdxLam`/`freshIdxApp`), to which σ' is
freshness-blind. Quantifying `MoreGeneral` over *all* `t` then fails at
`t = mvar k` for those internal `k` — σ commits to a concrete type but
σ' is undefined. Pruning σ before quoting MoreGeneral removes the
internal bindings, recovering the universal-`t` form.

## Why the context must be ground

`Ctx.Ground Γ` is `free(Γ) = ∅`, and it is a genuine side condition, not tidiness. The standard
account records that the correspondence between W and the deductive system "can only be made for
contexts with `free(Γ) = ∅`", because the algorithm *refines* variables the context already
mentions, and the deduction rules permit no such refinement. Concretely, with `a : ⋆` and
`f : ?0`:

```
infer Γ (f a)   = none                     -- no derivation: ?0 is an atom, not an arrow
W     Γ (f a) ?9 = some {0 ↦ ⋆ → ?9, …}    -- W refines the context's own ?0
```

So W accepts terms the judgement rejects — it "fails to detect all type errors" — and any
completeness statement without the hypothesis is simply false. The earlier version of this theorem
omitted it.

Worth noting that `stlcElaboratable`'s groundness demand is exactly this condition, arrived at
independently from "no metavariable may leak between declarations".

**Status: open.** Beyond the missing side condition, the obstacle is the *shape of the statement*,
not missing lemmas — inducting on
this form directly fails, because the lam step needs the unify equations built from the
*unrestricted* `σ_body`, while the induction hypothesis only speaks about the pruned one, and W's
output domain legitimately contains internal fresh mvars above `srcFresh`.

The workable reformulation prunes the *quantifier* instead of `σ`:

```
∃ σ, W Γ e τ = some σ ∧ ∃ ρ, ∀ t, HasVars.fresh t ≤ srcFresh Γ e τ → t[σ'] = (t[σ])[ρ]
```

With that, `var` closes from `unify_complete` + `unify_mgu` + `unify_keys`; `lam` closes by
extending σ' at the fresh index (`pSubst_insert_fresh`) and feeding the induction hypothesis's ρ to
`unify_complete` — legitimate because `freshIdxLam_eq_srcFresh` above pins the recursive
threshold at exactly one more than the outer one, so `τ` and `α` are both inside it.

What is still missing is *support* bookkeeping, and only for `app` and for the final descent to
the pruned form: both need a substitution's ρ patched above a threshold, which needs to know that
the other substitution cannot see up there. `unify_keys`/`unify_range` supply exactly that for a
single `unify` call; what has to be added is closure of the bound under `Subst.comp`, and then a
strengthened induction that carries it. -/
theorem W_principal : ∀ (Γ : Ctx N) (e : (Term N)) (τ : Ty) (σ' : Subst Ty),
    Γ.Ground →
    HasType (HasSubst.pSubst Γ σ')
            (HasSubst.pSubst e σ')
            (HasSubst.pSubst τ σ') →
    ∃ σ, W Γ e τ = some σ ∧
         MoreGeneral (Subst.restrictBelow σ (srcFresh Γ e τ)) σ' := by
  intro Γ e τ σ' _hΓ _h
  sorry

/-- W succeeds whenever any substitution makes the triple well-typed. -/
theorem W_complete {Γ : Ctx N} {e : (Term N)} {τ : Ty} {σ' : Subst Ty}
    (hΓ : Γ.Ground)
    (h : HasType (HasSubst.pSubst Γ σ')
                 (HasSubst.pSubst e σ')
                 (HasSubst.pSubst τ σ')) :
    W Γ e τ ≠ none := by
  obtain ⟨σ, h_W, _⟩ := W_principal Γ e τ σ' hΓ h
  rw [h_W]
  exact Option.some_ne_none σ

/-- Corollary of `W_principal` once W's returned σ is fixed. Returns
the pruned-σ form (option D). -/
theorem W_principal_of_eq {Γ : Ctx N} {e : (Term N)} {τ : Ty} {σ σ' : Subst Ty}
    (hΓ : Γ.Ground)
    (h_W : W Γ e τ = some σ)
    (h : HasType (HasSubst.pSubst Γ σ')
                 (HasSubst.pSubst e σ')
                 (HasSubst.pSubst τ σ')) :
    MoreGeneral (Subst.restrictBelow σ (srcFresh Γ e τ)) σ' := by
  obtain ⟨σ₀, h_W₀, h_mgu⟩ := W_principal Γ e τ σ' hΓ h
  rw [h_W] at h_W₀
  have : σ = σ₀ := by injection h_W₀
  rw [this]
  exact h_mgu

/-! ## The elaboration boundary

`Elaboration`/`ElaborationResult` used to live in a general `Language` interface. They are stated
here instead, at STLC, because nothing else ever used them: the general interface's only instance
was STLC's, and its parser-free `Language` struct has been superseded by `Pipeline.Language`,
whose elaboration side (`ElaboratableLanguage`) is deliberately substitution-free.

What is kept is the part that interface got right and the synthetic one cannot say: `mgu` demands
the returned substitution be *most general*, not merely one that works. `ElaboratableLanguage`
can only demand determinism, so a language wanting principality has to state it — as here — in
its own terms.
-/

/-- A **principal** solution for `(Γ, e, τ)`: a substitution that types the triple, and is more
general than any other that does. `σ` is a field rather than an existential so callers can
destructure it in `Type`-valued definitions. -/
structure Elaboration (Γ : Ctx N) (e : Term N) (τ : Ty) : Type where
  σ    : Subst Ty
  hSat : HasType (HasSubst.pSubst Γ σ)
                 (HasSubst.pSubst e σ)
                 (HasSubst.pSubst τ σ)
  mgu  : ∀ σ' : Subst Ty,
           HasType (HasSubst.pSubst Γ σ')
                   (HasSubst.pSubst e σ')
                   (HasSubst.pSubst τ σ') →
           MoreGeneral σ σ'

/-- Elaborating `e` at `τ` under `Γ`: a principal solution, or a *proof* there is none. The error
branch carries a refutation rather than a diagnostic — restoring diagnostics means giving it a
payload. -/
inductive ElaborationResult (Γ : Ctx N) (e : Term N) (τ : Ty) : Type where
  | error : (Elaboration Γ e τ → False) → ElaborationResult Γ e τ
  | ok    : Elaboration Γ e τ → ElaborationResult Γ e τ

/-- The σ exposed to elaboration consumers: W's output pruned to keys
strictly below the source-fresh threshold. The unpruned σ may bind W's
internal scaffolding mvars; the pruned form drops those so the
`MoreGeneral` field's `∀ t` quantifier works against arbitrary σ'. -/
private def elabσ (Γ : Ctx N) (e : (Term N)) (τ : Ty) (σ_full : Subst Ty) : Subst Ty :=
  Subst.restrictBelow σ_full (srcFresh Γ e τ)

/-- Elaboration at a **ground** context. The hypothesis is not decoration: the correspondence
between W and the deductive system only holds for `free(Γ) = ∅`, which `Ctx.Ground` is (see
`W_principal`). -/
def Term.elaborate :
    (Γ : Ctx N) → Γ.Ground → (e : (Term N)) → (τ : Ty) → ElaborationResult Γ e τ
  | Γ, hΓg, e, τ =>
      match Heq : W Γ e τ with
      | none   =>
          ElaborationResult.error
            (fun ⟨_σ', hSat, _⟩ => W_complete hΓg hSat Heq)
      | some σ_full =>
          ElaborationResult.ok
          { σ := elabσ Γ e τ σ_full
            hSat := by
              -- `HasType` on the *pruned* triple from `HasType` on the full one. Each of Γ, e, τ
              -- has its free mvars below `srcFresh`, so dropping σ's bindings at or above that
              -- threshold — which is exactly W's internal scaffolding — changes nothing.
              have hbase := (W_correct Γ e τ σ_full Heq).toHasType
              have hΓ : HasVars.fresh Γ ≤ srcFresh Γ e τ := Nat.le_max_left _ _
              have he : HasVars.fresh e ≤ srcFresh Γ e τ :=
                Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
              have hτ : HasVars.fresh τ ≤ srcFresh Γ e τ :=
                Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
              show HasType (HasSubst.pSubst Γ (Subst.restrictBelow σ_full (srcFresh Γ e τ)))
                     (HasSubst.pSubst e (Subst.restrictBelow σ_full (srcFresh Γ e τ)))
                     (HasSubst.pSubst τ (Subst.restrictBelow σ_full (srcFresh Γ e τ)))
              rw [Term.tyPSubst_restrictBelow e σ_full _ he,
                  Signature.pSubst_restrictBelow σ_full _ τ hτ]
              -- the context only agrees key-by-key, which is what `cong` wants
              exact HasType.cong
                (fun y => (Ctx.pSubst_restrictBelow_get? Γ σ_full _ hΓ y).symm) hbase
            mgu := fun σ' h_σ' => W_principal_of_eq hΓg Heq h_σ' }

end LambdaLab.Stlc.Named
