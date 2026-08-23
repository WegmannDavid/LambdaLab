import LambdaLab.Stlc.Named.Typing.JComplete

/-!
# Principality is *not* `MoreGeneral` — a counterexample

`elabSubst_principal_below` (`JComplete.lean`) says every typing factors through the computed
substitution **on the source's own types**. The obvious question is why the restriction is there,
and the answer is not "the proof was hard": the unrestricted statement — `MoreGeneral σ σ'`, whose
`∃ ρ, ∀ t` ranges over *every* type — is **false** for this elaborator. This file proves it.

## The example, and why it is the smallest one

```
  Γ = f : ?0, g : ?1, b : ⋆        ⊢  f (g b) : ⋆
```

The type of `g b` is not determined by anything: `g` may return whatever `f` accepts. So the
principal answer has to *name* that type, and the only names available are the ones `gen` drew —
here `?2`, above the source threshold. The computed answer is

```
  ?0 ↦ ?2 ⇒ ⋆        ?1 ↦ ⋆ ⇒ ?2        (?2 itself unbound)
```

Now take the competing solution `σ' = {?0 ↦ ⋆ ⇒ ⋆, ?1 ↦ ⋆ ⇒ ⋆}`, which types the triple perfectly
well. `MoreGeneral` demands one ρ with `t[σ'] = (t[σ])[ρ]` for **every** `t`:

* at `t = ?0` it forces `ρ(?2) = ⋆`, since `⋆ ⇒ ⋆ = (?2 ⇒ ⋆)[ρ]`;
* at `t = ?2` it forces `ρ(?2) = ?2`, since σ does not bind `?2` and neither does σ'.

`⋆ ≠ ?2`, so no such ρ exists. Nothing about the algorithm is at fault — the same happens to any
elaborator whose answer is in solved form, because the escape is the *drawn variable itself*, and
`MoreGeneral` insists on being told about it.

## Why the answer is taken on trust here, and only here

The contradiction needs the computed σ, not merely a σ that types the triple: the substitution
`{?0 ↦ ?0 ⇒ ⋆, ?1 ↦ ⋆ ⇒ ?0}` — reusing a *source* variable as the name — is also a solution and
*is* `MoreGeneral` than every other one. So a proof that no most-general solution exists would be
proving something false; what is false is that the elaborator's answer is one.

`unify` is defined by well-founded recursion, so the kernel will not evaluate it, and `native_decide`
is what is left. It is confined to `ce_answer` below, and nothing on the live path depends on this
file — `#print axioms elabSubst_principal_below` stays clean.
-/

namespace LambdaLab.Stlc.Named

/-! ## The triple -/

/-- `f : ?0`, `g : ?1`, `b : ⋆`. -/
def ceCtx : Ctx String :=
  ((Ctx.empty.cons "b" Ty.base).cons "g" (Ty.mvar 1)).cons "f" (Ty.mvar 0)

/-- `f (g b)`: the intermediate type is unconstrained, so the principal answer must name it. -/
def ceTm : Term String := .app (.var "f") (.app (.var "g") (.var "b"))

/-- A competing typing: read every unknown as `⋆ ⇒ ⋆`. -/
def ceSol : Subst Ty :=
  ((∅ : Subst Ty).insert 0 (Ty.base ⇒ Ty.base)).insert 1 (Ty.base ⇒ Ty.base)

/-! ## What the elaborator answers -/

/-- **The computed answer, as far as the argument needs it.** `?0` goes to a type mentioning the
drawn `?2`, and `?2` itself is left free.

The one `native_decide` in the development: `unify` is well-founded, so the kernel cannot run it.
Only this file depends on the result. -/
theorem ce_answer :
    (elabSubst ceCtx ceTm Ty.base).map
        (fun σ => (HasSubst.pSubst (Ty.mvar 0) σ, HasSubst.pSubst (Ty.mvar 2) σ))
      = some (Ty.arrow (Ty.mvar 2) Ty.base, Ty.mvar 2) := by
  native_decide

/-- The elaborator succeeds on the triple, with an answer of that shape. -/
theorem ce_elabSubst : ∃ σ, elabSubst ceCtx ceTm Ty.base = some σ ∧
    HasSubst.pSubst (Ty.mvar 0) σ = Ty.arrow (Ty.mvar 2) Ty.base ∧
    HasSubst.pSubst (Ty.mvar 2) σ = Ty.mvar 2 := by
  have h := ce_answer
  cases hs : elabSubst ceCtx ceTm Ty.base with
  | none => rw [hs] at h; simp at h
  | some σ =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨σ, rfl, h.1, h.2⟩

/-! ## The competing typing -/

theorem ceCtx_f : ceCtx.get? "f" = some (Ty.mvar 0) := by
  simp only [ceCtx, Ctx.get?_cons]; simp
theorem ceCtx_g : ceCtx.get? "g" = some (Ty.mvar 1) := by
  simp only [ceCtx, Ctx.get?_cons]; simp
theorem ceCtx_b : ceCtx.get? "b" = some Ty.base := by
  simp only [ceCtx, Ctx.get?_cons]; simp

theorem ceSol_ctx {x : String} {τ : Ty} (h : ceCtx.get? x = some τ) :
    (HasSubst.pSubst ceCtx ceSol).get? x = some (HasSubst.pSubst τ ceSol) := by
  rw [HashMap.pSubst_get?, h]; rfl

/-- `⋆ ⇒ ⋆` for `f` and `g`, `⋆` for `b` — the triple really is typeable this way. -/
theorem ce_typing :
    HasType (HasSubst.pSubst ceCtx ceSol) (HasSubst.pSubst ceTm ceSol)
      (HasSubst.pSubst Ty.base ceSol) := by
  have hf : (HasSubst.pSubst ceCtx ceSol).get? "f" = some (Ty.base ⇒ Ty.base) := by
    rw [ceSol_ctx ceCtx_f]; simp [ceSol, Std.HashMap.getD_insert]
  have hg : (HasSubst.pSubst ceCtx ceSol).get? "g" = some (Ty.base ⇒ Ty.base) := by
    rw [ceSol_ctx ceCtx_g]; simp [ceSol]
  have hb : (HasSubst.pSubst ceCtx ceSol).get? "b" = some Ty.base := by
    rw [ceSol_ctx ceCtx_b]; simp [ceSol]
  have htm : HasSubst.pSubst ceTm ceSol = ceTm := rfl
  rw [htm, Ty.pSubst_base]
  exact .app (.var hf) (.app (.var hg) (.var hb))

/-! ## The refutation -/

/-- **The unrestricted form of `elabSubst_principal_below` is false.**

Exactly the statement `JComplete.lean` used to carry as a `sorry`, refuted at `N := String`. The
witness is the triple above; the two instances of `MoreGeneral`'s `∀ t` that collide are `?0` and
the drawn `?2`. -/
theorem elabSubst_not_principal :
    ¬ (∀ {N : Type} [LambdaLab.Nominal.Atom N] [HasVars N]
        {Γ : Ctx N} {t : Term N} {τ : Ty} {σ : Subst Ty},
        elabSubst Γ t τ = some σ →
        ∀ σ', HasType (HasSubst.pSubst Γ σ') (HasSubst.pSubst t σ') (HasSubst.pSubst τ σ') →
          MoreGeneral σ σ') := by
  intro H
  obtain ⟨σ, hσ, h0, h2⟩ := ce_elabSubst
  obtain ⟨ρ, hρ⟩ := H hσ ceSol ce_typing
  -- at `?0`: the drawn variable must go to `⋆`
  have e0 := hρ (Ty.mvar 0)
  -- at `?2`: σ does not bind it, and neither does σ', so it must stay itself
  have e2 := hρ (Ty.mvar 2)
  rw [h0] at e0
  rw [h2] at e2
  simp [ceSol, Std.HashMap.getD_insert] at e0
  simp [ceSol, Std.HashMap.getD_insert] at e2
  rw [← e2] at e0
  exact absurd e0 (by simp)

end LambdaLab.Stlc.Named
