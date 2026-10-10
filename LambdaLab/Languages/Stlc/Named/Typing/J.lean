import LambdaLab.Stlc.Named.Typing.Basic
import LambdaLab.Stlc.Named.Typing.Properties
import LambdaLab.Stlc.Named.Typing.Unification
import LambdaLab.Nominal.Unification.MGU

/-!
# Constraint generation — the `J`-style route to principal types

`W` (`Typing/W.lean`) interleaves solving with traversal: it unifies at every node and threads the
resulting substitution into the remaining premises. That is the shape Milner's presentation uses,
and, as the standard account puts it, W "was formulated to aid the proof of soundness" — which is
exactly how it has played out here. `W_correct` and `HasTypeW.toHasType` went through; principality
is stuck, and stuck *because* of the interleaving: the fresh index at each node is
computed from the arguments at hand, so an index consumed in one subcall can be re-consumed by a
sibling whose arguments happen not to mention it.

This file takes the other route, due to Wand: **generate all the constraints first, solve once at
the end**. Nothing is substituted during the walk, so no freshness invariant has to survive a
substitution, and the fresh supply is a counter that only ever goes up.

The payoff is that the three properties separate, and principality stops being an induction at all:

* **soundness** — any solution of the generated constraints is a typing (`HasTypeJ.sound`, below);
* **completeness** — any typing gives a solution of the constraints;
* **principality** — the *most general* solution is `unify`'s, which is `unify_mgu`. No induction
  over the term is involved: the work was already done by constraint generation.

## Why this is so short here

Two features of this STLC make generation almost trivial compared with the textbook presentation.

There are **no type schemes** in `Ty` — it is `base | arrow | mvar`, with no `∀` — so `HasType` is
already monotype-only and syntax-directed, and generation has no `[Inst]`/`[Gen]` to fold away.
Our `mvar`s are unification variables here, not bound type variables. (`Typing/D.lean` does add
schemes, and turns out to be *strictly* stronger for it — see `HasTypeD.stronger_than_hasType`.
That system is a specification to compare against, not one this file implements.)

And **binders carry their annotation** (`lam x α body`), so `Abs` invents nothing. The *only* rule
that draws on the supply is `App`, for the result type of the application.

## Shape of the presentation

Laid out like `W`: an inductive **judgement** `HasTypeJ` carrying the rules, and a **function**
`gen` computing it, bridged by `gen_correct` exactly as `W_correct` bridges `W` to `HasTypeW`. The
judgement is what the proofs induct over — the interesting properties are properties of
derivations, and inducting on a derivation avoids picking apart the function's `Option` plumbing.

Following the standard presentation of algorithm J, the supply is threaded explicitly rather than
left to a side effect, so a rule may *name* the variable it draws:

```
             Γ x = τ
  ────────────────────────────  Var
     n; Γ ⊢ x : τ ⊣ ∅ ; n

        n; Γ,x:α ⊢ e : τ ⊣ C ; n'
  ─────────────────────────────────────  Abs   (α is written, so nothing is drawn)
   n; Γ ⊢ λx:α.e : α→τ ⊣ C ; n'

   n; Γ ⊢ e₁ : τ₁ ⊣ C₁ ; n₁      n₁; Γ ⊢ e₂ : τ₂ ⊣ C₂ ; n₂
  ─────────────────────────────────────────────────────────────  App
   n; Γ ⊢ e₁ e₂ : βₙ₂ ⊣ {τ₁ = τ₂→βₙ₂} ∪ C₁ ∪ C₂ ; n₂+1
```

`W` is left exactly as it is. The two are not rivals: `HasTypeJ` says "what must hold", `W` says
"here is a witness, built incrementally".
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N]

/-! ## The judgement

`n; Γ ⊢ e : τ ⊣ C; n'` — starting with the supply at `n`, `e` is assigned `τ` subject to `C`, and
the supply ends at `n'`. Only `app` draws on the supply; only `var` can fail to apply, and it fails
by there being no rule, which is how an unbound variable is rejected.
-/

/-- **Constraint generation as a judgement.** The `Nat`s thread the fresh-variable supply. -/
inductive HasTypeJ : Nat → Ctx N → Term N → Ty → Equations Ty → Nat → Prop where
  | var {n Γ x τ} :
      Γ.get? x = some τ →
      HasTypeJ n Γ (.var x) τ [] n
  | lam {n Γ x α body τb C n'} :
      HasTypeJ n (Γ.cons x α) body τb C n' →
      HasTypeJ n Γ (.lam x α body) (α ⇒ τb) C n'
  | app {n Γ e₁ e₂ τ₁ τ₂ C₁ C₂ n₁ n₂} :
      HasTypeJ n Γ e₁ τ₁ C₁ n₁ →
      HasTypeJ n₁ Γ e₂ τ₂ C₂ n₂ →
      HasTypeJ n Γ (.app e₁ e₂) (Ty.mvar n₂)
        ((τ₁, τ₂ ⇒ Ty.mvar n₂) :: (C₁ ++ C₂)) (n₂ + 1)

/-- The supply only ever moves forward. This is the invariant that makes the drawn names actually
fresh — and the one W's argument-derived indices fail to provide. -/
theorem HasTypeJ.supply_le {n : Nat} {Γ : Ctx N} {e : Term N} {τ : Ty} {C : Equations Ty} {n' : Nat}
    (h : HasTypeJ n Γ e τ C n') : n ≤ n' := by
  induction h with
  | var _ => exact Nat.le_refl _
  | lam _ ih => exact ih
  | app _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ (Nat.le_trans ih₂ (Nat.le_succ _))

/-! ## Soundness

Any substitution satisfying the constraints turns the assigned type into a real typing. By
induction on the derivation. Note the shape: `σ` is applied to the context, the term (its
annotations) and the type alike, matching `HasType.subst`'s statement that typing is stable under
substitution.
-/

/-- **Soundness of generation.** Every solution of the constraints is a typing. -/
theorem HasTypeJ.sound {n : Nat} {Γ : Ctx N} {e : Term N} {τ : Ty} {C : Equations Ty} {n' : Nat}
    (h : HasTypeJ n Γ e τ C n') {σ : Subst Nat Ty} (hσ : Subst.Unifies σ C) :
    HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst e σ) (HasSubst.pSubst τ σ) := by
  induction h with
  | @var n Γ x τ hget =>
      refine HasType.var ?_
      rw [HashMap.pSubst_get?, hget]
      rfl
  | @lam n Γ x α body τb C n' _ ih =>
      -- transport the body's typing across `pSubst (Γ.cons x α) σ ≅ (pSubst Γ σ).cons x (α[σ])`
      have hb : HasType ((HasSubst.pSubst Γ σ).cons x (HasSubst.pSubst α σ))
          (HasSubst.pSubst body σ) (HasSubst.pSubst τb σ) :=
        HasType.cong (fun y => Ctx.pSubst_cons_get? Γ σ x α y) (ih hσ)
      rw [Ty.pSubst_arrow]
      exact HasType.lam hb
  | @app n Γ e₁ e₂ τ₁ τ₂ C₁ C₂ n₁ n₂ _ _ ih₁ ih₂ =>
      -- the head constraint says e₁'s type is a function into the drawn result name
      have hhead : HasSubst.pSubst τ₁ σ = HasSubst.pSubst (τ₂ ⇒ Ty.mvar n₂) σ :=
        hσ _ List.mem_cons_self
      have h₁ := ih₁ (fun q hq => hσ q (List.mem_cons_of_mem _ (List.mem_append_left _ hq)))
      have h₂ := ih₂ (fun q hq => hσ q (List.mem_cons_of_mem _ (List.mem_append_right _ hq)))
      rw [hhead, Ty.pSubst_arrow] at h₁
      exact HasType.app h₁ h₂

/-! ## The algorithm

`gen` computes the judgement. It fails only on an unbound variable — every other kind of
ill-typedness shows up as an unsatisfiable constraint set, not as a failure here. That separation
is the point.
-/

/-- **Constraint generation, computed.** Structural on the term; `Γ` and the supply are arguments
because both change on the way down. -/
def gen : Ctx N → Term N → Nat → Option (Ty × Equations Ty × Nat)
  | Γ, .var x, n => (Γ.get? x).map fun τ => (τ, [], n)
  | Γ, .lam x α body, n =>
      match gen (Γ.cons x α) body n with
      | none => none
      | some (τb, C, n') => some (α ⇒ τb, C, n')
  | Γ, .app e₁ e₂, n =>
      match gen Γ e₁ n with
      | none => none
      | some (τ₁, C₁, n₁) =>
          match gen Γ e₂ n₁ with
          | none => none
          | some (τ₂, C₂, n₂) =>
              some (Ty.mvar n₂, (τ₁, τ₂ ⇒ Ty.mvar n₂) :: (C₁ ++ C₂), n₂ + 1)

/-- **`gen` computes `HasTypeJ`.** The counterpart of `W_correct`; with it, every property proved
about the judgement transfers to the function. -/
theorem gen_correct : ∀ (e : Term N) (Γ : Ctx N) (n : Nat) (τ : Ty) (C : Equations Ty) (n' : Nat),
    gen Γ e n = some (τ, C, n') → HasTypeJ n Γ e τ C n' := by
  intro e
  induction e with
  | var x =>
      intro Γ n τ C n' h
      rw [gen, Option.map_eq_some_iff] at h
      obtain ⟨τ₀, hget, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact HasTypeJ.var hget
  | lam x α body ih =>
      intro Γ n τ C n' h
      rw [gen] at h
      split at h
      · exact absurd h (by simp)
      · rename_i τb C₀ n₀ hp
        have he := Option.some.inj h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact HasTypeJ.lam (ih (Γ.cons x α) n τb C₀ n₀ hp)
  | app e₁ e₂ ih₁ ih₂ =>
      intro Γ n τ C n' h
      rw [gen] at h
      split at h
      · exact absurd h (by simp)
      · rename_i τ₁ C₁ n₁ hp₁
        split at h
        · exact absurd h (by simp)
        · rename_i τ₂ C₂ n₂ hp₂
          have he := Option.some.inj h
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact HasTypeJ.app (ih₁ Γ n τ₁ C₁ n₁ hp₁) (ih₂ Γ n₁ τ₂ C₂ n₂ hp₂)

/-! ## The two halves, composed

Generate, then solve once. `HasTypeJ.sound` already covers the result — no separate argument is
needed for the composite, which is the dividend of having split the phases.
-/

/-- **Inference**: generate the constraints, solve them with `unify`, apply the answer. -/
def inferPrincipal (Γ : Ctx N) (e : Term N) (n : Nat) : Option Ty :=
  match gen Γ e n with
  | none => none
  | some r =>
      match unify r.2.1 with
      | none => none
      | some σ => some (HasSubst.pSubst r.1 σ)

/-- Soundness of the composite, straight from `HasTypeJ.sound` and `unify_unifies`. -/
theorem inferPrincipal_sound {Γ : Ctx N} {e : Term N} {n : Nat} {τ : Ty}
    (h : inferPrincipal Γ e n = some τ) :
    ∃ σ, HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst e σ) τ := by
  rw [inferPrincipal] at h
  split at h
  · exact absurd h (by simp)
  · rename_i r hg
    split at h
    · exact absurd h (by simp)
    · rename_i σ hu
      obtain rfl := Option.some.inj h
      exact ⟨σ, (gen_correct e Γ n r.1 r.2.1 r.2.2 hg).sound (unify_unifies _ σ hu)⟩

/-! ### It runs

`inferPrincipal` computes: over `f : ?0, a : ⋆, g : ⋆ → ⋆` it types `f a` at the
still-unconstrained `?1` (solving `?0 := ⋆ → ?1`), and accepts `(λx:⋆.x) f` by solving
`⋆ → ⋆ = ?0 → ?1`. A genuine type error surfaces as an *unsatisfiable* constraint set, never as a
failure of generation: `(λx:⋆.x) g` generates `⋆ = ⋆ → ⋆`, which `unify` then rejects.

## What followed — both in `Typing/JComplete.lean`

Two theorems completed the story, and both are statements about `HasTypeJ`, so both are inductions
over a derivation rather than over the term. This is where the J route paid for itself: neither has
a counterpart for `W`, whose `app` case is still open.

**Completeness** — `HasTypeJ.complete_aux`, packaged as `generationComplete` and lifted to the
elaborator as `elabSubst_complete`. If `pSubst Γ σ' ⊢ pSubst e σ' : τ'` and `HasTypeJ n Γ e τ C n'`,
some `σ` satisfies `C` with `pSubst τ σ = τ'` and agrees with `σ'` on the source. The induction
extends `σ'` at the drawn names — legitimate precisely because `HasTypeJ.supply_le` makes them
monotone, with `HasTypeJ.fresh_bound` bounding which variables the constraints mention.
`Signature.pSubst_insert_fresh` is the workhorse, as in `W_principal_lam_step`.

Note the shape agreement finally took: `AgreeBelow n σ σ'` is a **numeric threshold** after all —
`∀ u, freshIdx u ≤ n → pSubst u σ = pSubst u σ'`. It works here and did not work for `W` because J
threads a *monotone counter*, so `n` genuinely bounds everything drawn so far; W's argument-derived
indices give no such `n`, which is the counterexample recorded in `Typing/W.lean`. The problem was
never the threshold, it was having a supply that respects one. The checking form also does not
induct — the `lam` case would have to split a declared `τ` that may be a bare metavariable — which
is why `complete_aux` is the synthesising form.

**Principality** — `elabSubst_principal_below`. Given completeness, `unify C` is a most general
solution by `unify_mgu`, existing whenever a solution does by `unify_complete`, with domain and
range confined to `C`'s own variables by `unify_supported`. No induction over the term at all, which
is the whole reason for splitting generation from solving. It holds **on the source** and cannot
hold unrestrictedly: `Typing/Principality.lean` refutes the `MoreGeneral` form for this very
elaborator.
-/

end LambdaLab.Stlc.Named
