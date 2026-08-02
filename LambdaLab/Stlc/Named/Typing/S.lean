import LambdaLab.Stlc.Named.Typing.D

/-!
# `S` — the syntactical Hindley–Milner system

The middle of the three. `D` (`Typing/D.lean`) says what a typing *is* but admits derivations of
many shapes for one term, because `[Inst]` and `[Gen]` may be interleaved anywhere. `S` removes
that freedom by folding them into the structural rules:

* `[Inst]` moves into `[Var]`, which now instantiates the looked-up scheme on the spot;
* `[Gen]` moves into `[Let]`, via `Γ̄` (`SCtx.close`, in `D.lean`);
* every judgement carries a **monotype**.

The result is syntax-directed: the term determines the shape of the derivation, which is what
makes an algorithm possible at all. `J` is then `S` with the monotypes chosen by a fresh supply
and unification.

## Only three rules here

```
   Γ x = σ    σ ⊑ τ            Γ ⊢ e₀ : τ→τ'    Γ ⊢ e₁ : τ         Γ, x:τ ⊢ e : τ'
  ─────────────────── Var     ─────────────────────────── App    ─────────────────── Abs
      Γ ⊢ x : τ                     Γ ⊢ e₀ e₁ : τ'                Γ ⊢ λx:τ.e : τ→τ'
```

`[Let]` is absent because `Term` has no `let`. That is the rule `Γ̄` exists for, so `SCtx.close`
goes unused here — it is proved in `D.lean` and waits for the term language to grow.

## What this file establishes

`HasTypeS.toD` is *consistency* (`S ⟹ D`), the easy half of the equivalence.

The interesting half in our setting is that **`S` over a monotype context is exactly `HasType`**
(`HasType.toS` and `HasTypeS.toHasType`). With no `let`, no scheme can ever enter the context, so
`[Var]`'s instantiation never has anything to instantiate — and the syntactical system collapses
onto the kernel judgement. That is the precise statement of a claim `D.lean` and `J.lean` had only
made in prose.

Completeness (`D ⟹ S`, weakened) is *not* here; see the end of the file for what it needs.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Language (NameAlphabet)

variable {N : Type} [NameAlphabet N] [HasVars N]

/-- **The syntactical system.** Judgements carry monotypes; instantiation happens at `[Var]`. -/
inductive HasTypeS : SCtx N → Term N → Ty → Prop where
  | var {Γ x σ τ} :
      Γ.get? x = some σ →
      Scheme.Instantiates σ τ →
      HasTypeS Γ (.var x) τ
  | app {Γ e₀ e₁ τ τ'} :
      HasTypeS Γ e₀ (τ ⇒ τ') →
      HasTypeS Γ e₁ τ →
      HasTypeS Γ (.app e₀ e₁) τ'
  | abs {Γ x τ e τ'} :
      HasTypeS (Γ.cons x (.mono τ)) e τ' →
      HasTypeS Γ (.lam x τ e) (τ ⇒ τ')

omit [HasVars N] in
/-- `S` reads the context only through `get?`. Unlike `D` this needs no side condition, there
being no `[Gen]` to constrain. -/
theorem HasTypeS.cong {Γ Γ' : SCtx N} {e : Term N} {τ : Ty}
    (hΓ : ∀ y, Γ.get? y = Γ'.get? y) (h : HasTypeS Γ e τ) : HasTypeS Γ' e τ := by
  induction h generalizing Γ' with
  | var hget hinst => exact HasTypeS.var (by rw [← hΓ]; exact hget) hinst
  | app _ _ ih₀ ih₁ => exact HasTypeS.app (ih₀ hΓ) (ih₁ hΓ)
  | abs _ ih =>
      exact HasTypeS.abs (ih (fun y => by
        rw [LambdaLab.Language.Context.get?_cons, LambdaLab.Language.Context.get?_cons, hΓ]))

/-! ## Consistency: `S ⟹ D` -/

omit [HasVars N] in
/-- A monotype is an instance of `.mono` of itself and nothing else. -/
theorem Scheme.instantiates_mono_iff {τ ρ : Ty} :
    Scheme.Instantiates (.mono τ) ρ ↔ ρ = τ := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact Scheme.Instantiates.mono

omit [HasVars N] in
/-- **Consistency.** Every `S` derivation is a `D` derivation — `[Var]`'s built-in instantiation
becomes a `[Var]` followed by `[Inst]`, and the other rules are unchanged. -/
theorem HasTypeS.toD {Γ : SCtx N} {e : Term N} {τ : Ty} (h : HasTypeS Γ e τ) :
    HasTypeD Γ e (.mono τ) := by
  induction h with
  | var hget hinst =>
      refine HasTypeD.inst (HasTypeD.var hget) ?_
      intro ρ hρ
      rw [Scheme.instantiates_mono_iff] at hρ
      exact hρ ▸ hinst
  | app _ _ ih₀ ih₁ => exact HasTypeD.app ih₀ ih₁
  | abs _ ih => exact HasTypeD.abs ih

/-! ## `S` on a monotype context *is* `HasType`

With no `let`, nothing ever puts a scheme into the context, so `[Var]`'s instantiation is always
trivial. Both directions are short; together they say the syntactical system adds nothing over the
kernel judgement in this language.
-/

/-- The kernel judgement embeds. -/
theorem HasType.toS {Γ : Ctx N} {e : Term N} {τ : Ty} (h : HasType Γ e τ) :
    HasTypeS (SCtx.ofMono Γ) e τ := by
  induction h with
  | var hget =>
      exact HasTypeS.var (by rw [SCtx.ofMono_get?, hget]; rfl) Scheme.Instantiates.mono
  | lam _ ih => exact HasTypeS.abs (HasTypeS.cong (SCtx.ofMono_cons_get? _ _ _) ih)
  | app _ _ ih₁ ih₂ => exact HasTypeS.app ih₁ ih₂

/-- …and nothing more is derivable: over a monotype context `S` gives exactly `HasType`. -/
theorem HasTypeS.toHasType : ∀ {Γ : Ctx N} {e : Term N} {τ : Ty},
    HasTypeS (SCtx.ofMono Γ) e τ → HasType Γ e τ := by
  intro Γ e
  induction e generalizing Γ with
  | var x =>
      intro τ h
      cases h with
      | var hget hinst =>
          rw [SCtx.ofMono_get?, Option.map_eq_some_iff] at hget
          obtain ⟨τ₀, h₀, rfl⟩ := hget
          rw [Scheme.instantiates_mono_iff] at hinst
          exact HasType.var (hinst ▸ h₀)
  | lam x α body ih =>
      intro τ h
      cases h with
      | abs hb =>
          exact HasType.lam (ih (HasTypeS.cong (fun y => (SCtx.ofMono_cons_get? Γ x α y).symm) hb))
  | app e₁ e₂ ih₁ ih₂ =>
      intro τ h
      cases h with
      | app h₀ h₁ => exact HasType.app (ih₁ h₀) (ih₂ h₁)

/-- The equivalence, packaged. -/
theorem HasTypeS.iff_hasType {Γ : Ctx N} {e : Term N} {τ : Ty} :
    HasTypeS (SCtx.ofMono Γ) e τ ↔ HasType Γ e τ :=
  ⟨HasTypeS.toHasType, HasType.toS⟩

/-! ## What completeness would need

The remaining half is the article's weakened statement

```
Γ ⊢_D e:σ  ⟹  Γ ⊢_S e:τ  ∧  Γ̄(τ) ⊑ σ
```

and it cannot be proved by picking *any* instance of `σ` for `τ`. Take `σ = ∀α.α→α` over the empty
context: instantiating at `⋆` gives `τ = ⋆→⋆`, whose closure `Γ̄(⋆→⋆) = ⋆→⋆` is *not* more general
than `∀α.α→α` — it has only the one instance. The witness has to be the **principal** instance,
i.e. `σ` instantiated at *fresh* variables, which is `inst(σ)` in the standard presentation of
algorithm J. That operation is not defined here; it needs a fresh supply, exactly as `HasTypeJ`
threads one.

Note also that the strong form is false regardless — one cannot derive `λx.x : ∀α.α→α` in `S`,
only `λx.x : α→α`, since `S`'s judgements are monotypes by construction. `D.lean`'s
`HasTypeD.instance_not_sound` is the same phenomenon reaching the kernel judgement.
-/

end LambdaLab.Stlc.Named
