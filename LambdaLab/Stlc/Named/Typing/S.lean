import LambdaLab.Stlc.Named.Typing.D
import LambdaLab.Stlc.Named.Typing.Properties

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

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N] [HasVars N]

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
        rw [TypeSystem.Named.Context.get?_cons, TypeSystem.Named.Context.get?_cons, hΓ]))

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

omit [HasVars N] in
/-- The kernel judgement embeds. -/
theorem HasType.toS {Γ : Ctx N} {e : Term N} {τ : Ty} (h : HasType Γ e τ) :
    HasTypeS (SCtx.ofMono Γ) e τ := by
  induction h with
  | var hget =>
      exact HasTypeS.var (by rw [SCtx.ofMono_get?, hget]; rfl) Scheme.Instantiates.mono
  | lam _ ih => exact HasTypeS.abs (HasTypeS.cong (SCtx.ofMono_cons_get? _ _ _) ih)
  | app _ _ ih₁ ih₂ => exact HasTypeS.app ih₁ ih₂

omit [HasVars N] in
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

omit [HasVars N] in
/-- The equivalence, packaged. -/
theorem HasTypeS.iff_hasType {Γ : Ctx N} {e : Term N} {τ : Ty} :
    HasTypeS (SCtx.ofMono Γ) e τ ↔ HasType Γ e τ :=
  ⟨HasTypeS.toHasType, HasType.toS⟩

/-! ## Completeness fails — `D` is strictly stronger

The remaining direction is the article's weakened statement

```
Γ ⊢_D e:σ  ⟹  Γ ⊢_S e:τ  ∧  Γ̄(τ) ⊑ σ
```

**It is false here**, and not for the article's reason. There, `[Abs]` *chooses* the parameter
type, so `S` can pick whatever the use site needs. Ours is written in the term, so `S` is stuck
with it — while `D` can still `[Gen]` the annotation's metavariable and `[Inst]` it back down to
something else entirely.

Take `Γ = a : ⋆` and `e = (λ x : ?0 . x) a`. `HasType` — hence `S`, by `iff_hasType` — cannot type
it at all: the annotation forces the argument to be `?0`, and `a` is `⋆`. But `D` derives
`.mono ⋆` for it, by generalising `?0` (not free in `Γ`) and instantiating at `⋆`.

So `D` types *terms* the other systems reject, not merely more schemes for the same terms. Earlier
notes in `D.lean` and `J.lean` claimed the opposite — that with no `let` nothing can consume a `∀`.
That was wrong: `[Inst]` consumes one on the *conclusion*, with no context involvement at all.
-/

def Γa : Ctx String := Ctx.empty.cons "a" Ty.base
def eApp : Term String := .app polyId (.var "a")

/-- `⋆` has no free metavariables. `decide` cannot see this — `Signature.occurs` is
well-founded recursion and does not reduce in the kernel — so it goes through
`occurs_construct` at the nullary constructor. -/
theorem Ty.not_isFree_base (n : Nat) : ¬ HasVars.isFree Ty.base n := by
  show ¬ (Signature.occurs n Ty.base = true)
  rw [show (Ty.base : Ty)
        = Signature.construct (Sum.inr ⟨TyConstructor.base, Vector.ofFn Fin.elim0⟩) from rfl,
      Signature.occurs_construct]
  simp
  exact fun x => x.elim0

/-- `λ x : ?0 . x` types in *any* context — the body just reads the binder back. -/
theorem polyId_hasType_any (Γ : Ctx String) : HasType Γ polyId (Ty.mvar 0 ⇒ Ty.mvar 0) :=
  HasType.lam (HasType.var (by rw [Ctx.get?_cons]; simp))

theorem Γa_get : Γa.get? "a" = some Ty.base := by rw [Γa, Ctx.get?_cons]; simp

/-- `HasType` cannot type it: the annotation forces the argument to be `?0`, but `a : ⋆`. -/
theorem eApp_no_hasType : ∀ τ, ¬ HasType Γa eApp τ := by
  intro τ h
  obtain ⟨α, hfun, harg⟩ := HasType.app_inv h
  obtain ⟨β, hβ, -⟩ := HasType.lam_inv hfun
  -- hβ : α ⇒ τ = ?0 ⇒ β, so α = ?0
  have hα : α = Ty.mvar 0 := by injection hβ
  rw [hα] at harg
  have := HasType.var_inv harg
  rw [Γa_get] at this
  exact absurd this (by decide)

/-- 0 is not free in `Γa`: its only entry, `a : ⋆`, has no metavariables. -/
theorem Γa_zero_not_free : ¬ SCtx.IsFree (SCtx.ofMono Γa) 0 := by
  rintro ⟨x, σ, hx, hf⟩
  rw [SCtx.ofMono_get?] at hx
  obtain ⟨τ₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hx
  rw [Γa, Ctx.get?_cons] at h₀
  by_cases hxa : "a" = x
  · rw [if_pos hxa] at h₀
    cases h₀
    exact Ty.not_isFree_base 0 hf
  · rw [if_neg hxa, Ctx.get?_empty] at h₀
    exact absurd h₀ (by simp)

/-- …but `D` can, by generalising the identity and instantiating it at `⋆`. -/
theorem eApp_hasTypeD : HasTypeD (SCtx.ofMono Γa) eApp (.mono Ty.base) := by
  -- [Gen]: quantify the annotation's metavariable, which the context does not mention
  have hgen : HasTypeD (SCtx.ofMono Γa) polyId polyIdScheme :=
    HasTypeD.gen (HasType.toD (polyId_hasType_any Γa)) Γa_zero_not_free
  -- [Inst]: bring it back down at ⋆, which the annotation never permitted
  have hinst : HasTypeD (SCtx.ofMono Γa) polyId (.mono (Ty.base ⇒ Ty.base)) := by
    refine HasTypeD.inst hgen ?_
    intro ρ hρ
    rw [Scheme.instantiates_mono_iff] at hρ
    exact hρ ▸ polyIdScheme_inst
  have hvar : HasTypeD (SCtx.ofMono Γa) (.var "a") (.mono Ty.base) :=
    HasTypeD.var (by rw [SCtx.ofMono_get?, Γa_get]; rfl)
  exact HasTypeD.app hinst hvar

/-- **`D` is strictly stronger than the kernel judgement**, even with no `let`. -/
theorem HasTypeD.stronger_than_hasType :
    ∃ (Γ : Ctx String) (e : Term String) (σ : Scheme),
      HasTypeD (SCtx.ofMono Γ) e σ ∧ ∀ τ, ¬ HasType Γ e τ :=
  ⟨Γa, eApp, .mono Ty.base, eApp_hasTypeD, eApp_no_hasType⟩

/-! ### What this means for the lattice

`HasType ↔ S ⟹ D` is proved and the last arrow is strict. Recovering an equivalence needs one of:

* dropping binder annotations, so `[Abs]` may choose — the article's setting, where the missing
  half is only the *strong* form and the weakened one holds; or
* restricting `D` so `[Gen]` cannot quantify a variable that occurs in an annotation of the term,
  which is the honest reading of "these `∀`s are unreachable" that the earlier notes wanted; or
* accepting `D` as a strictly larger system and stating the bridge one-way, as it now is.

Either way `SCtx.close` (Γ̄) stays unused until `Term` has `let`, which is the construct all of
this machinery exists for.
-/

end LambdaLab.Stlc.Named
