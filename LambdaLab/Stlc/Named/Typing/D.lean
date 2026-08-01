import LambdaLab.Stlc.Named.Typing.Basic
import LambdaLab.Stlc.Named.Typing.Unification

/-!
# `D` — the declarative Hindley–Milner system

The specification end of the family. `HasTypeD` is what one *means* by "this term has this type";
`HasTypeW` and `HasTypeJ` are two ways to *find* one, and the content of the theory is that they
agree with `D`.

## The three systems, and why there are three

* **D** (here) — six rules, with `[Inst]` and `[Gen]` free-standing. They may be interleaved with
  the structural rules anywhere, so one term admits derivations of many different shapes. Good as
  a definition, useless as an algorithm.
* **S** — the syntactical system: `[Inst]` folded into `[Var]`, `[Gen]` folded into `[Let]`, and
  judgements restricted to monotypes. Now the term determines the shape of the derivation. The
  bridge to `D` is deliberately *weakened*: `Γ ⊢_D e : σ` gives `Γ ⊢_S e : τ` with `Γ̄(τ) ⊑ σ`,
  i.e. one final generalisation recovers the scheme.
* **J**/**W** — S plus a means of choosing the monotypes: a fresh supply and unification.
  `Typing/J.lean` and `Typing/W.lean`.

## What is faithful here, and what is not

Faithful: polytypes, free type variables, the specialisation order, and all of `[Var]`, `[App]`,
`[Abs]`, `[Inst]`, `[Gen]`.

Two deliberate departures, both because this is STLC and not Mini-ML:

* **No `[Let]`.** `Term` has no `let`, so the rule has nothing to fire on. It is the only rule that
  puts a scheme into the context, which is why let-polymorphism is the whole point of HM — and why
  its absence makes `D` collapse (see the end of the file).
* **`[Abs]` takes the binder type as given.** The article's `λx.e` leaves the parameter type to the
  rule; ours is written in the term. So `abs` below is the article's, restricted to the annotation
  the source supplies — which is exactly why `J` draws no fresh variable there.

Metavariables (`Ty.mvar`) serve as the type variables `α`. In `D` they are genuinely *bound* by
`∀`; in `W`/`J` they are *unification* variables. Same syntax, different role — and the reason
`Mvars.lean` insists `?n` is an opaque atom for the plain `HasType`.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Language (NameAlphabet)

variable {N : Type} [NameAlphabet N] [HasVars N]

/-! ## Polytypes

`σ = τ | ∀ α . σ` — quantifiers only at the top, which is what keeps HM decidable.
-/

/-- A type scheme: a monotype under zero or more `∀`s. -/
inductive Scheme where
  | mono : Ty → Scheme
  | all : Nat → Scheme → Scheme
  deriving DecidableEq, Repr

/-- `free(α) = {α}`, `free(∀ α . σ) = free(σ) − {α}`. On monotypes this is the `HasVars` notion
the unifier already uses. -/
def Scheme.IsFree : Scheme → Nat → Prop
  | .mono τ, n => HasVars.isFree τ n
  | .all α σ, n => n ≠ α ∧ Scheme.IsFree σ n

/-- A context assigning *schemes* — what `D` needs and `HasType` does not have. -/
abbrev SCtx (N : Type) [NameAlphabet N] : Type := LambdaLab.Language.Context N Scheme

/-- `free(Γ) = ⋃_{x:σ ∈ Γ} free(σ)`. -/
def SCtx.IsFree (Γ : SCtx N) (n : Nat) : Prop :=
  ∃ x σ, Γ.get? x = some σ ∧ Scheme.IsFree σ n

/-! ## Instantiation and the specialisation order

A scheme's *instances* are the monotypes reachable by instantiating every quantifier; `σ' ⊑ σ`
("σ' is more general") then says every instance of `σ` is already an instance of `σ'`. This is the
extensional reading of the article's rule, and the form `[Inst]` actually uses.
-/

/-- Substitute a monotype for one bound variable, stopping at a shadowing binder. -/
def Scheme.instAt : Scheme → Nat → Ty → Scheme
  | .mono τ, α, τ₀ => .mono (HasSubst.single τ α τ₀)
  | .all β σ, α, τ₀ => if β = α then .all β σ else .all β (Scheme.instAt σ α τ₀)

/-- `σ` instantiates to the monotype `τ`: peel each `∀`, choosing a witness for it. -/
inductive Scheme.Instantiates : Scheme → Ty → Prop where
  | mono {τ} : Scheme.Instantiates (.mono τ) τ
  | all {α σ τ₀ τ} :
      Scheme.Instantiates (σ.instAt α τ₀) τ →
      Scheme.Instantiates (.all α σ) τ

/-- `σ' ⊑ σ` — `σ'` is at least as general as `σ`. -/
def Scheme.Specializes (σ' σ : Scheme) : Prop :=
  ∀ τ : Ty, Scheme.Instantiates σ τ → Scheme.Instantiates σ' τ

theorem Scheme.Specializes.refl (σ : Scheme) : σ.Specializes σ := fun _ h => h

theorem Scheme.Specializes.trans {σ₁ σ₂ σ₃ : Scheme}
    (h₁ : σ₁.Specializes σ₂) (h₂ : σ₂.Specializes σ₃) : σ₁.Specializes σ₃ :=
  fun τ h => h₁ τ (h₂ τ h)

/-! ## The rules

```
      x:σ ∈ Γ                Γ ⊢ e₀ : τ→τ'   Γ ⊢ e₁ : τ
  ───────────── Var        ───────────────────────────── App
   Γ ⊢ x : σ                       Γ ⊢ e₀ e₁ : τ'

   Γ, x:τ ⊢ e : τ'           Γ ⊢ e : σ'   σ' ⊑ σ        Γ ⊢ e : σ   α ∉ free(Γ)
  ─────────────────── Abs   ────────────────────── Inst  ───────────────────────── Gen
   Γ ⊢ λx:τ.e : τ→τ'              Γ ⊢ e : σ                   Γ ⊢ e : ∀α.σ
```

`Inst` and `Gen` are what make this *declarative*: neither is driven by the term, so either may be
applied anywhere, any number of times.
-/

/-- **The declarative system.** -/
inductive HasTypeD : SCtx N → Term N → Scheme → Prop where
  | var {Γ x σ} :
      Γ.get? x = some σ →
      HasTypeD Γ (.var x) σ
  | app {Γ e₀ e₁ τ τ'} :
      HasTypeD Γ e₀ (.mono (τ ⇒ τ')) →
      HasTypeD Γ e₁ (.mono τ) →
      HasTypeD Γ (.app e₀ e₁) (.mono τ')
  | abs {Γ x τ e τ'} :
      HasTypeD (Γ.cons x (.mono τ)) e (.mono τ') →
      HasTypeD Γ (.lam x τ e) (.mono (τ ⇒ τ'))
  | inst {Γ e σ σ'} :
      HasTypeD Γ e σ' →
      Scheme.Specializes σ' σ →
      HasTypeD Γ e σ
  | gen {Γ e σ α} :
      HasTypeD Γ e σ →
      ¬ SCtx.IsFree Γ α →
      HasTypeD Γ e (.all α σ)

/-! ## Against the kernel judgement

`HasType` is `D` with the scheme layer removed: monotype contexts, monotype conclusions, no
`[Inst]`, no `[Gen]`. So it embeds.
-/

/-- Every monotype context is a scheme context. -/
def SCtx.ofMono (Γ : Ctx N) : SCtx N := Γ.map fun _ τ => Scheme.mono τ

@[simp] theorem SCtx.ofMono_get? (Γ : Ctx N) (x : N) :
    (SCtx.ofMono Γ).get? x = (Γ.get? x).map Scheme.mono := by
  show (Γ.map _).get? x = _
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map,
      ← Std.HashMap.get?_eq_getElem?]

theorem SCtx.ofMono_cons_get? (Γ : Ctx N) (x : N) (τ : Ty) (y : N) :
    (SCtx.ofMono (Γ.cons x τ)).get? y = ((SCtx.ofMono Γ).cons x (Scheme.mono τ)).get? y := by
  rw [SCtx.ofMono_get?, Ctx.get?_cons, LambdaLab.Language.Context.get?_cons, SCtx.ofMono_get?]
  by_cases h : x = y <;> simp [h]

/-- `free(Γ)` is read off `get?`, so contexts that agree pointwise have the same free variables.
This is why `HasTypeD.cong` needs no side condition for `[Gen]`. -/
theorem SCtx.IsFree.congr {Γ Γ' : SCtx N} (hΓ : ∀ y, Γ.get? y = Γ'.get? y) (n : Nat) :
    SCtx.IsFree Γ n ↔ SCtx.IsFree Γ' n := by
  constructor
  · rintro ⟨x, σ, hx, hf⟩; exact ⟨x, σ, (hΓ x) ▸ hx, hf⟩
  · rintro ⟨x, σ, hx, hf⟩; exact ⟨x, σ, (hΓ x).symm ▸ hx, hf⟩

/-- `HasTypeD` only looks at the context through `get?`, so it transports along agreement. -/
theorem HasTypeD.cong {Γ Γ' : SCtx N} {e : Term N} {σ : Scheme}
    (hΓ : ∀ y, Γ.get? y = Γ'.get? y) (h : HasTypeD Γ e σ) : HasTypeD Γ' e σ := by
  induction h generalizing Γ' with
  | var hget => exact HasTypeD.var (by rw [← hΓ]; exact hget)
  | app _ _ ih₁ ih₂ => exact HasTypeD.app (ih₁ hΓ) (ih₂ hΓ)
  | abs _ ih =>
      exact HasTypeD.abs (ih (fun y => by
        rw [LambdaLab.Language.Context.get?_cons, LambdaLab.Language.Context.get?_cons, hΓ]))
  | inst _ hs ih => exact HasTypeD.inst (ih hΓ) hs
  | gen _ hα ih => exact HasTypeD.gen (ih hΓ) (fun hc => hα ((SCtx.IsFree.congr hΓ _).mpr hc))

/-- **`HasType` embeds into `D`.** The kernel judgement is the fragment with no schemes in play. -/
theorem HasType.toD {Γ : Ctx N} {e : Term N} {τ : Ty} (h : HasType Γ e τ) :
    HasTypeD (SCtx.ofMono Γ) e (.mono τ) := by
  induction h with
  | var hget => exact HasTypeD.var (by rw [SCtx.ofMono_get?, hget]; rfl)
  | lam _ ih => exact HasTypeD.abs (HasTypeD.cong (SCtx.ofMono_cons_get? _ _ _) ih)
  | app _ _ ih₁ ih₂ => exact HasTypeD.app ih₁ ih₂

/-! ## What the converse would take, and why `D` collapses here

The other direction — a `D` derivation at a monotype, over a monotype context, gives a `HasType`
derivation — is the substance of the `D`-to-`S` bridge: push every `[Inst]`/`[Gen]` down to the
leaves and show the shape can always be normalised. In Mini-ML that is a real theorem.

Here it is nearly vacuous, and the reason is worth seeing. `[Gen]` can fire, but nothing can
*consume* a `∀`: the only rule that reads a scheme out of the context is `[Var]`, and the only
rule that puts one there is `[Let]` — which this language does not have. So a scheme can be built
at the root and instantiated straight back down by `[Inst]`, and never does any work. That is
precisely the sense in which STLC has no polymorphism, and precisely why `Typing/J.lean` needs no
`inst`/`gen` machinery: with no `let`, `D` and the syntax-directed system have the same monotype
derivations.

Adding `let` to `Term` is what would make this file earn its keep — `[Let]` and `Γ̄(τ)` are where
generalisation actually happens, and `J`'s `[Let]` would then need the same `Γ̄`.
-/

end LambdaLab.Stlc.Named
