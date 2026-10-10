import LambdaLab.Nominal.Instances
import LambdaLab.Stlc.Named.Typing.Basic
import LambdaLab.Stlc.Named.Typing.Unification
import LambdaLab.Stlc.Named.Typing.Properties

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
  puts a scheme into the context, which is why let-polymorphism is the whole point of HM. It does
  **not** follow that `D` collapses onto the kernel judgement without it — an earlier version of
  this note claimed exactly that, and the end of the file records why it is wrong: `[Inst]` consumes
  a `∀` on the *conclusion*, needing no context entry at all.
* **`[Abs]` takes the binder type as given.** The article's `λx.e` leaves the parameter type to the
  rule; ours is written in the term. So `abs` below is the article's, restricted to the annotation
  the source supplies — which is exactly why `J` draws no fresh variable there.

Metavariables (`Ty.mvar`) serve as the type variables `α`. In `D` they are genuinely *bound* by
`∀`; in `W`/`J` they are *unification* variables. Same syntax, different role — and the reason
`?n` is an opaque atom for the plain `HasType`, which has no rule mentioning `Ty.mvar` at all.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N]

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
abbrev SCtx (N : Type) [Atom N] : Type := TypeSystem.Named.Context N Scheme

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

/-! ## Generalisation: `Γ̄(τ)`

`Γ̄(τ) = ∀ α̂ . τ` with `α̂ = free(τ) − free(Γ)` — quantify everything free in the type that the
context does not already pin down. It is what `[Let]` uses in the syntactical system, and what the
weakened `D`-to-`S` bridge applies at the end to recover a scheme.

Computing it needs both `IsFree` predicates decidably, and needs `free(τ)` *enumerated* rather than
merely decided. The bound is `freshIdx τ`, which the unifier already provides.
-/

def Scheme.freeB : Scheme → Nat → Bool
  | .mono τ,  n => Signature.occurs n τ
  | .all α σ, n => (! (n == α)) && Scheme.freeB σ n

@[simp] theorem Scheme.freeB_iff : ∀ (σ : Scheme) (n : Nat),
    Scheme.freeB σ n = true ↔ Scheme.IsFree σ n
  | .mono τ,  n => Iff.rfl
  | .all α σ, n => by
      simp only [Scheme.freeB, Scheme.IsFree, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true, beq_eq_false_iff_ne, ne_eq]
      rw [Scheme.freeB_iff σ n]

def SCtx.freeB (Γ : SCtx N) (n : Nat) : Bool :=
  Γ.toList.any fun p => Scheme.freeB p.2 n

theorem SCtx.freeB_iff (Γ : SCtx N) (n : Nat) :
    SCtx.freeB Γ n = true ↔ SCtx.IsFree Γ n := by
  constructor
  · intro h
    rw [SCtx.freeB, List.any_eq_true] at h
    obtain ⟨p, hp, hf⟩ := h
    refine ⟨p.1, p.2, ?_, (Scheme.freeB_iff _ _).mp hf⟩
    rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.mem_toList_iff_getElem?_eq_some]
    exact hp
  · rintro ⟨x, σ, hx, hf⟩
    rw [SCtx.freeB, List.any_eq_true]
    refine ⟨(x, σ), ?_, (Scheme.freeB_iff _ _).mpr hf⟩
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact hx

/-- The variables to quantify: `free(τ) − free(Γ)`, enumerated below `fresh τ`. -/
def SCtx.quantified (Γ : SCtx N) (τ : Ty) : List Nat :=
  (List.range (freshIdx τ)).filter fun n => Signature.occurs n τ && !SCtx.freeB Γ n

/-- **`Γ̄(τ) = ∀ α̂ . τ`, `α̂ = free(τ) − free(Γ)`** — the closure operator. -/
def SCtx.close (Γ : SCtx N) (τ : Ty) : Scheme :=
  (SCtx.quantified Γ τ).foldr Scheme.all (.mono τ)

/-- One `[Gen]` per quantified variable. -/
theorem HasTypeD.gen_foldr (Γ : SCtx N) (e : Term N) (τ : Ty) :
    ∀ (l : List Nat), (∀ α ∈ l, ¬ SCtx.IsFree Γ α) →
      HasTypeD Γ e (.mono τ) → HasTypeD Γ e (l.foldr Scheme.all (.mono τ))
  | [],      _,  h => h
  | a :: as, hl, h =>
      HasTypeD.gen
        (HasTypeD.gen_foldr Γ e τ as (fun α hα => hl α (List.mem_cons_of_mem _ hα)) h)
        (hl a List.mem_cons_self)

/-- **The closure is derivable.** `Γ̄(τ)` is reachable from `τ` by iterated `[Gen]`, which is what
lets the weakened `D`-to-`S` bridge recover a scheme by one final generalisation. -/
theorem HasTypeD.close (Γ : SCtx N) (e : Term N) (τ : Ty) (h : HasTypeD Γ e (.mono τ)) :
    HasTypeD Γ e (SCtx.close Γ τ) := by
  refine HasTypeD.gen_foldr Γ e τ _ (fun α hα => ?_) h
  rw [SCtx.quantified, List.mem_filter] at hα
  intro hc
  have : SCtx.freeB Γ α = true := (SCtx.freeB_iff Γ α).mpr hc
  simp [this] at hα

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
  rw [SCtx.ofMono_get?, Ctx.get?_cons, TypeSystem.Named.Context.get?_cons, SCtx.ofMono_get?]
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
        rw [TypeSystem.Named.Context.get?_cons, TypeSystem.Named.Context.get?_cons, hΓ]))
  | inst _ hs ih => exact HasTypeD.inst (ih hΓ) hs
  | gen _ hα ih => exact HasTypeD.gen (ih hΓ) (fun hc => hα ((SCtx.IsFree.congr hΓ _).mpr hc))

/-- **`HasType` embeds into `D`.** The kernel judgement is the fragment with no schemes in play. -/
theorem HasType.toD {Γ : Ctx N} {e : Term N} {τ : Ty} (h : HasType Γ e τ) :
    HasTypeD (SCtx.ofMono Γ) e (.mono τ) := by
  induction h with
  | var hget => exact HasTypeD.var (by rw [SCtx.ofMono_get?, hget]; rfl)
  | lam _ ih => exact HasTypeD.abs (HasTypeD.cong (SCtx.ofMono_cons_get? _ _ _) ih)
  | app _ _ ih₁ ih₂ => exact HasTypeD.app ih₁ ih₂

/-! ### It computes

Over the empty context everything free in the type is quantified — `Γ̄(?0 ⇒ ?0) = ∀0. ?0 ⇒ ?0`. A
context that already mentions a variable pins it, and only the rest generalise: under `y : ?0`,
`Γ̄(?0 ⇒ ?1) = ∀1. ?0 ⇒ ?1`.

## The converse fails, and precisely as the standard account says

One might hope for the converse: a `D` derivation whose scheme instantiates to `τ` gives
`HasType Γ e τ`. It does not, and the reason is the one the standard development gives for `S`
being incomplete — there one cannot derive `λx.x : ∀α.α→α`, only `λx.x : α→α`.

Here the same gap appears one step earlier, because `[Gen]` is available but the *annotation*
pins the binder. `λ x : ?0 . x` has exactly one `HasType` type, `?0 ⇒ ?0`. But `[Gen]` may quantify
`?0` — it is not free in the empty context — giving `∀0. ?0 ⇒ ?0`, and *that* instantiates to
`⋆ ⇒ ⋆`, which the term does not have.
-/

/-- `λ x : ?0 . x`, whose only `HasType` type is `?0 ⇒ ?0`. -/
def polyId : Term String := .lam "x" (Ty.mvar 0) (.var "x")

/-- …and the scheme `D` can nevertheless derive for it. -/
def polyIdScheme : Scheme := .all 0 (.mono (Ty.mvar 0 ⇒ Ty.mvar 0))

theorem polyId_hasType : HasType Ctx.empty polyId (Ty.mvar 0 ⇒ Ty.mvar 0) :=
  HasType.lam (HasType.var (by rw [Ctx.get?_cons]; simp))

theorem polyId_not_base : ¬ HasType (Ctx.empty : Ctx String) polyId (Ty.base ⇒ Ty.base) := by
  intro h
  exact absurd (HasType.det h polyId_hasType) (by decide)

theorem polyIdScheme_inst : Scheme.Instantiates polyIdScheme (Ty.base ⇒ Ty.base) := by
  refine Scheme.Instantiates.all (τ₀ := Ty.base) ?_
  have hsub : Scheme.instAt (.mono (Ty.mvar 0 ⇒ Ty.mvar 0)) 0 Ty.base
            = .mono (Ty.base ⇒ Ty.base) := by
    show Scheme.mono (HasSubst.pSubst (Ty.mvar 0 ⇒ Ty.mvar 0)
          ((∅ : Subst Nat Ty).insert 0 Ty.base)) = _
    rw [Ty.pSubst_arrow, Ty.pSubst_mvar, Std.HashMap.getD_insert]
    simp
  rw [hsub]
  exact Scheme.Instantiates.mono

theorem polyId_hasTypeD :
    HasTypeD (SCtx.ofMono (Ctx.empty : Ctx String)) polyId polyIdScheme :=
  HasTypeD.gen (HasType.toD polyId_hasType) (by
    rintro ⟨x, σ, hx, -⟩
    rw [SCtx.ofMono_get?, Ctx.get?_empty] at hx
    exact absurd hx (by simp))

-- The scheme above is not ad hoc: it is `SCtx.close (SCtx.ofMono Ctx.empty) (?0 ⇒ ?0)`, i.e. `Γ̄`
-- of the identity's type over the empty context — the *canonical* generalisation. So the
-- counterexample is not an artefact of picking a strange scheme; it is what `[Let]` would have
-- produced. (Not stated as a theorem: `close` runs through a `HashMap`, so `decide` sticks.)

/-- **The naive converse of `HasType.toD` is false.** Instantiating a `D`-derivable scheme does not
give a `HasType` derivation, so `D` is strictly stronger than the kernel judgement even here.

The literature's *weakened* statement — `Γ ⊢_D e:σ ⟹ Γ ⊢_S e:τ ∧ Γ̄(τ) ⊑ σ`, recovering the scheme
by one final generalisation — does not rescue it here either: `Typing/S.lean` refutes that too
(`HasTypeD.stronger_than_hasType`), because our `[Abs]` cannot re-choose an annotation the way the
article's can. `Γ̄` is `SCtx.close` above and `HasTypeD.close` supplies the generalisation half; the
`S` side is not merely unproved, it is false. -/
theorem HasTypeD.instance_not_sound :
    ¬ ∀ (Γ : Ctx String) (e : Term String) (σ : Scheme) (τ : Ty),
        HasTypeD (SCtx.ofMono Γ) e σ → Scheme.Instantiates σ τ → HasType Γ e τ := fun h =>
  polyId_not_base
    (h Ctx.empty polyId polyIdScheme (Ty.base ⇒ Ty.base) polyId_hasTypeD polyIdScheme_inst)

/-! ## `D` is strictly stronger — it types terms the kernel judgement rejects

An earlier version of this note claimed the extra schemes were unreachable: `[Gen]` can fire, but
nothing can *consume* a `∀`, since the only rule reading a scheme from the context is `[Var]` and
the only rule putting one there is `[Let]`, which this language lacks.

That is wrong. `[Inst]` consumes a `∀` on the **conclusion**, with no context involved at all. So
`[Gen]` followed by `[Inst]` lets `D` re-choose the type of a written annotation, which the kernel
judgement can never do. `Typing/S.lean` carries the counterexample
(`HasTypeD.stronger_than_hasType`): with `a : ⋆`, the term `(λ x : ?0 . x) a` has no `HasType`
derivation, yet `D` gives it `⋆`.

So `HasType.toD` is a strict embedding, and the reverse bridge fails even in the weakened form the
literature uses. What remains true is the narrower statement actually proved here: `S` — hence
`HasType` — coincides with `D` only after `[Inst]`/`[Gen]` are removed, which is what `S` does.

`[Let]` and `Γ̄(τ)` are still where generalisation is *meant* to happen; adding `let` to `Term` is
what would make this file earn its keep.
-/

end LambdaLab.Stlc.Named
