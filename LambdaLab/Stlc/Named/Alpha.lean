import LambdaLab.Stlc.Named.Typing.Properties
import LambdaLab.Stlc.Named.Translation
import LambdaLab.TypeSystem.Named.Basic

/-!
# α-equality for the named STLC

`TypeSystem.Named.HasAlphaEq` asks a language when two of its terms are the same term. This is
STLC's answer, and it is not a new development: **two named terms are α-equal exactly when their de
Bruijn erasures agree**, and the erasure with all of its lemmas is already here in
`Translation.lean`. `Translation.lean`'s own header says as much — "the translation collapses
α-equivalent named terms onto the same de Bruijn term" — so this file is that sentence, made into a
definition and handed to the interface.

## The definition, and the free-variable conjunct

```lean
t ≈α u  :=  t.freeVars = u.freeVars ∧ t.toDB t.freeVars = u.toDB u.freeVars
```

The second half is the erasure comparison. The first half is there because `toDB` is only faithful
on a context that covers the free variables: `lookupVar x [] = 0` for *every* `x`, so `toDB []`
sends `var x` and `var y` alike to `var 0` and would identify two distinct free variables. Pinning
the context to the terms' own free variables is what keeps the comparison honest, and the two
contexts are the same list precisely because the first conjunct says so.

Requiring the free variables to agree **as lists** — order and multiplicity — looks stronger than
it is. α-renaming touches binders only; it never adds, drops or reorders a free occurrence, so
genuinely α-equal terms have literally equal `freeVars`. Nothing is excluded by asking for it, and
two things are gained: the whole `HasAlphaEq` law bundle becomes three `rfl`-shaped lines, and
`freeVars_eq` below — the first congruence anyone wants — is `And.left`.

## Why not quantify over every context

`∀ Γ, t.toDB Γ = u.toDB Γ` is the tidier-looking definition and its laws are equally trivial. It
was rejected for one reason: it is a `∀` over `List N`, so it is not decidable, and the `decide`
examples at the bottom of this file are the cheapest evidence available that the definition is the
intended relation rather than merely *an* equivalence. Fixing the context to `freeVars` keeps the
statement a decidable conjunction of two equalities.

## What is checked here, and what is not

`alphaEq_lam_rename` is the characterisation that matters: renaming a binder to a name fresh for
the body gives an α-equal term. Without it "this is an equivalence relation" would be worth very
little — `fun _ _ => True` is an equivalence relation too. It is proved from `toDB_rename`, which
`Translation.lean` already had for the substitution proof.

Not here: that `≈α` is a congruence for `HasType` and for `⟶`. Both are real theorems rather than
bookkeeping, and the second needs a translation *back* from de Bruijn steps to named ones, which
this development does not have — `Step.toDB_step` goes one way only.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N]

/-! ## The relation -/

/-- **α-equality**: the same free variables, and the same de Bruijn erasure over them. -/
def Term.AlphaEq (t u : Term N) : Prop :=
  t.freeVars = u.freeVars ∧ t.toDB t.freeVars = u.toDB u.freeVars

/-! ### The equivalence laws

Each is a pair of `Eq` moves on the two conjuncts — the payoff of defining `≈α` as agreement of two
functions rather than as an inductive relation, where transitivity is the hard case. -/

theorem Term.AlphaEq.refl (t : Term N) : t.AlphaEq t := ⟨rfl, rfl⟩

theorem Term.AlphaEq.symm {t u : Term N} (h : t.AlphaEq u) : u.AlphaEq t :=
  ⟨h.1.symm, h.2.symm⟩

theorem Term.AlphaEq.trans {t u v : Term N} (h₁ : t.AlphaEq u) (h₂ : u.AlphaEq v) : t.AlphaEq v :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- **The first congruence, for free**: α-equal terms have the same free variables, on the nose.
It is a conjunct of the definition rather than a theorem about it — see the header for why that
costs nothing. -/
theorem Term.AlphaEq.freeVars_eq {t u : Term N} (h : t.AlphaEq u) : t.freeVars = u.freeVars := h.1

/-- Both erasures may be read at either term's free variables, the two lists being equal. -/
theorem Term.AlphaEq.toDB_eq {t u : Term N} (h : t.AlphaEq u) :
    t.toDB t.freeVars = u.toDB t.freeVars := by
  rw [h.2, h.1]

/-! ## The instance

Beside the definition, as `instHasType` sits beside the judgement and `instStep` beside `Step`, so
that `≈α` reads at the relation's own file onwards. -/

instance instHasAlphaEq : TypeSystem.Named.HasAlphaEq (Term N) where
  AlphaEq := Term.AlphaEq
  refl := Term.AlphaEq.refl
  symm := Term.AlphaEq.symm
  trans := Term.AlphaEq.trans

/-- The class relation is the definition, definitionally — so a lemma proved about either applies
to both, and a `≈α` goal may be attacked with `Term.AlphaEq`'s own lemmas. -/
@[simp] theorem alphaEq_eq :
    (TypeSystem.Named.HasAlphaEq.AlphaEq : Term N → Term N → Prop) = Term.AlphaEq := rfl

/-! ## Decidability

Two equations, one on `List N` and one on `Stlc.DeBruijn.Term`. `Atom` supplies the first through
`decEq`; the second is why `DeBruijn.Term` derives `DecidableEq`. -/

instance (t u : Term N) : Decidable (t.AlphaEq u) := by
  unfold Term.AlphaEq; infer_instance

/-! ## The characterisation: renaming a binder

The reason to believe this relation is α-equality and not merely some equivalence. `toDB_rename`
does the work; the free-variable half is the calculation that filtering the renamed binder out of
the renamed body gives back what filtering the original binder out of the original body gave. -/

/-! Two list steps, proved locally rather than imported: this file is inside the executables'
import cone, where Mathlib is not available (`Parser/Numeral.lean` records what one import costs).
Both are three-line inductions. -/

private theorem map_filter_of_forall {α : Type} (f : α → α) (p : α → Bool) :
    ∀ (l : List α), (∀ w ∈ l, p (f w) = p w) →
      (l.map f).filter p = (l.filter p).map f := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
      intro h
      have ha : p (f a) = p a := h a List.mem_cons_self
      have ihs := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
      simp only [List.map_cons, List.filter_cons, ha]
      by_cases hp : p a <;> simp [hp, ihs]

private theorem map_eq_self_of_forall {α : Type} (f : α → α) :
    ∀ (l : List α), (∀ w ∈ l, f w = w) → l.map f = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
      intro h
      simp [h a List.mem_cons_self, ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]

/-- Renaming `x` to a name fresh for the term commutes with taking free variables: every free `x`
becomes `z`, and everything else stays put. -/
theorem Term.freeVars_rename (e : Term N) (x z : N) (hz : z ∉ e.allVars) :
    (e.rename x z).freeVars = e.freeVars.map (fun w => if w = x then z else w) := by
  induction e with
  | var w => by_cases h : w = x <;> simp [Term.rename, Term.freeVars, h]
  | lam u τ inner ih =>
      simp only [Term.allVars, List.mem_cons, not_or] at hz
      obtain ⟨hzu, hzi⟩ := hz
      by_cases hux : u = x
      · -- the binder *is* `x`: `rename` stops, and the filter has already removed every `x`,
        -- so the map is the identity on what is left
        have hren : (Term.lam u τ inner).rename x z = Term.lam u τ inner := by
          simp [Term.rename, hux]
        rw [hren]
        refine (map_eq_self_of_forall _ _ (fun w hw => ?_)).symm
        simp only [Term.freeVars, List.mem_filter, decide_eq_true_eq, ne_eq] at hw
        simp [hux ▸ hw.2]
      · have hren : (Term.lam u τ inner).rename x z = Term.lam u τ (inner.rename x z) := by
          simp [Term.rename, hux]
        rw [hren]
        simp only [Term.freeVars, ih hzi]
        refine map_filter_of_forall _ _ _ (fun w _ => ?_)
        by_cases h : w = x
        · have h1 : ¬ (z = u) := hzu
          have h2 : ¬ (x = u) := fun hh => hux hh.symm
          simp [h, h1, h2]
        · simp [h]
  | app e₁ e₂ ih₁ ih₂ =>
      simp only [Term.allVars, List.mem_append, not_or] at hz
      simp [Term.rename, Term.freeVars, ih₁ hz.1, ih₂ hz.2]

private theorem filter_map_ite {α : Type} [DecidableEq α] (x z : α) :
    ∀ (l : List α), (∀ w ∈ l, w ≠ z) →
      (l.map (fun w => if w = x then z else w)).filter (fun w => decide ¬ (w = z))
        = l.filter (fun w => decide ¬ (w = x)) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
      intro hmem
      have iha := ih (fun w hw => hmem w (List.mem_cons_of_mem _ hw))
      -- `simp` normalises the goal's predicate to `!decide (· = ·)`; bring the IH to that form
      simp only [decide_not] at iha
      by_cases hax : a = x
      · simp [hax, iha]
      · have haz : ¬ (a = z) := hmem a List.mem_cons_self
        simp [hax, haz, iha]

/-- Dropping the *new* binder from the renamed body leaves exactly what dropping the *old* one left
from the original — the free-variable half of `alphaEq_lam_rename`. -/
theorem Term.freeVars_filter_rename (e : Term N) (x z : N) (hz : z ∉ e.allVars) :
    (e.rename x z).freeVars.filter (fun w => decide ¬ (w = z))
      = e.freeVars.filter (fun w => decide ¬ (w = x)) := by
  rw [Term.freeVars_rename e x z hz]
  exact filter_map_ite x z e.freeVars
    (fun w hw hwz => hz (hwz ▸ Term.freeVars_subset_allVars e w hw))

/-- **Renaming a binder to a fresh name gives an α-equal term.** The characterisation that makes
the definition worth believing: it says `≈α` actually relates terms that differ in a bound name,
which no amount of "it is an equivalence relation" would establish.

The erasure half is `toDB_rename` at `Γ₁ = []`; the free-variable half is
`freeVars_filter_rename`. -/
theorem Term.alphaEq_lam_rename (x z : N) (τ : Ty) (body : Term N)
    (hz : z ∉ body.allVars) (hzx : z ≠ x) :
    (Term.lam x τ body).AlphaEq (Term.lam z τ (body.rename x z)) := by
  have hfv : (Term.lam x τ body).freeVars = (Term.lam z τ (body.rename x z)).freeVars := by
    simp only [Term.freeVars]
    exact (Term.freeVars_filter_rename body x z hz).symm
  refine ⟨hfv, ?_⟩
  simp only [Term.toDB]
  rw [← hfv]
  exact congrArg _ (Term.toDB_rename body [] _ x z hz hzx (by simp) (by simp))

/-! ## α-equality is compatible with the judgement

`TypeSystem.Named.LawfulAlphaEq` demands that α-equal terms type alike, and without that law the
`≈α` in `Confluent` would constrain nothing. It is a short trip through the translation, because
that is where α-equality was defined: erase both terms over a context covering their (shared) free
variables, note that the erasures are the same de Bruijn term, and read the typing back. -/

/-- **α-equal terms have the same types.** `HasType.toDB` out, `HasType.fromDB` back, and the two
meet because `≈α` says the erasures agree. -/
theorem Term.AlphaEq.hasType {Γ : Ctx N} {t u : Term N} {τ : Ty}
    (h : t.AlphaEq u) (ht : HasType Γ t τ) : HasType Γ u τ := by
  have hcompat := CtxCompat.fromCtx Γ t.freeVars (fun x hx => HasType.freeVars_in_ctx t ht x hx)
  have hdb := HasType.toDB t ht t.freeVars (Ctx.toDB Γ t.freeVars) (fun _ hx => hx) hcompat
  rw [h.toDB_eq] at hdb
  have hu : ∀ x ∈ u.freeVars, x ∈ t.freeVars := fun x hx => h.1 ▸ hx
  simpa using HasType.fromDB u t.freeVars (Ctx.toDB Γ t.freeVars) τ.toDB hu hcompat hdb

/-- …in both directions, `≈α` being symmetric. -/
theorem Term.AlphaEq.hasType_iff {Γ : Ctx N} {t u : Term N} {τ : Ty} (h : t.AlphaEq u) :
    HasType Γ t τ ↔ HasType Γ u τ :=
  ⟨h.hasType, h.symm.hasType⟩

/-! ## It computes

`≈α` is decidable, so the cases that matter can simply be run. These are the evidence that the
definition relates what it should and separates what it should — cheap to write, and they fail
loudly if the definition ever drifts. -/

namespace AlphaExamples

open LambdaLab.Stlc.Named

private def x : String := "x"
private def y : String := "y"
private def z : String := "z"

/-- Bound names do not matter: `λx:⋆. x  ≈α  λy:⋆. y`. -/
example : (Term.lam x .base (.var x)).AlphaEq (Term.lam y .base (.var y)) := by decide

/-- Free names do: `x ≉α y`. -/
example : ¬ (Term.var x : Term String).AlphaEq (Term.var y) := by decide

/-- A free occurrence is not captured by renaming the binder:
`λx:⋆. z  ≈α  λy:⋆. z`, both leaving `z` free. -/
example : (Term.lam x .base (.var z)).AlphaEq (Term.lam y .base (.var z)) := by decide

/-- …but binding the free one is a different term: `λx:⋆. z ≉α λz:⋆. z`. -/
example : ¬ (Term.lam x .base (.var z)).AlphaEq (Term.lam z .base (.var z)) := by decide

/-- The annotation is part of the term, not something α forgets. -/
example : ¬ (Term.lam x .base (.var x)).AlphaEq (Term.lam y (.base ⇒ .base) (.var y)) := by decide

/-- Nesting, with shadowing: `λx.λy. x y  ≈α  λy.λx. y x`. -/
example :
    (Term.lam x .base (.lam y .base (.app (.var x) (.var y)))).AlphaEq
      (Term.lam y .base (.lam x .base (.app (.var y) (.var x)))) := by decide

/-- The inner binder shadows: `λx.λx. x  ≈α  λy.λz. z`, and *not* `λy.λz. y`. -/
example :
    (Term.lam x .base (.lam x .base (.var x))).AlphaEq
      (Term.lam y .base (.lam z .base (.var z))) := by decide

example :
    ¬ (Term.lam x .base (.lam x .base (.var x))).AlphaEq
        (Term.lam y .base (.lam z .base (.var y))) := by decide

/-- The general characterisation, at a concrete instance. -/
example : (Term.lam x .base (.var x)).AlphaEq (Term.lam y .base ((Term.var x).rename x y)) :=
  Term.alphaEq_lam_rename x y .base (.var x) (by decide) (by decide)

end AlphaExamples

end LambdaLab.Stlc.Named
