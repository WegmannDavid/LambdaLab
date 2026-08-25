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

That `≈α` is a congruence for `HasType` is here (`Term.AlphaEq.hasType`), and so is the machinery
for reduction: `Term.step_reflect` supplies the direction `Translation.lean` never needed, lifting a
de Bruijn step back to a named one. With it, `Stlc/Named/TypeSystem.lean` discharges `Confluent`.

Not here: the congruence itself, `t ≈α u → t ⟶ t' → ∃ u', u ⟶* u' ∧ t' ≈α u'`. It is now within
reach rather than blocked — `step_reflect` is the piece it was waiting on — but it is not a field of
`LawfulAlphaEq` and nothing yet asks for it.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N]

/-! ## The relation -/

/-- **α-equality**: the same free variables, and the same de Bruijn erasure under every context
that covers them. -/
def Term.AlphaEq (t u : Term N) : Prop :=
  t.freeVars = u.freeVars ∧
  ∀ Γ : List N, (∀ x ∈ t.freeVars, x ∈ Γ) → t.toDB Γ = u.toDB Γ

/-! ### The equivalence laws

Each is a pair of `Eq` moves on the two conjuncts — the payoff of defining `≈α` as agreement of two
functions rather than as an inductive relation, where transitivity is the hard case. -/

theorem Term.AlphaEq.refl (t : Term N) : t.AlphaEq t := ⟨rfl, fun _ _ => rfl⟩

theorem Term.AlphaEq.symm {t u : Term N} (h : t.AlphaEq u) : u.AlphaEq t :=
  ⟨h.1.symm, fun Γ hΓ => (h.2 Γ (fun x hx => hΓ x (h.1 ▸ hx))).symm⟩

theorem Term.AlphaEq.trans {t u v : Term N} (h₁ : t.AlphaEq u) (h₂ : u.AlphaEq v) : t.AlphaEq v :=
  ⟨h₁.1.trans h₂.1,
   fun Γ hΓ => (h₁.2 Γ hΓ).trans (h₂.2 Γ (fun x hx => hΓ x (h₁.1 ▸ hx)))⟩

/-- **The first congruence, for free**: α-equal terms have the same free variables, on the nose.
It is a conjunct of the definition rather than a theorem about it — see the header for why that
costs nothing. -/
theorem Term.AlphaEq.freeVars_eq {t u : Term N} (h : t.AlphaEq u) : t.freeVars = u.freeVars := h.1

/-- The erasures agree at the terms' own free variables — the smallest adequate context, and the
one `typing_respects` runs at. -/
theorem Term.AlphaEq.toDB_eq {t u : Term N} (h : t.AlphaEq u) :
    t.toDB t.freeVars = u.toDB t.freeVars :=
  h.2 t.freeVars (fun _ hx => hx)

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
  refine ⟨hfv, fun Γ _ => ?_⟩
  simp only [Term.toDB]
  exact congrArg _ (Term.toDB_rename body [] Γ x z hz hzx (by simp) (by simp))

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

/-! ## Faithfulness: the erasure determines the free variables

The brick everything below needs. Confluence hands back a common *de Bruijn* term, so recovering
`≈α` from it means recovering both conjuncts, and the free-variable one is not obvious: two named
terms with equal erasures could a priori have different free variables.

They cannot, and the proof is the standard two-stack induction. It has to be: the `lam` case
compares `b` under `x :: Γ` with `b'` under `y :: Γ`, so a statement fixed at *one* context cannot
carry it. `Δ₁`/`Δ₂` are the binders passed so far on each side — equal in length, arbitrary in
content — and the conclusion is about the variables that escape them. -/

/-- `lookupVar` is injective on names the context actually contains: an index names one binder. -/
theorem lookupVar_inj {x y : N} : ∀ {Γ : List N},
    x ∈ Γ → y ∈ Γ → lookupVar x Γ = lookupVar y Γ → x = y := by
  intro Γ
  induction Γ with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons a as ih =>
      intro hx hy heq
      simp only [lookupVar] at heq
      by_cases hax : a = x <;> by_cases hay : a = y
      · exact hax ▸ hay ▸ rfl
      · subst hax; simp [hay] at heq
      · subst hay; simp [hax] at heq
      · simp only [hax, hay, if_false, Nat.add_right_cancel_iff] at heq
        refine ih ?_ ?_ heq
        · rcases List.mem_cons.mp hx with h | h
          · exact absurd h.symm hax
          · exact h
        · rcases List.mem_cons.mp hy with h | h
          · exact absurd h.symm hay
          · exact h

/-- A name in the near stack indexes inside it; a name outside indexes past it. Together these are
what let the induction tell "bound on both sides" from "free on both sides". -/
theorem lookupVar_lt_of_mem {x : N} {Δ Γ : List N} (h : x ∈ Δ) :
    lookupVar x (Δ ++ Γ) < Δ.length := by
  rw [lookupVar_append_left x Δ Γ h]; exact lookupVar_lt_length x Δ h

theorem lookupVar_ge_of_not_mem {x : N} {Δ Γ : List N} (h : x ∉ Δ) :
    Δ.length ≤ lookupVar x (Δ ++ Γ) := by
  rw [lookupVar_append_right x Δ Γ h]; omega

private theorem filter_all {α : Type} : ∀ (l : List α), l.filter (fun _ => true) = l := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- Peeling one binder off the stack: filtering out `a :: Δ` is filtering out `a`, then `Δ`. The
step the `lam` case takes, kept separate so that case stays two lines. -/
private theorem filter_notMem_cons {α : Type} [DecidableEq α] (a : α) (Δ : List α) :
    ∀ (l : List α), l.filter (fun w => decide (w ∉ a :: Δ))
      = (l.filter (fun w => decide ¬ (w = a))).filter (fun w => decide (w ∉ Δ)) := by
  intro l
  induction l with
  | nil => rfl
  | cons c cs ih =>
      by_cases h1 : c = a
      · simp [List.mem_cons, h1, Bool.and_comm]
      · by_cases h2 : c ∈ Δ
        · simp [List.mem_cons, h1, h2, Bool.and_comm]
        · simp [List.mem_cons, h1, h2, Bool.and_comm]

/-- **The erasure determines the free variables**, relative to the binders passed so far. -/
theorem Term.freeVars_eq_of_toDB :
    ∀ (t u : Term N) (Δ₁ Δ₂ Γ : List N),
      Δ₁.length = Δ₂.length →
      (∀ w ∈ t.freeVars, w ∈ Δ₁ ++ Γ) →
      (∀ w ∈ u.freeVars, w ∈ Δ₂ ++ Γ) →
      t.toDB (Δ₁ ++ Γ) = u.toDB (Δ₂ ++ Γ) →
      t.freeVars.filter (fun w => decide (w ∉ Δ₁))
        = u.freeVars.filter (fun w => decide (w ∉ Δ₂)) := by
  intro t
  induction t with
  | var w =>
      intro u Δ₁ Δ₂ Γ hlen ht hu heq
      cases u with
      | var v =>
          simp only [Term.toDB, Stlc.DeBruijn.Term.var.injEq] at heq
          have hw : w ∈ Δ₁ ++ Γ := ht w (by simp [Term.freeVars])
          have hv : v ∈ Δ₂ ++ Γ := hu v (by simp [Term.freeVars])
          by_cases hwΔ : w ∈ Δ₁
          · by_cases hvΔ : v ∈ Δ₂
            · simp [Term.freeVars, hwΔ, hvΔ]
            · exact absurd heq (by
                have h1 := lookupVar_lt_of_mem (Δ := Δ₁) (Γ := Γ) hwΔ
                have h2 := lookupVar_ge_of_not_mem (Δ := Δ₂) (Γ := Γ) hvΔ
                omega)
          · by_cases hvΔ' : v ∈ Δ₂
            · exact absurd heq (by
                have h1 := lookupVar_ge_of_not_mem (Δ := Δ₁) (Γ := Γ) hwΔ
                have h2 := lookupVar_lt_of_mem (Δ := Δ₂) (Γ := Γ) hvΔ'
                omega)
            · rw [lookupVar_append_right w Δ₁ Γ hwΔ,
                  lookupVar_append_right v Δ₂ Γ hvΔ'] at heq
              have hwΓ : w ∈ Γ := by
                rcases List.mem_append.mp hw with h | h
                · exact absurd h hwΔ
                · exact h
              have hvΓ : v ∈ Γ := by
                rcases List.mem_append.mp hv with h | h
                · exact absurd h hvΔ'
                · exact h
              have hwv : w = v := lookupVar_inj hwΓ hvΓ (by omega)
              subst hwv
              simp [Term.freeVars, hwΔ, hvΔ']
      | lam _ _ _ => simp [Term.toDB] at heq
      | app _ _ => simp [Term.toDB] at heq
  | lam x τ b ih =>
      intro u Δ₁ Δ₂ Γ hlen ht hu heq
      cases u with
      | var _ => simp [Term.toDB] at heq
      | app _ _ => simp [Term.toDB] at heq
      | lam y τ' b' =>
          simp only [Term.toDB, Stlc.DeBruijn.Term.lam.injEq] at heq
          have hb := ih b' (x :: Δ₁) (y :: Δ₂) Γ (by simpa using hlen)
            (fun w hw => by
              by_cases hwx : w = x
              · simp [hwx]
              · exact List.mem_cons_of_mem _
                  (ht w (by simp [Term.freeVars, List.mem_filter, hw, hwx])))
            (fun w hw => by
              by_cases hwy : w = y
              · simp [hwy]
              · exact List.mem_cons_of_mem _
                  (hu w (by simp [Term.freeVars, List.mem_filter, hw, hwy])))
            heq.2
          simp only [Term.freeVars]
          rw [← filter_notMem_cons x Δ₁, ← filter_notMem_cons y Δ₂]
          exact hb
  | app e₁ e₂ ih₁ ih₂ =>
      intro u Δ₁ Δ₂ Γ hlen ht hu heq
      cases u with
      | var _ => simp [Term.toDB] at heq
      | lam _ _ _ => simp [Term.toDB] at heq
      | app f₁ f₂ =>
          simp only [Term.toDB, Stlc.DeBruijn.Term.app.injEq] at heq
          simp only [Term.freeVars, List.filter_append]
          rw [ih₁ f₁ Δ₁ Δ₂ Γ hlen
                (fun w hw => ht w (by simp [Term.freeVars, hw]))
                (fun w hw => hu w (by simp [Term.freeVars, hw])) heq.1,
              ih₂ f₂ Δ₁ Δ₂ Γ hlen
                (fun w hw => ht w (by simp [Term.freeVars, hw]))
                (fun w hw => hu w (by simp [Term.freeVars, hw])) heq.2]

/-- The top-level reading: equal erasures under a covering context force equal free variables. -/
theorem Term.freeVars_eq_of_toDB' {t u : Term N} {Γ : List N}
    (ht : ∀ w ∈ t.freeVars, w ∈ Γ) (hu : ∀ w ∈ u.freeVars, w ∈ Γ)
    (heq : t.toDB Γ = u.toDB Γ) : t.freeVars = u.freeVars := by
  have h := Term.freeVars_eq_of_toDB t u [] [] Γ rfl ht hu heq
  simpa [filter_all] using h

/-- **The erasure equality transports to any other context.** Faithfulness says the escaping
positions hold the *same name* on both sides; this says that is all the erasure depends on, so
swapping the outer context for another leaves the two sides still equal. No adequacy is needed of
`Γ'` — an escaping name indexes past both stacks whether or not `Γ'` contains it. -/
theorem Term.toDB_transport :
    ∀ (t u : Term N) (Δ₁ Δ₂ Γ Γ' : List N),
      Δ₁.length = Δ₂.length →
      (∀ w ∈ t.freeVars, w ∈ Δ₁ ++ Γ) →
      (∀ w ∈ u.freeVars, w ∈ Δ₂ ++ Γ) →
      t.toDB (Δ₁ ++ Γ) = u.toDB (Δ₂ ++ Γ) →
      t.toDB (Δ₁ ++ Γ') = u.toDB (Δ₂ ++ Γ') := by
  intro t
  induction t with
  | var w =>
      intro u Δ₁ Δ₂ Γ Γ' hlen ht hu heq
      cases u with
      | lam _ _ _ => simp [Term.toDB] at heq
      | app _ _ => simp [Term.toDB] at heq
      | var v =>
          simp only [Term.toDB, Stlc.DeBruijn.Term.var.injEq] at heq ⊢
          have hw : w ∈ Δ₁ ++ Γ := ht w (by simp [Term.freeVars])
          have hv : v ∈ Δ₂ ++ Γ := hu v (by simp [Term.freeVars])
          by_cases hwΔ : w ∈ Δ₁
          · by_cases hvΔ : v ∈ Δ₂
            · rw [lookupVar_append_left w Δ₁ Γ hwΔ, lookupVar_append_left v Δ₂ Γ hvΔ] at heq
              rw [lookupVar_append_left w Δ₁ Γ' hwΔ, lookupVar_append_left v Δ₂ Γ' hvΔ]
              exact heq
            · exact absurd heq (by
                have h1 := lookupVar_lt_of_mem (Δ := Δ₁) (Γ := Γ) hwΔ
                have h2 := lookupVar_ge_of_not_mem (Δ := Δ₂) (Γ := Γ) hvΔ
                omega)
          · by_cases hvΔ : v ∈ Δ₂
            · exact absurd heq (by
                have h1 := lookupVar_ge_of_not_mem (Δ := Δ₁) (Γ := Γ) hwΔ
                have h2 := lookupVar_lt_of_mem (Δ := Δ₂) (Γ := Γ) hvΔ
                omega)
            · rw [lookupVar_append_right w Δ₁ Γ hwΔ, lookupVar_append_right v Δ₂ Γ hvΔ] at heq
              have hwΓ : w ∈ Γ := by
                rcases List.mem_append.mp hw with h | h
                · exact absurd h hwΔ
                · exact h
              have hvΓ : v ∈ Γ := by
                rcases List.mem_append.mp hv with h | h
                · exact absurd h hvΔ
                · exact h
              have hwv : w = v := lookupVar_inj hwΓ hvΓ (by omega)
              subst hwv
              rw [lookupVar_append_right w Δ₁ Γ' hwΔ, lookupVar_append_right w Δ₂ Γ' hvΔ]
              omega
  | lam x τ b ih =>
      intro u Δ₁ Δ₂ Γ Γ' hlen ht hu heq
      cases u with
      | var _ => simp [Term.toDB] at heq
      | app _ _ => simp [Term.toDB] at heq
      | lam y τ' b' =>
          simp only [Term.toDB, Stlc.DeBruijn.Term.lam.injEq] at heq ⊢
          refine ⟨heq.1, ?_⟩
          exact ih b' (x :: Δ₁) (y :: Δ₂) Γ Γ' (by simpa using hlen)
            (fun w hw => by
              by_cases hwx : w = x
              · simp [hwx]
              · exact List.mem_cons_of_mem _
                  (ht w (by simp [Term.freeVars, List.mem_filter, hw, hwx])))
            (fun w hw => by
              by_cases hwy : w = y
              · simp [hwy]
              · exact List.mem_cons_of_mem _
                  (hu w (by simp [Term.freeVars, List.mem_filter, hw, hwy])))
            heq.2
  | app e₁ e₂ ih₁ ih₂ =>
      intro u Δ₁ Δ₂ Γ Γ' hlen ht hu heq
      cases u with
      | var _ => simp [Term.toDB] at heq
      | lam _ _ _ => simp [Term.toDB] at heq
      | app f₁ f₂ =>
          simp only [Term.toDB, Stlc.DeBruijn.Term.app.injEq] at heq ⊢
          exact ⟨ih₁ f₁ Δ₁ Δ₂ Γ Γ' hlen
                   (fun w hw => ht w (by simp [Term.freeVars, hw]))
                   (fun w hw => hu w (by simp [Term.freeVars, hw])) heq.1,
                 ih₂ f₂ Δ₁ Δ₂ Γ Γ' hlen
                   (fun w hw => ht w (by simp [Term.freeVars, hw]))
                   (fun w hw => hu w (by simp [Term.freeVars, hw])) heq.2⟩

/-- **Equal erasures under one covering context give α-equality.** The two halves above, packaged:
this is the intro rule everything that produces a de Bruijn fact needs, and it is exactly what
turns the confluence theorem's common de Bruijn reduct into a `≈α` claim about named terms. -/
theorem Term.alphaEq_of_toDB {t u : Term N} {Γ : List N}
    (ht : ∀ w ∈ t.freeVars, w ∈ Γ) (hu : ∀ w ∈ u.freeVars, w ∈ Γ)
    (heq : t.toDB Γ = u.toDB Γ) : t.AlphaEq u :=
  ⟨Term.freeVars_eq_of_toDB' ht hu heq,
   fun Γ' _ => Term.toDB_transport t u [] [] Γ Γ' rfl ht hu heq⟩

/-! ## Lifting a de Bruijn reduction back to a named one

The direction `Translation.lean` never needed: `Step.toDB_step` carries a named step down to de
Bruijn, and this carries a de Bruijn step back up. It is what confluence needs, because
`MStep.confluent` produces a common reduct on the *de Bruijn* side and `Confluent` asks for named
ones.

It goes through because `toDB` is shape-preserving — `var` to `var`, `lam` to `lam`, `app` to
`app` — so a redex downstairs sits exactly where one sits upstairs, and the β case is
`Term.toDB_subst` read right to left. -/

/-- **A de Bruijn step lifts.** Whatever `e`'s erasure steps to, `e` itself steps to something that
erases to it. -/
theorem Term.step_reflect :
    ∀ (e : Term N) (Γ : List N) (d : Stlc.DeBruijn.Term),
      (∀ w ∈ e.freeVars, w ∈ Γ) →
      Stlc.DeBruijn.Step (e.toDB Γ) d →
      ∃ u : Term N, Step e u ∧ u.toDB Γ = d := by
  intro e
  induction e with
  | var w => intro Γ d _ hs; simp only [Term.toDB] at hs; cases hs
  | lam x τ b ih =>
      intro Γ d hfv hs
      simp only [Term.toDB] at hs
      cases hs with
      | lam hb =>
          obtain ⟨u, hstep, herase⟩ := ih (x :: Γ) _
            (fun w hw => by
              by_cases hwx : w = x
              · simp [hwx]
              · exact List.mem_cons_of_mem _
                  (hfv w (by simp [Term.freeVars, List.mem_filter, hw, hwx])))
            hb
          exact ⟨Term.lam x τ u, Step.lam hstep, by simp [Term.toDB, herase]⟩
  | app f a ihf iha =>
      intro Γ d hfv hs
      have hff : ∀ w ∈ f.freeVars, w ∈ Γ :=
        fun w hw => hfv w (by simp [Term.freeVars, hw])
      have hfa : ∀ w ∈ a.freeVars, w ∈ Γ :=
        fun w hw => hfv w (by simp [Term.freeVars, hw])
      cases f with
      | var w =>
          simp only [Term.toDB] at hs
          cases hs with
          | appL hl => cases hl
          | appR hr =>
              obtain ⟨u, hstep, herase⟩ := iha Γ _ hfa hr
              exact ⟨Term.app (Term.var w) u, Step.appR hstep, by simp [Term.toDB, herase]⟩
      | app g h =>
          simp only [Term.toDB] at hs
          cases hs with
          | appL hl =>
              obtain ⟨u, hstep, herase⟩ := ihf Γ _ hff (by simpa [Term.toDB] using hl)
              exact ⟨Term.app u a, Step.appL hstep, by simp [Term.toDB, herase]⟩
          | appR hr =>
              obtain ⟨u, hstep, herase⟩ := iha Γ _ hfa hr
              exact ⟨Term.app (Term.app g h) u, Step.appR hstep, by simp [Term.toDB, herase]⟩
      | lam x σ fb =>
          simp only [Term.toDB] at hs
          cases hs with
          | beta =>
              refine ⟨fb.subst x a, Step.beta, ?_⟩
              have := Term.toDB_subst fb [] Γ x a (fun w hw => hfa w hw) (by simp) (by simp)
              simpa [Term.toDB, iterShift0] using this
          | appL hl =>
              obtain ⟨u, hstep, herase⟩ := ihf Γ _ hff (by simpa [Term.toDB] using hl)
              exact ⟨Term.app u a, Step.appL hstep, by simp [Term.toDB, herase]⟩
          | appR hr =>
              obtain ⟨u, hstep, herase⟩ := iha Γ _ hfa hr
              exact ⟨Term.app (Term.lam x σ fb) u, Step.appR hstep, by simp [Term.toDB, herase]⟩

/-- **A de Bruijn reduction lifts.** The multi-step form, by induction from the *front* of the
chain — `RTC.head_induction_on`, since each lifted step has to be taken before the rest can be. -/
theorem Term.mstep_reflect {Γ : List N} :
    ∀ {c d : Stlc.DeBruijn.Term}, RTC Stlc.DeBruijn.Step c d →
      ∀ e : Term N, e.toDB Γ = c → (∀ w ∈ e.freeVars, w ∈ Γ) →
        ∃ u : Term N, RTC Step e u ∧ u.toDB Γ = d := by
  intro c d h
  induction h using RTC.head_induction_on with
  | refl => intro e he _; exact ⟨e, RTC.refl, he⟩
  | head hstep _ ih =>
      intro e he hfv
      obtain ⟨u₁, hs1, he1⟩ := Term.step_reflect e Γ _ hfv (he ▸ hstep)
      obtain ⟨u, hus, hue⟩ := ih u₁ he1
        (fun w hw => hfv w (Step.preserves_freeVars hs1 w hw))
      exact ⟨u, RTC.head hs1 hus, hue⟩

/-! ## The cases that matter

`≈α` is no longer decidable — its second conjunct quantifies over contexts — so these are proofs
rather than `decide` calls. They cost a line each and they are the evidence that the definition
relates what it should and separates what it should: a negative case refutes one conjunct, a
positive case computes the erasure. -/

namespace AlphaExamples

open LambdaLab.Stlc.Named

private def x : String := "x"
private def y : String := "y"
private def z : String := "z"

/-- Bound names do not matter: `λx:⋆. x  ≈α  λy:⋆. y`. -/
example : (Term.lam x .base (.var x)).AlphaEq (Term.lam y .base (.var y)) :=
  ⟨by decide, fun _ _ => by simp [Term.toDB]⟩

/-- Free names do: `x ≉α y` — they do not even have the same free variables. -/
example : ¬ (Term.var x : Term String).AlphaEq (Term.var y) :=
  fun h => absurd h.1 (by decide)

/-- A free occurrence is not captured by renaming the binder: `λx:⋆. z ≈α λy:⋆. z`. -/
example : (Term.lam x .base (.var z)).AlphaEq (Term.lam y .base (.var z)) :=
  ⟨by decide, fun _ _ => by simp [Term.toDB, lookupVar, x, y, z]⟩

/-- …but binding the free one is a different term: `λx:⋆. z ≉α λz:⋆. z`. -/
example : ¬ (Term.lam x .base (.var z)).AlphaEq (Term.lam z .base (.var z)) :=
  fun h => absurd h.1 (by decide)

/-- The annotation is part of the term, not something α forgets. Both sides are closed, so the
free-variable conjunct cannot separate them — the erasure does. -/
example : ¬ (Term.lam x .base (.var x)).AlphaEq (Term.lam y (.base ⇒ .base) (.var y)) := by
  intro h
  have := h.2 [] (by decide)
  simp [Term.toDB, Ty.toDB] at this

/-- Nesting, with the two binders swapped: `λx.λy. x y  ≈α  λy.λx. y x`. -/
example :
    (Term.lam x .base (.lam y .base (.app (.var x) (.var y)))).AlphaEq
      (Term.lam y .base (.lam x .base (.app (.var y) (.var x)))) :=
  ⟨by decide, fun _ _ => by simp [Term.toDB, lookupVar, x, y]⟩

/-- The inner binder shadows: `λx.λx. x  ≈α  λy.λz. z`. -/
example :
    (Term.lam x .base (.lam x .base (.var x))).AlphaEq
      (Term.lam y .base (.lam z .base (.var z))) :=
  ⟨by decide, fun _ _ => by simp [Term.toDB, lookupVar, x, z]⟩

/-- …and *not* `λy.λz. y`, which reaches past the shadowing binder. This is the case a definition
that mishandled shadowing would get wrong. -/
example :
    ¬ (Term.lam x .base (.lam x .base (.var x))).AlphaEq
        (Term.lam y .base (.lam z .base (.var y))) := by
  intro h
  have := h.2 [] (by decide)
  simp only [Term.toDB, lookupVar, x, y, z] at this
  exact absurd this (by decide)

/-- The general characterisation, at a concrete instance. -/
example : (Term.lam x .base (.var x)).AlphaEq (Term.lam y .base ((Term.var x).rename x y)) :=
  Term.alphaEq_lam_rename x y .base (.var x) (by decide) (by decide)

end AlphaExamples

end LambdaLab.Stlc.Named
