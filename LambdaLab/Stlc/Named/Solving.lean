import LambdaLab.Stlc.Named.Lang
import LambdaLab.Stlc.Named.Typing.W

/-!
# An elaborator that *solves* metavariables, built on algorithm W

`stlcElaboratable` (in `Lang.lean`) checks: the declared type must be derivable as written, so
`def id : ?0 → ?0 := λ x : ⋆ . x` is rejected — nothing tries `?0 := ⋆`. This file wires in the
one thing that does try: `Typing/W.lean`.

W is not new, but it was unreachable from the surface until now, because it was pinned at
`Ctx String` while a parsed term is a `Term VName`. It is now parametric in the name alphabet
(as are `Ctx`, `HasType` and the substitution machinery under it), so it applies directly to
what the parser produces.

## What is proved, and what is assumed

**Sound.** `W_correct` and `HasTypeW.toHasType` are both sorry-free, so a successful run yields a
genuine `HasType` derivation — see `solve_hasType` below. Nothing here rests on `W_principal`.

**Not principal.** `W_principal` is still open, so this elaborator makes *no claim* that the
substitution it finds is the most general one. It finds *a* solution and, being deterministic,
always the same one.

## Why `Elaborates` carries a stability conjunct

`ElaboratableLanguage.quote_elaborates` requires that re-elaborating an output reproduces it —
`Abstraction.default` needs a surface form for every abstract value, and the obvious candidate
for `(t', τ')` is `(t', τ')` itself. That is the statement "W is idempotent on its own output",
which is true but *unproved*: the natural route is a completeness-of-W-on-the-ground-fragment
induction, resting on `unify_complete` (which is proved) but needing a good deal of freshness
bookkeeping.

Rather than assume it, this file **requires** it: `Elaborates` says W solves the declaration
*and* the solution is stable. A hypothetical term whose W-output were unstable simply does not
elaborate. That is conservative, never unsound, and needs no `sorry` — and it is exactly the
missing lemma, sitting where it can be discharged later by deleting the conjunct.

## Exactly what is sorry-free

Everything on the elaboration side: `#print axioms` gives `[propext, Classical.choice, Quot.sound]`
for `solve`, `solveStable`, `solveStable_idem`, `solve_hasType`, `solveCert_isSome` — and for
`W_correct` and `HasTypeW.toHasType` beneath them.

`stlcSolving` itself does **not**: it reports `sorryAx`, inherited through
`toLanguage := stlcLanguage`, whose parser rests on the assumed `stlcUnambiguous`
(`Lang.lean`). That is the *parser's* open lemma, not the elaborator's, and the same is true of
`stlcElaboratable`. Nothing here depends on `W_principal`.

In practice the conjunct always holds, because `solve` also demands the output be ground, and
nothing can substitute into a ground term or type.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Language (NameAlphabet)

-- Terms compare, given comparable names — needed to *check* that an elaboration is stable.
deriving instance DecidableEq for Term

/-- Variable names carry no type metavariables. Needed for `Ctx VName` to be substitutable. -/
instance : HasVars VName where
  isFree _ _ := False
  fresh _ := 0
  fresh_gt_free := by intro _ _ h; cases h

/-- Run W and apply what it found. `none` if the term does not type, or if a metavariable would
survive: the same no-leak policy `stlcElaboratable` takes, except that here W has had a chance to
solve them first. -/
def solve (Γ : Ctx VName) (t : Term VName) (τ : Ty) : Option (Term VName × Ty) :=
  match W Γ t τ with
  | none => none
  | some σ =>
      if (HasSubst.pSubst τ σ : Ty).Ground ∧ (HasSubst.pSubst t σ : Term VName).AnnotsGround then
        some (HasSubst.pSubst t σ, HasSubst.pSubst τ σ)
      else none

/-- **Soundness.** A successful `solve` yields a real typing derivation for the elaborated term,
in the correspondingly-substituted context. This is `W_correct` composed with
`HasTypeW.toHasType`, neither of which uses `sorry`. -/
theorem solve_hasType {Γ : Ctx VName} {t : Term VName} {τ : Ty} {p : Term VName × Ty}
    (h : solve Γ t τ = some p) :
    ∃ σ, W Γ t τ = some σ ∧ HasType (HasSubst.pSubst Γ σ) p.1 p.2 := by
  rw [solve] at h
  split at h
  · exact absurd h (by simp)
  · rename_i σ hW
    refine ⟨σ, hW, ?_⟩
    split at h
    · cases h; exact (W_correct Γ t τ σ hW).toHasType
    · exact absurd h (by simp)

/-- `solve`, restricted to the answers it reproduces when re-run on itself. See the header: this
extra check is the unproved idempotence lemma, imposed rather than assumed. -/
def solveStable (Γ : Ctx VName) (t : Term VName) (τ : Ty) : Option (Term VName × Ty) :=
  match solve Γ t τ with
  | none => none
  | some p => if solve Γ p.1 p.2 = some p then some p else none

/-- …and that check is exactly what makes the answer a fixed point, which is what
`quote_elaborates` needs. -/
theorem solveStable_idem {Γ : Ctx VName} {t : Term VName} {τ : Ty} {p : Term VName × Ty}
    (h : solveStable Γ t τ = some p) : solveStable Γ p.1 p.2 = some p := by
  rw [solveStable] at h
  split at h
  · exact absurd h (by simp)
  · rename_i q hq
    split at h
    · rename_i hst
      cases h
      simp [solveStable, hst]
    · exact absurd h (by simp)

/-! `solveStable` has to be repackaged to carry its own certificate, which is the shape
`ElaboratableLanguage.elaborate` wants. Matching on it directly would abstract it out of the
subtype's property, so the result is generalized with an equation first — `certAux` matches on a
*copy* and carries the proof that the copy is the real thing. -/

private def certAux (Γ : Ctx VName) (t : Term VName) (τ : Ty) :
    (o : Option (Term VName × Ty)) → solveStable Γ t τ = o →
    Option { p : Term VName × Ty // solveStable Γ t τ = some (p.1, p.2) }
  | none,   _ => none
  | some q, h => some ⟨q, by rw [h]⟩

/-- `solveStable`, carrying its own certificate. -/
def solveCert (Γ : Ctx VName) (t : Term VName) (τ : Ty) :
    Option { p : Term VName × Ty // solveStable Γ t τ = some (p.1, p.2) } :=
  certAux Γ t τ (solveStable Γ t τ) rfl

private theorem certAux_isSome (Γ : Ctx VName) (t : Term VName) (τ : Ty) :
    ∀ (o : Option (Term VName × Ty)) (h : solveStable Γ t τ = o),
      (certAux Γ t τ o h).isSome = o.isSome
  | none,   _ => rfl
  | some _, _ => rfl

theorem solveCert_isSome {Γ : Ctx VName} {t : Term VName} {τ : Ty}
    (h : (solveStable Γ t τ).isSome) : (solveCert Γ t τ).isSome := by
  rw [solveCert, certAux_isSome]; exact h

/-- STLC with metavariable solving. `Elaborates` is the graph of `solveStable`. -/
def stlcSolving : Language.ElaboratableLanguage where
  toLanguage := stlcLanguage
  Elaborates Γ t t' τ τ' := solveStable Γ t τ = some (t', τ')
  elaborates_unique h₁ h₂ := by
    have h := Option.some.inj (h₁.symm.trans h₂)
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  elaborate := solveCert
  elaborate_complete h := solveCert_isSome (by rw [h]; rfl)
  quote t' τ' := (t', τ')
  quote_elaborates h := by
    obtain ⟨t, τ, hst⟩ := h
    exact solveStable_idem hst

/-- Parse and elaborate a file, solving metavariables. -/
def solving (src : String) : Option String :=
  (stlcSolving.elaborateFile src).map stlcSolving.renderElaborated

/-! ## It solves the cases the checking elaborator rejects

`#eval!` for the same reason as in `Mvars.lean`: the parser's round-trip proof rests on the
assumed `stlcUnambiguous`. The elaboration below is sorry-free.
-/

-- `?0` is solved to `⋆` from the binder annotation.
#eval! solving "def id : ?0 → ?0 := λ x : ⋆ . x"
-- some "def id : ⋆ → ⋆ := λ x : ⋆ . x"

-- Two independent metavariables, both solved.
#eval! solving "def id : ?0 → ?1 := λ x : ⋆ . x"
-- some "def id : ⋆ → ⋆ := λ x : ⋆ . x"

-- A metavariable standing for a whole function type.
#eval! solving "def const : ⋆ → ?0 := λ x : ⋆ . ( λ y : ⋆ . x )"
-- some "def const : ⋆ → ( ⋆ → ⋆ ) := …"

-- Ground declarations are unaffected.
#eval! solving "def id : ⋆ → ⋆ := λ x : ⋆ . x"

-- Still rejected, and rightly: nothing determines `?0`, so a metavariable would survive.
#eval! solving "def poly : ?0 → ?0 := λ x : ?0 . x"      -- none

-- Genuine type errors are still errors.
#eval! solving "def bad : ⋆ → ⋆ := λ x : ⋆ . ( λ y : ⋆ . y )"   -- none

-- Solving happens per declaration, and the *solved* type enters the context, so `useId`
-- resolves `id` at `⋆ → ⋆` even though it was declared with a metavariable.
#eval! solving "def id : ?0 → ?0 := λ x : ⋆ . x   def useId : ?1 := id"
-- some "def id : ⋆ → ⋆ := λ x : ⋆ . x def useId : ⋆ → ⋆ := id"

end LambdaLab.Stlc.Named
