import LambdaLab.Stlc.Named.Solving
import LambdaLab.Stlc.Named.Typing.Target

/-!
# STLC wired to the constraint-based elaborator

`Solving.lean` wires the surface to `W`. This wires it to `Typing/Target.lean`'s `elabSubst` —
generate every constraint, then solve once — which is the same job done the other way round.

## Why this instance is sorry-free where `Target.elaborate` is not

`Target.lean` deliberately splits the computation from its proofs. `elabSubst` and
`elabSubst_sound` carry no `sorry`; only `elaborate`, which additionally bundles the open
most-generality conjunct, does. This file uses the first two, so the elaboration side is clean —
`stlcInferring` reports `sorryAx` only through `toLanguage`, i.e. the parser's assumed
`stlcUnambiguous`, exactly as the other three instances do.

What is therefore *not* claimed here: that the substitution found is the most general one. That is
`GenerationComplete` and the range invariant beside it, both still open.

## Same shape as `Solving.lean`

`Elaborates` is the graph of a stable solve, for the same reason as there:
`quote_elaborates` needs re-elaborating an output to reproduce it, which is unproved, so it is
*required* rather than assumed. The duplication between the two files is real and would come out
if the substitution-finder were made a parameter; both are kept side by side for now because
comparing them is the point.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Language (NameAlphabet)

/-- Infer, then apply — refusing to let a metavariable survive the declaration, the same no-leak
policy the other strict instances take. -/
def solveJ (Γ : Ctx VName) (t : Term VName) (τ : Ty) : Option (Term VName × Ty) :=
  match elabSubst Γ t τ with
  | none => none
  | some σ =>
      if (HasSubst.pSubst τ σ : Ty).Ground ∧ (HasSubst.pSubst t σ : Term VName).AnnotsGround then
        some (HasSubst.pSubst t σ, HasSubst.pSubst τ σ)
      else none

/-- **Soundness**, straight from `elabSubst_sound`. -/
theorem solveJ_hasType {Γ : Ctx VName} {t : Term VName} {τ : Ty} {p : Term VName × Ty}
    (h : solveJ Γ t τ = some p) :
    ∃ σ, elabSubst Γ t τ = some σ ∧ HasType (HasSubst.pSubst Γ σ) p.1 p.2 := by
  rw [solveJ] at h
  split at h
  · exact absurd h (by simp)
  · rename_i σ hσ
    refine ⟨σ, hσ, ?_⟩
    split at h
    · cases h; exact elabSubst_sound hσ
    · exact absurd h (by simp)

/-- The answers that reproduce themselves — the imposed idempotence, as in `Solving.lean`. -/
def solveJStable (Γ : Ctx VName) (t : Term VName) (τ : Ty) : Option (Term VName × Ty) :=
  match solveJ Γ t τ with
  | none => none
  | some p => if solveJ Γ p.1 p.2 = some p then some p else none

theorem solveJStable_idem {Γ : Ctx VName} {t : Term VName} {τ : Ty} {p : Term VName × Ty}
    (h : solveJStable Γ t τ = some p) : solveJStable Γ p.1 p.2 = some p := by
  rw [solveJStable] at h
  split at h
  · exact absurd h (by simp)
  · rename_i q hq
    split at h
    · rename_i hst
      cases h
      simp [solveJStable, hst]
    · exact absurd h (by simp)

private def certJAux (Γ : Ctx VName) (t : Term VName) (τ : Ty) :
    (o : Option (Term VName × Ty)) → solveJStable Γ t τ = o →
    Option { p : Term VName × Ty // solveJStable Γ t τ = some (p.1, p.2) }
  | none,   _ => none
  | some q, h => some ⟨q, by rw [h]⟩

def solveJCert (Γ : Ctx VName) (t : Term VName) (τ : Ty) :
    Option { p : Term VName × Ty // solveJStable Γ t τ = some (p.1, p.2) } :=
  certJAux Γ t τ (solveJStable Γ t τ) rfl

private theorem certJAux_isSome (Γ : Ctx VName) (t : Term VName) (τ : Ty) :
    ∀ (o : Option (Term VName × Ty)) (h : solveJStable Γ t τ = o),
      (certJAux Γ t τ o h).isSome = o.isSome
  | none,   _ => rfl
  | some _, _ => rfl

theorem solveJCert_isSome {Γ : Ctx VName} {t : Term VName} {τ : Ty}
    (h : (solveJStable Γ t τ).isSome) : (solveJCert Γ t τ).isSome := by
  rw [solveJCert, certJAux_isSome]; exact h

/-- **STLC elaborated by constraint generation.** -/
def stlcInferring : Language.ElaboratableLanguage where
  toLanguage := stlcLanguage
  Elaborates Γ t t' τ τ' := solveJStable Γ t τ = some (t', τ')
  elaborates_unique h₁ h₂ := by
    have h := Option.some.inj (h₁.symm.trans h₂)
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  elaborate := solveJCert
  elaborate_complete h := solveJCert_isSome (by rw [h]; rfl)
  quote t' τ' := (t', τ')
  quote_elaborates h := by
    obtain ⟨t, τ, hst⟩ := h
    exact solveJStable_idem hst

/-- Parse and elaborate a file by constraint generation. -/
def inferring (src : String) : Option String :=
  (stlcInferring.elaborateFile src).map stlcInferring.renderElaborated

/-! ## It agrees with the W-based instance

`#eval!` for the usual reason: the parser's round-trip proof rests on the assumed
`stlcUnambiguous`. The elaboration below assumes nothing.
-/

#eval! inferring "def id : ?0 → ?0 := λ x : ⋆ . x"        -- some "def id : ⋆ → ⋆ := λ x : ⋆ . x"
#eval! inferring "def id : ?0 → ?1 := λ x : ⋆ . x"        -- some "def id : ⋆ → ⋆ := λ x : ⋆ . x"
#eval! inferring "def const : ⋆ → ?0 := λ x : ⋆ . ( λ y : ⋆ . x )"
#eval! inferring "def poly : ?0 → ?0 := λ x : ?0 . x"     -- none: a metavariable would survive
#eval! inferring "def bad : ⋆ → ⋆ := λ x : ⋆ . ( λ y : ⋆ . y )"  -- none: genuine type error
#eval! inferring "def id : ?0 → ?0 := λ x : ⋆ . x   def useId : ?1 := id"
-- some "def id : ⋆ → ⋆ := λ x : ⋆ . x def useId : ⋆ → ⋆ := id"

end LambdaLab.Stlc.Named
