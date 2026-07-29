import LambdaLab.Stlc.Named.Lang

/-!
# Metavariables in STLC source

`?0`, `?7` are spellable types (`Stlc/Named/Lang.lean`), so a source file may write them. This
file is about what they actually *mean* here, which is not what the notation suggests.

## Without an inference stage, `?n` is a rigid opaque type

`HasType` never introduces or solves a `Ty.mvar` — there is no rule mentioning one. So the
judgement treats `?0` exactly the way it treats `⋆`: an atom that equals itself and nothing else.
`?0` and `?1` are two *different* atoms, and `?0` is not `⋆`.

That makes `def poly : ?0 → ?0 := λ x : ?0 . x` well-typed but **not polymorphic**. It cannot be
used at `⋆ → ⋆`. `?n` is an infinite supply of extra base types, not a hole.

Turning them into real holes is exactly what `Typing/W.lean` is for: unification is what lets one
stand for something else. That stage is not wired into the surface (see `Lang.lean` — binder
annotations are mandatory, so nothing needs solving), which is why `stlcElaboratable` refuses to
let a metavariable survive a declaration at all: a `?0` that no one will ever solve is a mistake
in the source, not an inference request.

## Two policies, one `Language`

`stlcElaboratable` (in `Lang.lean`) demands `τ.Ground`; `stlcPermissive` below drops that and is
otherwise identical. They share a `toLanguage`, so they parse and print the *same* files — the
disagreement is entirely in `Elaborates`, which is the interface's claim: leakage is the
language's decision, not a field of `ElaboratableLanguage`.
-/

namespace LambdaLab.Stlc.Named

/-- STLC with metavariables allowed to survive a declaration and enter the context. Identical to
`stlcElaboratable` except for the missing groundness demands. -/
def stlcPermissive : Language.ElaboratableLanguage where
  toLanguage := stlcLanguage
  Elaborates Γ t t' τ τ' := t' = t ∧ τ' = τ ∧ HasType Γ t τ
  elaborates_unique h₁ h₂ := by
    obtain ⟨rfl, rfl, -⟩ := h₁
    obtain ⟨rfl, rfl, -⟩ := h₂
    exact ⟨rfl, rfl⟩
  elaborate Γ t τ := if h : HasType Γ t τ then some ⟨(t, τ), rfl, rfl, h⟩ else none
  elaborate_complete h := by
    obtain ⟨rfl, rfl, h⟩ := h
    simp only [dif_pos h]
    rfl
  quote t' τ' := (t', τ')
  quote_elaborates h := by
    obtain ⟨t, τ, rfl, rfl, h⟩ := h
    exact ⟨rfl, rfl, h⟩

/-- Elaborate under the strict policy (no metavariable may survive). -/
def strict (src : String) : Option String :=
  (stlcElaboratable.elaborateFile src).map stlcElaboratable.renderElaborated

/-- Elaborate under the permissive policy. -/
def permissive (src : String) : Option String :=
  (stlcPermissive.elaborateFile src).map stlcPermissive.renderElaborated

/-! ## What the two policies say

Every string below parses — `stlcLanguage.parseFile` accepts all of them. Everything that differs
is elaboration.

These are `#eval!`, not `#eval`: STLC's parser is built from `mixfix`, whose law is discharged by
the still-assumed `stlcUnambiguous` (`Lang.lean`), so the term carries a `sorry` in its
*correctness proof*. The code being run is ordinary compiled code; it is the round-trip guarantee
that is conditional, not the execution. Elaboration itself — `infer`, `HasType` — is sorry-free.
-/

-- The identity at an unsolved type. Strict rejects it; permissive keeps it.
#eval! strict     "def poly : ?0 → ?0 := λ x : ?0 . x"      -- none
#eval! permissive "def poly : ?0 → ?0 := λ x : ?0 . x"      -- some "def poly : ?0 → ?0 := …"

-- The metavariable travels through the context: `poly` is in scope at `?0 → ?0`, and `again`
-- picks it up. This is the leak the strict policy exists to prevent.
#eval! permissive "def poly : ?0 → ?0 := λ x : ?0 . x   def again : ?0 → ?0 := poly"
-- some "def poly : ?0 → ?0 := λ x : ?0 . x def again : ?0 → ?0 := poly"

-- …and here is why it is a leak worth preventing. `poly` is *not* polymorphic: `?0` is an atom,
-- so it does not match `⋆`, and nothing will ever make it. Rejected even by the permissive one.
#eval! permissive "def poly : ?0 → ?0 := λ x : ?0 . x   def bad : ⋆ → ⋆ := poly"      -- none

-- Different indices are different atoms, so this fails too — `?0 ≠ ?1`.
#eval! permissive "def poly : ?0 → ?0 := λ x : ?0 . x   def bad : ?1 → ?1 := poly"    -- none

-- Metavariables in nested positions behave the same way: fine on their own terms…
#eval! permissive "def apply : ( ?0 → ?1 ) → ?0 → ?1 := λ f : ?0 → ?1 . ( λ x : ?0 . f x )"
-- …and a ground declaration is accepted by both policies, unchanged.
#eval! strict     "def id : ⋆ → ⋆ := λ x : ⋆ . x"
#eval! permissive "def id : ⋆ → ⋆ := λ x : ⋆ . x"

-- Mixing: one ground declaration and one not. Strict rejects the *file*, since a single
-- declaration failing to elaborate fails the fold.
#eval! strict     "def id : ⋆ → ⋆ := λ x : ⋆ . x   def poly : ?0 → ?0 := λ x : ?0 . x"  -- none

end LambdaLab.Stlc.Named
