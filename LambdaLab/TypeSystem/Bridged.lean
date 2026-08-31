import LambdaLab.TypeSystem.DeBruijn.Category
import LambdaLab.TypeSystem.Named.Category
import LambdaLab.TypeSystem.Bridge

/-!
# `BridgedSys` — named and de Bruijn systems, audited in pairs

An object is a named system, a de Bruijn system, and a bridge exhibiting the second as the
first's reference — the pair-with-audit that the whole formalization program is about. The
bridge travels as a *field*, as `Sys` carries its `TypeSystem`: were it left to instance search,
resolution would have to see through the bundling projections at exactly the transparency that
has bitten this repository twice. Data, not search.

A morphism is a pair of morphisms, one per category, **commuting with the erasures**. The
scope-indexing of `erase` dictates the square's shape rather than obstructing it: translate the
term and map the scope along `mapN`, or erase first and translate underneath —

```
erase (f t) (Γ.map f.mapN) = f_db (erase t Γ)
```

— under a covering hypothesis, with a free-variable coherence (`mapFreeVars`) making covering
itself transport. Composition works because the two coherences feed each other: the composed
scope is the twice-mapped scope (`List.map_map`), and the middle covering comes from the first
morphism's `mapFreeVars`.

**What is deliberately not in the hom (yet):** typing coherence. The two components each
preserve typing in their own category — the named one over its carried `mapCtx`, the bridge
relationally over `CtxCompat` — and relating those two context treatments is the one seam this
design knowingly carries. It becomes a law here the day a transport-along-morphisms theorem
needs it, and not before.

The payoff shape this category exists for: the tower's property classes (`StronglyNormalizing`,
`Confluent`, …) select full subcategories on each side, and the bridge's transport theorems say
membership *pulls back* from the de Bruijn projection — SN-reflection along a bridge is
`sn_of_erase`, stated once. Those statements land here as the arc continues; today the category
stands, with STLC as its first object (`Stlc/Named/Bridge.lean`).
-/

namespace LambdaLab.TypeSystem.Bridged

open LambdaLab.TypeSystem.Bridge (HasFreeVars HasErase StepBridge TypingBridge)

/-- An object: a named system, its de Bruijn reference, and the bridge between them — carried,
not searched for. -/
structure Sys : Type 1 where
  /-- The named side. -/
  named : Named.Sys
  /-- The de Bruijn side. -/
  db : DeBruijn.Sys
  /-- The audit relating them. -/
  [bridge : TypingBridge named.N named.Tm named.Ty db.Tm db.Ty]

attribute [instance] Sys.bridge

/-- A morphism: a pair of morphisms commuting with the erasures. -/
structure Hom (X Y : Sys) where
  /-- The named component. -/
  namedHom : Named.Hom X.named Y.named
  /-- The de Bruijn component. -/
  dbHom : DeBruijn.Hom X.db Y.db
  /-- Free variables cohere: the image term's names come from the source term's, translated.
  This is what lets a covering scope transport through the square below. -/
  mapFreeVars : ∀ (t : X.named.Tm) (x' : Y.named.N),
    x' ∈ HasFreeVars.freeVars (namedHom.mapTm t) →
    x' ∈ (HasFreeVars.freeVars t).map namedHom.mapN
  /-- **The square**: translate then erase under the mapped scope, or erase then translate. -/
  erase_square : ∀ (t : X.named.Tm) (Γ : List X.named.N),
    (∀ x ∈ HasFreeVars.freeVars t, x ∈ Γ) →
    HasErase.erase (namedHom.mapTm t) (Γ.map namedHom.mapN)
      = dbHom.mapTm (HasErase.erase t Γ)

namespace Hom

/-- The identity morphism: both components identities, both coherences by `map_id`. -/
def id (X : Sys) : Hom X X where
  namedHom := Named.Hom.id X.named
  dbHom := DeBruijn.Hom.id X.db
  mapFreeVars t x' h := by simpa [Named.Hom.id] using h
  erase_square t Γ _ := by simp [Named.Hom.id, DeBruijn.Hom.id]

/-- Composition: pairs compose in their categories; the free-variable coherences chain through
`List.mem_map`, and the squares paste — the composed scope is the twice-mapped scope, and the
middle covering is the first coherence's gift. -/
def comp {X Y Z : Sys} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  namedHom := Named.Hom.comp f.namedHom g.namedHom
  dbHom := DeBruijn.Hom.comp f.dbHom g.dbHom
  mapFreeVars t x' h := by
    have h1 := g.mapFreeVars (f.namedHom.mapTm t) x'
      (by simpa [Named.Hom.comp] using h)
    obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp h1
    obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp (f.mapFreeVars t x₁ hx₁)
    simpa [Named.Hom.comp] using List.mem_map.mpr ⟨x₀, hx₀, rfl⟩
  erase_square t Γ hc := by
    have hcf : ∀ x ∈ HasFreeVars.freeVars (f.namedHom.mapTm t),
        x ∈ Γ.map f.namedHom.mapN := by
      intro x hx
      obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp (f.mapFreeVars t x hx)
      exact List.mem_map.mpr ⟨x₀, hc x₀ hx₀, rfl⟩
    show HasErase.erase (g.namedHom.mapTm (f.namedHom.mapTm t))
        (Γ.map (g.namedHom.mapN ∘ f.namedHom.mapN))
      = g.dbHom.mapTm (f.dbHom.mapTm (HasErase.erase t Γ))
    rw [← List.map_map, g.erase_square _ _ hcf, f.erase_square t Γ hc]

end Hom

/-- **The category of bridged systems.** Axioms are componentwise the two categories', plus
proof irrelevance for the coherences. -/
instance : CategoryTheory.Category Sys where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

end LambdaLab.TypeSystem.Bridged
