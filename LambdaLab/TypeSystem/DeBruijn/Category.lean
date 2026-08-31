import Mathlib.CategoryTheory.Category.Basic
import LambdaLab.TypeSystem.DeBruijn.Basic

/-!
# `DBSys` — the category of de Bruijn type systems

Objects are whole *systems* — `Stlc.DeBruijn` is one object, System T will be another — and the
interesting structure is between systems: a subobject is a *fragment* (a sub-syntax closed under
the judgement and the reduction), an inclusion of calculi is a mono, and each lawful class of
the tower carves out a full subcategory (the `Confluent` systems, the `StronglyNormalizing`
systems, …). This is the organizing layer the bridge arc is heading toward; the categories come
first because the de Bruijn side is the clean laboratory — no α, no name maps, no equivariance
question — so the categorical decisions are made here and mirrored by the named side.

## Morphisms are lax on `Step`

A morphism maps terms and types, preserves the judgement on the nose, and preserves reduction
*laxly*: one step lands in `⟶*`. Lax is what composes — a translation may implement one source
step by several target steps, or by none (an administrative collapse) — and it is the weakest
form under which reduction-level structure still transports. The bridge's stronger *positive*
form (`⟶⁺`, which `SN` transport needs) is a refinement a sub-class of morphisms can carry
later; it is deliberately not the hom condition, so that erasure-like and quotient-like maps
are all eligible.

Contexts are lists, so the context transport is not data: it is `Γ.map mapTy`, and the
composition law is `List.map_map`. The named mirror is not so lucky — see its header.

Objects bundle the *lawless* `TypeSystem`, per the tower's discipline: everything above is a
property, and properties select full subcategories rather than changing the objects.

Mathlib's `Category` supplies the vocabulary (and, later, `Subobject`); the import is free
here for the reason `Bicat.lean`'s is — this file is metatheory, outside the executables' cone.
One hazard travels with it: Mathlib's `Quiver` arrow is spelled `⟶` too, at precedence 10, so
an unparenthesized `t ⟶ t' → P` parses as `t ⟶ (t' → P)` and dies badly — the `(t ⟶ t')` in
`mapStep` is load-bearing. Elaboration then disambiguates the parenthesized form by instance,
exactly as the two turnstiles are disambiguated by the context's type.
-/

namespace LambdaLab.TypeSystem.DeBruijn

/-- An object: a de Bruijn type system, bundled. -/
structure Sys : Type 1 where
  /-- The terms. -/
  Tm : Type
  /-- The types. -/
  Ty : Type
  /-- The system: judgement and reduction, lawless — laws select subcategories. -/
  [inst : TypeSystem Tm Ty]

attribute [instance] Sys.inst

/-- A morphism of de Bruijn systems: terms and types map, typing is preserved on the nose
(contexts transported by `List.map`), reduction is preserved laxly. -/
@[ext] structure Hom (S T : Sys) where
  /-- The term translation. -/
  mapTm : S.Tm → T.Tm
  /-- The type translation. -/
  mapTy : S.Ty → T.Ty
  /-- Typing is preserved; the context comes along by `map`. -/
  mapTyping : ∀ {Γ : Context S.Ty} {t : S.Tm} {τ : S.Ty},
    Γ ⊢ t : τ → Γ.map mapTy ⊢ mapTm t : mapTy τ
  /-- One step lands in many — the lax condition. -/
  mapStep : ∀ {t t' : S.Tm}, (t ⟶ t') → mapTm t ⟶* mapTm t'

namespace Hom

/-- Lax on one step is lax on every reduction sequence. -/
theorem mapMStep {S T : Sys} (f : Hom S T) {t t' : S.Tm} (h : t ⟶* t') :
    f.mapTm t ⟶* f.mapTm t' := by
  induction h with
  | refl => exact RTC.refl
  | tail _ s ih => exact ih.trans (f.mapStep s)

/-- The identity morphism. -/
def id (S : Sys) : Hom S S where
  mapTm := _root_.id
  mapTy := _root_.id
  mapTyping h := by simpa using h
  mapStep s := RTC.single s

/-- Composition — diagrammatic. The context law is `List.map_map`; the step law is laxness
composing with itself through `mapMStep`. -/
def comp {S T U : Sys} (f : Hom S T) (g : Hom T U) : Hom S U where
  mapTm := g.mapTm ∘ f.mapTm
  mapTy := g.mapTy ∘ f.mapTy
  mapTyping h := by simpa [List.map_map] using g.mapTyping (f.mapTyping h)
  mapStep s := g.mapMStep (f.mapStep s)

end Hom

/-- **The category of de Bruijn type systems.** The axioms are definitional — data components
compose as functions compose, the laws are proofs — and the default automation closes them. -/
instance : CategoryTheory.Category Sys where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

end LambdaLab.TypeSystem.DeBruijn
