import Mathlib.CategoryTheory.Category.Basic
import LambdaLab.TypeSystem.Named.Basic

/-!
# `NamedSys` — the category of named type systems

The named mirror of `TypeSystem/DeBruijn/Category.lean`: objects are whole named systems —
`Stlc.Named` at each `Atom` instance is one — morphisms translate names, terms and types,
preserve the judgement on the nose and reduction laxly. The de Bruijn header has the shared
story; this one records the two decisions the names force.

## The context transport is *data*

A de Bruijn context is a list, so a morphism transports it by `map` and the composition law is
`List.map_map`. A named context is a `Std.HashMap`, and there the same design dies twice over:
rebuilding a map along `mapN`/`mapTy` (via `toList`/`ofList`) composes only up to an equality
of hashmaps that **cannot be proved** — no extensionality — and is not even well-defined
keywise when `mapN` collides. So the morphism *carries* its context transport (`mapCtx`),
constrained keywise on image keys (`mapCtx_get?`), and composition is composition of the
carried functions — definitional, no extensionality, no `ofList` in sight. The same
no-extensionality fact that made `cong` a field of the named tower and a theorem of the
de Bruijn one shapes the hom here.

Off-image keys are deliberately unconstrained: `mapCtx` may carry junk there, and no law below
looks. Tightening that (e.g. for subobject work) is a refinement, not a redesign.

## What is *not* demanded of `mapN`

Not injectivity, and not equivariance. A collapsing `mapN` makes `mapCtx_get?` and `mapTyping`
hard to satisfy *for that morphism* — the laws are the gate, morphism by morphism — and the
principled nominal condition (equivariance under atom permutations, `Nominal/`'s vocabulary)
is a refinement this category should eventually meet. It is left out of the first version
knowingly: the de Bruijn category is the laboratory precisely because it has no such question,
and the named one should not guess at the answer before the categorical layer is exercised.
-/

namespace LambdaLab.TypeSystem.Named

open LambdaLab.Nominal (Atom)

/-- An object: a named type system, bundled — the name type and its `Atom` supply travel with
the carriers. -/
structure Sys : Type 1 where
  /-- The names. -/
  N : Type
  /-- The terms. -/
  Tm : Type
  /-- The types. -/
  Ty : Type
  /-- Names are atoms: decidable, hashable, inexhaustible. -/
  [atom : Atom N]
  /-- The system: judgement and reduction, lawless — laws select subcategories. -/
  [inst : TypeSystem N Tm Ty]

attribute [instance] Sys.atom Sys.inst

/-- A morphism of named systems. The context transport is a *field*, spec'd keywise on image
keys — see the header for why it cannot be derived from `mapN` and `mapTy`. -/
@[ext] structure Hom (S T : Sys) where
  /-- The name translation. -/
  mapN : S.N → T.N
  /-- The term translation. -/
  mapTm : S.Tm → T.Tm
  /-- The type translation. -/
  mapTy : S.Ty → T.Ty
  /-- The context transport — carried, not derived. -/
  mapCtx : Context S.N S.Ty → Context T.N T.Ty
  /-- On image keys, the transport is the translation, keywise. -/
  mapCtx_get? : ∀ (Γ : Context S.N S.Ty) (x : S.N),
    (mapCtx Γ).get? (mapN x) = (Γ.get? x).map mapTy
  /-- Typing is preserved, over the carried transport. -/
  mapTyping : ∀ {Γ : Context S.N S.Ty} {t : S.Tm} {τ : S.Ty},
    Γ ⊢ t : τ → mapCtx Γ ⊢ mapTm t : mapTy τ
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
  mapN := _root_.id
  mapTm := _root_.id
  mapTy := _root_.id
  mapCtx := _root_.id
  mapCtx_get? Γ x := by simp
  mapTyping h := h
  mapStep s := RTC.single s

/-- Composition — diagrammatic. The carried transports compose as functions, the keywise spec
by `Option.map_map`, and typing by feeding one law to the next: no hashmap is ever rebuilt. -/
def comp {S T U : Sys} (f : Hom S T) (g : Hom T U) : Hom S U where
  mapN := g.mapN ∘ f.mapN
  mapTm := g.mapTm ∘ f.mapTm
  mapTy := g.mapTy ∘ f.mapTy
  mapCtx := g.mapCtx ∘ f.mapCtx
  mapCtx_get? Γ x := by
    show (g.mapCtx (f.mapCtx Γ)).get? (g.mapN (f.mapN x)) = _
    rw [g.mapCtx_get?, f.mapCtx_get?, Option.map_map]
  mapTyping h := g.mapTyping (f.mapTyping h)
  mapStep s := g.mapMStep (f.mapStep s)

end Hom

/-- **The category of named type systems.** The axioms are definitional for the de Bruijn
category's reason: every data component composes as functions compose — including the carried
context transport, which is the design's payoff — and the laws are proofs. -/
instance : CategoryTheory.Category Sys where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

end LambdaLab.TypeSystem.Named
