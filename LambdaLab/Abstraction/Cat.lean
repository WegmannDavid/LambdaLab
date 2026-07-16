import Mathlib.CategoryTheory.Category.Basic
import LambdaLab.Abstraction.Comp

/-!
# `Abs` as (the data of) a bicategory, over Mathlib

Objects are types; a **1-cell** `A ⟶ B` is an abstraction with its annotation type bundled
(`OneCell`); a **2-cell** is a map of annotation types commuting with both legs (`TwoCell`) — a
morphism of spans over the fixed feet `A` and `B`.

This file gives the parts that are genuine, complete Mathlib instances:

* the **local category** `Category (OneCell A B)` — 2-cells compose vertically, with identities and
  the category laws (all by proof-irrelevance + η, since a 2-cell is determined by its map);
* **horizontal composition** of 1-cells (`OneCell.hcomp`) and the identity 1-cell (`OneCell.id`),
  built from `Abstraction.comp` / `Abstraction.id`.

That is the 1- and 2-cell data of the bicategory `Abs`. The full `Bicategory` typeclass additionally
wants the associator/unitor 2-cells and their coherence (pentagon, triangle); Mathlib has **no**
span-bicategory to inherit those from, so they are a separate, substantial development — flagged at
the bottom, not asserted here.
-/

namespace LambdaLab.Abstraction

open CategoryTheory

/-- A 1-cell `A ⟶ B` in `Abs`: an abstraction with its annotation type packaged in. -/
structure OneCell (A B : Type) where
  Annotated : Type
  hom : Abstraction A B Annotated

/-- A 2-cell `f ⟹ g`: a map of annotation types commuting with `realize` and `forget` — i.e. a
morphism of the underlying spans, fixing the feet `A` and `B`. -/
@[ext]
structure TwoCell {A B : Type} (f g : OneCell A B) where
  map : f.Annotated → g.Annotated
  realize_comp : ∀ y, g.hom.realize (map y) = f.hom.realize y
  forget_comp  : ∀ y, g.hom.forget (map y) = f.hom.forget y

/-- **The local category**: 2-cells between `A ⟶ B` compose vertically. A 2-cell is determined by
its `map` (the two conditions are propositions), so every law is `rfl` up to proof-irrelevance. -/
instance (A B : Type) : Category (OneCell A B) where
  Hom f g := TwoCell f g
  id f := { map := _root_.id, realize_comp := fun _ => rfl, forget_comp := fun _ => rfl }
  comp α β :=
    { map := β.map ∘ α.map
      realize_comp := fun y => (β.realize_comp (α.map y)).trans (α.realize_comp y)
      forget_comp  := fun y => (β.forget_comp (α.map y)).trans (α.forget_comp y) }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem TwoCell.id_map {A B : Type} (f : OneCell A B) :
    (𝟙 f : TwoCell f f).map = _root_.id := rfl

@[simp] theorem TwoCell.comp_map {A B : Type} {f g h : OneCell A B}
    (α : f ⟶ g) (β : g ⟶ h) : (α ≫ β).map = β.map ∘ α.map := rfl

/-! ## Horizontal composition of 1-cells, and identities -/

/-- The identity 1-cell `A ⟶ A`. -/
def OneCell.id (A : Type) : OneCell A A := ⟨A, Abstraction.id A⟩

/-- Horizontal composition of 1-cells, `(A ⟶ B) → (B ⟶ C) → (A ⟶ C)` — the pullback composition
of the underlying abstractions, with its (composite) annotation type. -/
def OneCell.hcomp {A B C : Type} (f : OneCell A B) (g : OneCell B C) : OneCell A C :=
  ⟨CompAnnotated f.hom g.hom, f.hom.comp g.hom⟩

@[simp] theorem OneCell.hcomp_abstract {A B C : Type} (f : OneCell A B) (g : OneCell B C) :
    (f.hcomp g).hom.abstract = g.hom.abstract ∘ f.hom.abstract := rfl

/-! ## What remains for a full `Bicategory` instance

The 1- and 2-cell data above is complete. To upgrade to Mathlib's `Bicategory Type` we still owe:

* left/right **whiskering** of a 2-cell by a 1-cell, and their naturality;
* the **associator** `(f ≫ g) ≫ h ≅ f ≫ (g ≫ h)` — a 2-cell iso, i.e. the canonical bijection of
  iterated pullbacks (`Mathlib`'s `pullbackAssoc` is the analogue to lean on);
* the **unitors** `id ≫ f ≅ f`, `f ≫ id ≅ f` — the trivial-fiber isomorphisms;
* the **pentagon** and **triangle** coherence.

None of this is short — the span bicategory's coherence is genuinely involved and Mathlib does not
provide it — so it is deliberately left as a scoped follow-on rather than stubbed with `sorry`.
-/

end LambdaLab.Abstraction
