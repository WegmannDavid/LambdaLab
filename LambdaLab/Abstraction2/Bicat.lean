import Mathlib.CategoryTheory.Bicategory.Basic
import LambdaLab.Abstraction2.Basic

/-!
# `Abs` (indexed design) — toward a `Bicategory` instance

Objects are types. A 1-cell `A ⟶ B` is an abstraction with its annotation family bundled
(`OneCell`). A 2-cell is a **fibrewise** map of annotation families commuting with `realize`
(`TwoCell`) — a map of spans over the fixed feet, but the fibre indexing makes it fibrewise.

This file builds the layer that is genuinely tractable and checks whether the coherence closes
concretely in `Type`. Data first: local category, horizontal composition, identity.
-/

namespace LambdaLab.Abstraction2

open CategoryTheory

/-- Transporting an annotation along its index does not change `realize`. Recurs wherever the
fibres chain (composition, associator). -/
theorem realize_cast {A B : Type} {Ann : B → Type} (F : (b : B) → Ann b → A)
    {x y : B} (h : x = y) (t : Ann x) : F y (h ▸ t) = F x t := by cases h; rfl

/-- Composition of abstractions: the annotation fibre is the dependent sum of the two fibres. -/
def _root_.Abstraction.comp {A B C : Type} {AnnAB : B → Type} {AnnBC : C → Type}
    (f : Abstraction A B AnnAB) (g : Abstraction B C AnnBC) :
    Abstraction A C (fun c => Σ β : AnnBC c, AnnAB (g.realize β)) where
  abstract := g.abstract ∘ f.abstract
  realize  := fun γ => f.realize γ.2
  default  := ⟨g.default, f.default⟩
  abstract_realize := fun c γ => by
    show g.abstract (f.abstract (f.realize γ.2)) = c
    rw [f.abstract_realize, g.abstract_realize]
  realize_complete := fun a => by
    obtain ⟨α, hα⟩ := f.realize_complete a
    obtain ⟨β, hβ⟩ := g.realize_complete (f.abstract a)
    refine ⟨⟨β, hβ.symm ▸ α⟩, ?_⟩
    show f.realize (hβ.symm ▸ α) = a
    rw [realize_cast (fun b (t : AnnAB b) => f.realize t) hβ.symm α]
    exact hα

/-- A 1-cell `A ⟶ B`: an abstraction with its annotation family packaged in. -/
structure OneCell (A B : Type) where
  Ann : B → Type
  hom : Abstraction A B Ann

/-- A 2-cell `f ⟹ g`: a **fibrewise** map of annotation families commuting with `realize`. -/
@[ext]
structure TwoCell {A B : Type} (f g : OneCell A B) where
  map : ∀ {b : B}, f.Ann b → g.Ann b
  realize_map : ∀ {b : B} (x : f.Ann b), g.hom.realize (map x) = f.hom.realize x

/-- Vertical composition of 2-cells. -/
def TwoCell.vcomp {A B : Type} {f g h : OneCell A B} (α : TwoCell f g) (β : TwoCell g h) :
    TwoCell f h where
  map := fun x => β.map (α.map x)
  realize_map := fun x => (β.realize_map (α.map x)).trans (α.realize_map x)

/-- The identity 2-cell. -/
def TwoCell.id {A B : Type} (f : OneCell A B) : TwoCell f f where
  map := fun x => x
  realize_map := fun _ => rfl

/-- **The local category** on `A ⟶ B`. A 2-cell is determined by its `map`, so the laws are `rfl`
after `ext`. -/
instance (A B : Type) : Category (OneCell A B) where
  Hom f g := TwoCell f g
  id f := TwoCell.id f
  comp α β := TwoCell.vcomp α β
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem TwoCell.id_map {A B : Type} (f : OneCell A B) {b : B} (x : f.Ann b) :
    (𝟙 f : TwoCell f f).map x = x := rfl

@[simp] theorem TwoCell.comp_map {A B : Type} {f g h : OneCell A B}
    (α : f ⟶ g) (β : g ⟶ h) {b : B} (x : f.Ann b) :
    (α ≫ β).map x = β.map (α.map x) := rfl

/-- The identity 1-cell `A ⟶ A`. -/
def OneCell.id (A : Type) : OneCell A A where
  Ann := fun a => { a' : A // a' = a }
  hom :=
    { abstract := _root_.id
      realize  := fun x => x.1
      default  := ⟨_, rfl⟩
      abstract_realize := fun _ x => x.2
      realize_complete := fun c => ⟨⟨c, rfl⟩, rfl⟩ }

/-- Horizontal composition of 1-cells. -/
def OneCell.hcomp {A B C : Type} (f : OneCell A B) (g : OneCell B C) : OneCell A C where
  Ann := fun c => Σ β : g.Ann c, f.Ann (g.hom.realize β)
  hom := f.hom.comp g.hom

end LambdaLab.Abstraction2
