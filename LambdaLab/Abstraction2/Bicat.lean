import Mathlib.CategoryTheory.Bicategory.Basic
import LambdaLab.Abstraction2.Basic

/-!
# `Abs` (indexed design) — toward a `Bicategory` instance

Objects are types. A 1-cell `A ⟶ B` is an abstraction with its annotation family bundled
(`OneCell`). A 2-cell is a **fibrewise** map of annotation families commuting with `realize`
(`TwoCell`) — a map of spans over the fixed feet, but the fibre indexing makes it fibrewise.

## ⚠ Status: WIP — the `Bicategory Abs` instance has ONE sorried coherence field

The full 1/2-cell data (composition, identity, associator, unitors, whiskerings) is built with its
own laws proved, and Mathlib's `aesop_cat` discharged MOST of the bicategory coherence **including
the pentagon and the triangle**. Hand-proved with transport handling: `whiskerRight_id`,
`whiskerLeft_comp`, `id_whiskerLeft` (singleton fibre), `whisker_exchange` (dependent-map naturality
via `map_eqRec` + `sigma_mk_heq`).

**ONE coherence field remains, as `sorry`: `comp_whiskerLeft`.** It reduces (via `Sigma.ext`) to the
Σ-transport distribution `h ▸ ⟨β,φ⟩ = ⟨h ▸ β, h ▸ φ⟩`, which is TRUE but whose statement will not
typecheck cleanly (the second component needs `Eq.rec`'s dependent motive, and the goal keeps the
transport in mismatched `▸`/`cast`/`Eq.rec` forms). Until it is filled, **`Bicategory Abs` depends
on `sorryAx` and must not be relied on.** Helpers in place: `map_eqRec`, `sigma_mk_heq`.
-/

namespace LambdaLab.Abstraction2

open CategoryTheory

/-- Transporting an annotation along its index does not change `realize`. Recurs wherever the
fibres chain (composition, associator). -/
theorem realize_cast {A B : Type} {Ann : B → Type} (F : (b : B) → Ann b → A)
    {x y : B} (h : x = y) (t : Ann x) : F y (h ▸ t) = F x t := by cases h; rfl

/-- Naturality of a dependent map under transport of its argument's index. -/
theorem map_eqRec {B : Type} {P Q : B → Type} (F : (b : B) → P b → Q b)
    {b1 b2 : B} (h : b1 = b2) (x : P b1) : F b2 (h ▸ x) = h ▸ F b1 x := by cases h; rfl

/-- `HEq` congruence for a dependent pair over a moving base index. -/
theorem sigma_mk_heq {γ : Type} {P : γ → Type} {Q : (c : γ) → P c → Type}
    {c1 c2 : γ} (hc : c1 = c2) {a1 : P c1} {a2 : P c2} {b1 : Q c1 a1} {b2 : Q c2 a2}
    (ha : a1 ≍ a2) (hb : b1 ≍ b2) :
    (⟨a1, b1⟩ : Σ z : P c1, Q c1 z) ≍ (⟨a2, b2⟩ : Σ z : P c2, Q c2 z) := by
  subst hc; obtain rfl := eq_of_heq ha; obtain rfl := eq_of_heq hb; rfl


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

/-- A 2-cell `f ⟹ g`: a **fibrewise** map of annotation families commuting with `realize`.
`map` takes the fibre index `b` explicitly, which keeps `ext` and `funext` clean. -/
@[ext]
structure TwoCell {A B : Type} (f g : OneCell A B) where
  map : (b : B) → f.Ann b → g.Ann b
  realize_map : ∀ (b : B) (x : f.Ann b), g.hom.realize (map b x) = f.hom.realize x

/-- Vertical composition of 2-cells. -/
def TwoCell.vcomp {A B : Type} {f g h : OneCell A B} (α : TwoCell f g) (β : TwoCell g h) :
    TwoCell f h where
  map := fun b x => β.map b (α.map b x)
  realize_map := fun b x => (β.realize_map b (α.map b x)).trans (α.realize_map b x)

/-- The identity 2-cell. -/
def TwoCell.id {A B : Type} (f : OneCell A B) : TwoCell f f where
  map := fun _ x => x
  realize_map := fun _ _ => rfl

/-- **The local category** on `A ⟶ B`. A 2-cell is determined by its `map`, so the laws are `rfl`
after `ext`. -/
instance (A B : Type) : Category (OneCell A B) where
  Hom f g := TwoCell f g
  id f := TwoCell.id f
  comp α β := TwoCell.vcomp α β
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem TwoCell.id_map {A B : Type} (f : OneCell A B) (b : B) (x : f.Ann b) :
    (𝟙 f : TwoCell f f).map b x = x := rfl

@[simp] theorem TwoCell.comp_map {A B : Type} {f g h : OneCell A B}
    (α : f ⟶ g) (β : g ⟶ h) (b : B) (x : f.Ann b) :
    (α ≫ β).map b x = β.map b (α.map b x) := rfl

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


/-! ## Associator and unitors (the invertible 2-cell data) -/

/-- The **associator** `(f ≫ g) ≫ h ≅ f ≫ (g ≫ h)`. Transport-free: both fibres are the same
`Σγ Σβ, f.Ann (g.realize β)` nested differently, so it is pure re-association. -/
def associator {A B C D : Type} (f : OneCell A B) (g : OneCell B C) (h : OneCell C D) :
    (f.hcomp g).hcomp h ≅ f.hcomp (g.hcomp h) where
  hom := { map := fun _ x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩, realize_map := fun _ _ => rfl }
  inv := { map := fun _ x => ⟨x.1.1, x.1.2, x.2⟩, realize_map := fun _ _ => rfl }
  hom_inv_id := by apply TwoCell.ext; funext b x; rfl
  inv_hom_id := by apply TwoCell.ext; funext b x; rfl

/-- The **left unitor** `𝟙 A ≫ f ≅ f`. The `𝟙 A` fibre is a singleton, so it drops out cleanly. -/
def leftUnitor {A B : Type} (f : OneCell A B) : (OneCell.id A).hcomp f ≅ f where
  hom := { map := fun _ x => x.1, realize_map := fun _ x => x.2.2.symm }
  inv := { map := fun _ β => ⟨β, ⟨f.hom.realize β, rfl⟩⟩, realize_map := fun _ _ => rfl }
  hom_inv_id := by apply TwoCell.ext; funext b x; obtain ⟨β, a', ha'⟩ := x; cases ha'; rfl
  inv_hom_id := by apply TwoCell.ext; funext b x; rfl

/-- The **right unitor** `f ≫ 𝟙 B ≅ f`. Carries a transport: the `𝟙 B` fibre pins the index to `b`,
so `f.Ann b'` must be transported along `b' = b`. -/
def rightUnitor {A B : Type} (f : OneCell A B) : f.hcomp (OneCell.id B) ≅ f where
  hom := { map := fun _ x => x.1.2 ▸ x.2
           realize_map := fun _ x => realize_cast (fun b (t : f.Ann b) => f.hom.realize t) x.1.2 x.2 }
  inv := { map := fun _ φ => ⟨⟨_, rfl⟩, φ⟩, realize_map := fun _ _ => rfl }
  hom_inv_id := by apply TwoCell.ext; funext b x; obtain ⟨⟨b', hb'⟩, φ⟩ := x; cases hb'; rfl
  inv_hom_id := by apply TwoCell.ext; funext b x; rfl

/-! ## Whiskerings -/

/-- Left whiskering `f ◁ η : f ≫ g ⟶ f ≫ h`. Carries a transport (the right operand's fibre moves
along `η`'s realize equation). -/
def whiskerL {A B C : Type} (f : OneCell A B) {g h : OneCell B C} (η : TwoCell g h) :
    TwoCell (f.hcomp g) (f.hcomp h) where
  map := fun c x => ⟨η.map c x.1, (η.realize_map c x.1).symm ▸ x.2⟩
  realize_map := fun c x =>
    realize_cast (fun b (t : f.Ann b) => f.hom.realize t) (η.realize_map c x.1).symm x.2

/-- Right whiskering `η ▷ h : f ≫ h ⟶ g ≫ h`. Transport-free. -/
def whiskerR {A B C : Type} {f g : OneCell A B} (η : TwoCell f g) (h : OneCell B C) :
    TwoCell (f.hcomp h) (g.hcomp h) where
  map := fun c x => ⟨x.1, η.map (h.hom.realize x.1) x.2⟩
  realize_map := fun c x => η.realize_map (h.hom.realize x.1) x.2

/-- Identity-1-cell fibres are singletons. -/
instance instSubsingletonEqFibre {α : Type} (v : α) : Subsingleton {a' : α // a' = v} :=
  ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩

instance instSubsingletonIdFibre {A : Type} (v : A) : Subsingleton ((OneCell.id A).Ann v) :=
  instSubsingletonEqFibre v

/-! ## The bicategory `Abs`

Objects are types, wrapped as `Abs` to avoid clashing with the existing `Category Type` (functions).
-/

/-- Objects of the bicategory: types. Wrapped so the `Bicategory` instance does not collide with the
function-category structure on `Type`. -/
def Abs : Type _ := Type

instance : Bicategory Abs where
  Hom A B := OneCell A B
  id A := OneCell.id A
  comp f g := f.hcomp g
  whiskerLeft := fun {_ _ _} f {_ _} η => whiskerL f η
  whiskerRight := fun {_ _ _} {_ _} η h => whiskerR η h
  associator f g h := associator f g h
  leftUnitor f := leftUnitor f
  rightUnitor f := rightUnitor f
  whiskerRight_id := by
    intros; apply TwoCell.ext; funext b x; obtain ⟨⟨b', hb'⟩, φ⟩ := x; cases hb'; rfl
  id_whiskerLeft := by
    intros; apply TwoCell.ext; funext b x; obtain ⟨β, s⟩ := x
    refine Sigma.ext rfl ?_; exact heq_of_eq (Subsingleton.elim _ _)
  whiskerLeft_comp := by
    intros; apply TwoCell.ext; funext b x; obtain ⟨β, φ⟩ := x
    refine Sigma.ext rfl ?_
    simp only [whiskerL, whiskerR, associator, leftUnitor, rightUnitor,
      TwoCell.comp_map, TwoCell.id_map, eqRec_heq_iff_heq, heq_eq_eq,
      eqRec_eq_cast, cast_cast, cast_eq]
  -- The ONLY remaining coherence gap. Reduces (via `Sigma.ext`) to the Σ-transport distribution
  -- `h ▸ ⟨β, φ⟩ = ⟨h ▸ β, h ▸ φ⟩`, which is TRUE (`cases h; rfl`) but whose *statement* will not
  -- typecheck cleanly: the second component needs `Eq.rec`'s dependent motive, and the goal keeps
  -- the transport in mismatched `▸`/`cast`/`Eq.rec` forms. A well-stated Σ-transport lemma closes it.
  comp_whiskerLeft := by intros; sorry
  whisker_exchange := by
    intros; apply TwoCell.ext; funext b x; obtain ⟨β, φ⟩ := x
    refine Sigma.ext rfl ?_
    simp only [whiskerL, whiskerR, TwoCell.comp_map]
    refine HEq.trans ?_ (eqRec_heq _ _).symm
    exact HEq.trans (heq_of_eq (map_eqRec _ _ _)) (eqRec_heq _ _)

end LambdaLab.Abstraction2
