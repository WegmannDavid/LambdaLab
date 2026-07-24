import Mathlib.CategoryTheory.Bicategory.Basic
import LambdaLab.Abstraction2.Basic

/-!
# `Abs` (v3) — the `Bicategory` instance for the refined structure

Port of `Abstraction/Bicat.lean` to the `Abstraction2` structure (partial `abstract`,
no `realize_complete` law). The port is cheap by design: the whole 2-cell layer —
`TwoCell`, whiskerings, associator, coherence — lives on the annotation/`realize`
side and never mentions `abstract`, so partiality changes nothing here; `comp`'s
`Option.bind` and the dropped law are absorbed in `Basic.lean`.

One genuine simplification over the old instance: the identity 1-cell is the
`Unit`-annotated `Abstraction.id`, whose `realize` is **definitionally** the index —
the old subtype fibre `{a' // a' = a}` pinned the index only propositionally, which
is what forced the right unitor's transport. Here `rightUnitor` is transport-free and
the unitor-side coherence closes by `rfl` (Σ/Unit eta).

## The transport crux (`comp_whiskerLeft` / `eqRec_hcomp`) — unchanged

Ported verbatim from the old file, same warning applies: the distribution lemma must
be phrased with `realize_cast` (exactly the form `whiskerL` produces), not an opaque
dependent `Eq.rec`; then `rw [eqRec_hcomp f g]` + a **default-transparency `rfl`**
closes it.
-/

namespace LambdaLab.Abstraction2

open CategoryTheory

/-- Transporting an annotation along its index does not change `realize`. Recurs wherever the
fibres chain (composition, whiskering). -/
theorem realize_cast {A B : Type} {Ann : B → Type} (F : (b : B) → Ann b → A)
    {x y : B} (h : x = y) (t : Ann x) : F y (h ▸ t) = F x t := by cases h; rfl

/-- Naturality of a dependent map under transport of its argument's index. -/
theorem map_eqRec {B : Type} {P Q : B → Type} (F : (b : B) → P b → Q b)
    {b1 b2 : B} (h : b1 = b2) (x : P b1) : F b2 (h ▸ x) = h ▸ F b1 x := by cases h; rfl

/-- A 1-cell `A ⟶ B`: an abstraction with its annotation family packaged in. -/
structure OneCell (A B : Type) where
  Ann : B → Type
  hom : Abstraction A B Ann

/-- A 2-cell `f ⟹ g`: a **fibrewise** map of annotation families commuting with `realize`.
`map` takes the fibre index `b` explicitly, which keeps `ext` and `funext` clean.
(No condition on `abstract`: it is not a leg of the span, just the bundled algorithm.) -/
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

/-- The identity 1-cell `A ⟶ A` — the `Unit`-annotated `Abstraction.id`. Its `realize` is
definitionally the index, which keeps the unitors transport-free. -/
def OneCell.id (A : Type) : OneCell A A where
  Ann := fun _ => Unit
  hom := Abstraction.id A

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

/-- The **left unitor** `𝟙 A ≫ f ≅ f`. The `𝟙 A` fibre is `Unit`, so it drops out by eta. -/
def leftUnitor {A B : Type} (f : OneCell A B) : (OneCell.id A).hcomp f ≅ f where
  hom := { map := fun _ x => x.1, realize_map := fun _ _ => rfl }
  inv := { map := fun _ β => ⟨β, ()⟩, realize_map := fun _ _ => rfl }
  hom_inv_id := by apply TwoCell.ext; funext b x; rfl
  inv_hom_id := by apply TwoCell.ext; funext b x; rfl

/-- The **right unitor** `f ≫ 𝟙 B ≅ f`. Transport-free (unlike the old subtype-fibre version):
`(𝟙 B).realize` is definitionally the index, so the fibre `f.Ann ((𝟙 B).realize β)` *is*
`f.Ann b`. -/
def rightUnitor {A B : Type} (f : OneCell A B) : f.hcomp (OneCell.id B) ≅ f where
  hom := { map := fun _ x => x.2, realize_map := fun _ _ => rfl }
  inv := { map := fun _ φ => ⟨(), φ⟩, realize_map := fun _ _ => rfl }
  hom_inv_id := by apply TwoCell.ext; funext b x; rfl
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
  map := fun _ x => ⟨x.1, η.map (h.hom.realize x.1) x.2⟩
  realize_map := fun _ x => η.realize_map (h.hom.realize x.1) x.2

/-- Identity-1-cell fibres are singletons (definitionally, by `Unit` eta). -/
instance instSubsingletonIdFibre {A : Type} (v : A) : Subsingleton ((OneCell.id A).Ann v) :=
  ⟨fun _ _ => rfl⟩

/-- `Eq.rec` transport of an `hcomp` fibre distributes over its two components, in the exact
`@Eq.rec` form that `whiskerL` on a composite produces. -/
theorem eqRec_hcomp {A B C : Type} (f : OneCell A B) (g : OneCell B C) {c1 c2 : C} (e : c1 = c2)
    (β : g.Ann c1) (φ : f.Ann (g.hom.realize β)) :
    @Eq.rec C c1 (fun x _ => (f.hcomp g).Ann x) (⟨β, φ⟩ : (f.hcomp g).Ann c1) c2 e
      = ⟨e ▸ β, (realize_cast (fun b (t : g.Ann b) => g.hom.realize t) e β).symm ▸ φ⟩ := by
  cases e; rfl

/-- Standalone proof of the `comp_whiskerLeft` coherence, with `f`/`g` named so `eqRec_hcomp` can be applied. -/
theorem comp_whiskerLeft_aux {A B C D : Type} (f : OneCell A B) (g : OneCell B C)
    {h h' : OneCell C D} (η : TwoCell h h') :
    whiskerL (f.hcomp g) η
      = (associator f g h).hom ≫ whiskerL f (whiskerL g η) ≫ (associator f g h').inv := by
  apply TwoCell.ext; funext b x; obtain ⟨γ, β, φ⟩ := x
  dsimp only [whiskerL, whiskerR, associator, TwoCell.comp_map, TwoCell.vcomp,
    CategoryStruct.comp]
  rw [eqRec_hcomp f g]; rfl

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
    intros; apply TwoCell.ext; funext b x; rfl
  id_whiskerLeft := by
    intros; apply TwoCell.ext; funext b x; obtain ⟨β, s⟩ := x
    refine Sigma.ext rfl ?_; exact heq_of_eq (Subsingleton.elim _ _)
  whiskerLeft_comp := by
    intros; apply TwoCell.ext; funext b x; obtain ⟨β, φ⟩ := x
    refine Sigma.ext rfl ?_
    simp only [whiskerL, TwoCell.comp_map, heq_eq_eq, eqRec_eq_cast, cast_cast]
  comp_whiskerLeft := by intros; exact comp_whiskerLeft_aux _ _ _
  whisker_exchange := by
    intros; apply TwoCell.ext; funext b x; obtain ⟨β, φ⟩ := x
    refine Sigma.ext rfl ?_
    simp only [whiskerL, TwoCell.comp_map]
    refine HEq.trans ?_ (eqRec_heq _ _).symm
    exact HEq.trans (heq_of_eq (map_eqRec _ _ _)) (eqRec_heq _ _)

end LambdaLab.Abstraction2
