/-!
# The category `Abs`

Objects are types; a morphism `Concrete ⇝ Abstract` is an **abstraction**: a lossy map that keeps
enough to reconstruct a concrete witness. The reconstruction data lives in a third type
`Annotated` — the `Abstract` value *plus* the information the abstraction throws away.

Structurally (see the `Comp` module) a morphism is a **span**

```
Concrete  ◀──realize──  Annotated  ──forget──▶  Abstract
```

whose left leg `realize` is epi and whose right leg `forget` is a split epi (its section is
`annotate`); composition is pullback of spans. `Abs` is therefore a wide sub-bicategory of
`Span(Set)`.

## The four legs

* `abstract : Concrete → Abstract` — the lossy map itself (tokenize / parse / erase parentheses).
* `realize  : Annotated → Concrete` — faithful reconstruction from the annotated form.
* `forget   : Annotated → Abstract` — drop the annotations, back to the bare abstract value.
* `annotate : Abstract → Annotated` — a *canonical* annotation of a bare abstract value.

## The three laws

* `abstract_realize` : `abstract ∘ realize = forget`. Reconstruct, then re-abstract, and you land on
  the projection. (Tokenizer: render an annotated token stream, re-tokenize, recover the tokens.)
  This does **not** force `abstract` injective — the point of a lossy map.
* `forget_annotate`  : `forget ∘ annotate = 1`. `annotate` is a section of `forget`.
* `realize_surj`     : `realize` is surjective — the annotated form names every concrete value
  (completeness).
-/

namespace LambdaLab.Abstraction

/-- A morphism of `Abs`: an abstraction of `Concrete` onto `Abstract`, factored through an
`Annotated` type that carries the reconstruction data. -/
structure Abstraction (Concrete Abstract Annotated : Type) where
  abstract : Concrete → Abstract
  realize  : Annotated → Concrete
  forget   : Annotated → Abstract
  annotate : Abstract → Annotated
  abstract_realize : ∀ y, abstract (realize y) = forget y
  forget_annotate  : ∀ t, forget (annotate t) = t
  realize_surj     : ∀ x, ∃ y, realize y = x

namespace Abstraction

variable {Concrete Abstract Annotated : Type}

/-! ## Derived facts

Both directions of the morphism split, and each split is forced by one law. -/

/-- `annotate` is injective — it is a section of `forget`, and sections are monic. -/
theorem annotate_injective (m : Abstraction Concrete Abstract Annotated) :
    Function.Injective m.annotate := by
  intro t₁ t₂ h
  have := congrArg m.forget h
  rwa [m.forget_annotate, m.forget_annotate] at this

/-- `abstract` is a **split epi**: `realize ∘ annotate` is a section of it.
`abstract ∘ (realize ∘ annotate) = forget ∘ annotate = 1`. -/
theorem abstract_section (m : Abstraction Concrete Abstract Annotated) (t : Abstract) :
    m.abstract (m.realize (m.annotate t)) = t := by
  rw [m.abstract_realize, m.forget_annotate]

/-! ## Identity

The identity abstraction loses nothing: all three types coincide and every leg is the identity. -/

/-- The identity morphism `A ⇝ A` in `Abs`. -/
def id (A : Type) : Abstraction A A A where
  abstract := _root_.id
  realize  := _root_.id
  forget   := _root_.id
  annotate := _root_.id
  abstract_realize := fun _ => rfl
  forget_annotate  := fun _ => rfl
  realize_surj     := fun x => ⟨x, rfl⟩

end Abstraction

end LambdaLab.Abstraction
