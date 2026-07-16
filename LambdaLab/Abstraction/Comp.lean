import LambdaLab.Abstraction.Basic

/-!
# Composition in `Abs`

Two abstractions `f : A ⇝ B` and `g : B ⇝ C` compose to `A ⇝ C`. Since a morphism is a span with
epi legs, composition is **span composition** — the pullback of `f`'s right leg (`forget`) against
`g`'s left leg (`realize`) over the shared middle object `B`:

```
        A ⇝ C  annotated by   Annotated_f ×_B Annotated_g
                                    │             │
                                p_f │             │ p_g
                                    ▼             ▼
             f.forget : Bf' ──────▶ B ◀────── g.realize : Cg'
```

The composite annotation is `Σ c' : Cg', { b' : Bf' // f.forget b' = g.realize c' }` — a `g`-choice
paired with an `f`-choice refining the intermediate `B` value it lands on. For `chars ⇝ lambda`
that is exactly *parenthesization choices × whitespace gaps*, glued over the token stream.

Each of the three laws discharges in a couple of rewrites, and every one turns on the pullback
square — the element-free version replaces `f.forget ∘ p_f` by `g.realize ∘ p_g`, which is where the
fiber condition is spent.

## Bicategory, not a strict category

Composition is pullback, which is defined only *up to isomorphism*, so `Abs` is a bicategory: the
unit and associativity laws hold up to iso of the `Annotated` type (they are not definitional — e.g.
`comp (id A) g` has annotation `Σ _ : Ann_g, {_ // _}`, iso to but not equal to `Ann_g`). This is
the same status as `Span(Set)`. Proving the coherence isos is left as a separate step; nothing below
depends on it.
-/

namespace LambdaLab.Abstraction

variable {A B C Bf' Cg' : Type}

/-- The annotation type of a composite: the pullback of `f.forget` and `g.realize` over `B`. -/
abbrev CompAnnotated (f : Abstraction A B Bf') (g : Abstraction B C Cg') : Type :=
  Σ c' : Cg', { b' : Bf' // f.forget b' = g.realize c' }

/-- Composition of abstractions. -/
def Abstraction.comp (f : Abstraction A B Bf') (g : Abstraction B C Cg') :
    Abstraction A C (CompAnnotated f g) where
  abstract := g.abstract ∘ f.abstract
  realize  := fun y => f.realize y.2.1
  forget   := fun y => g.forget y.1
  annotate := fun c =>
    ⟨g.annotate c, f.annotate (g.realize (g.annotate c)),
      f.forget_annotate (g.realize (g.annotate c))⟩
  abstract_realize := by
    rintro ⟨c', b', h⟩
    show g.abstract (f.abstract (f.realize b')) = g.forget c'
    rw [f.abstract_realize, h, g.abstract_realize]
  forget_annotate := by
    intro t
    show g.forget (g.annotate t) = t
    exact g.forget_annotate t
  realize_surj := by
    intro a
    obtain ⟨c', hc⟩ := g.realize_surj (f.abstract a)   -- g.realize c' = f.abstract a
    obtain ⟨b', hb⟩ := f.realize_surj a                -- f.realize b' = a
    have hp : f.forget b' = g.realize c' := by
      rw [← f.abstract_realize, hb, hc]
    exact ⟨⟨c', b', hp⟩, hb⟩

end LambdaLab.Abstraction
