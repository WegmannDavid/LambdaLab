/-!
# `IsoParser` — a consuming biparser carrying an annotation family

An `IsoParser α fst fol v Ann` is a lossless bijection between input streams and **value + annotation**:
`v` is the value we care about, and `Ann x` is *the choices the printer makes that are not pinned by
the value* (variable whitespace, redundant grouping, …). `print` needs those choices to render;
`parse` recovers them. Forgetting the annotation is exactly `abstract`, so an `IsoParser` **is** an
`Abs` morphism, packaged with FIRST/FOLLOW for the combinators.

* `Ann : v → Type` is a **family** — one choice-type per value — so `many1`'s "one choice per element"
  is length-correct by construction (as the tokenizer's `Gaps ts` was).
* The annotation is **trivial (`fun _ => PUnit`) exactly when there is no choice**; then this collapses
  to a genuine iso `stream ≃ v` (the old no-annotation `IsoParser`).

Laws: `parse_print` (print a value *with a choice*, parse it back and recover both), `print_parse`
(exactness), `firstOk` (outside FIRST, parse fails). Progress lives in the type, so `run_nil` is free.
-/

namespace LambdaLab.IsoParser

variable {α : Type} {fst fol : α → Bool} {v : Type} {Ann : v → Type}

/-- The FOLLOW condition: `rest` is empty, or its head is admissible. Vacuous at `[]`. -/
def HeadIn (f : α → Bool) (rest : List α) : Prop :=
  ∀ a, rest.head? = some a → f a = true

@[simp] theorem HeadIn_nil (f : α → Bool) : HeadIn f ([] : List α) := by
  intro a h; simp at h

/-- Weaken a FOLLOW condition along `f ≤ g`. -/
theorem HeadIn.mono {f g : α → Bool} (h : ∀ a, f a = true → g a = true)
    {rest : List α} (hr : HeadIn f rest) : HeadIn g rest :=
  fun a ha => h a (hr a ha)

/-- A consuming biparser: a partial iso between streams and `value + annotation`, indexed by
FIRST/FOLLOW and an annotation family `Ann : v → Type`. -/
structure IsoParser (α : Type) (fst fol : α → Bool) (v : Type) (Ann : v → Type) where
  /-- Parse a prefix into a value, its annotation, and a strictly shorter leftover. -/
  parse : (input : List α) →
    Option ((Σ x : v, Ann x) × { r : List α // r.length < input.length })
  /-- Print a value together with a choice of annotation. -/
  print : (x : v) → Ann x → List α
  /-- Outside FIRST, `parse` fails. -/
  firstOk : ∀ (c : α) (rest : List α), fst c = false → parse (c :: rest) = none
  /-- **Round-trip.** Printing a value with a choice, then parsing, recovers both. -/
  parse_print : ∀ (x : v) (a : Ann x) (rest : List α), HeadIn fol rest →
      (parse (print x a ++ rest)).map (fun z => (z.1, z.2.val)) = some (⟨x, a⟩, rest)
  /-- **Exactness.** Whatever `parse` consumed, `print` reproduces exactly. -/
  print_parse : ∀ (input : List α) (xa : Σ x : v, Ann x)
      (r : { r : List α // r.length < input.length }),
      parse input = some (xa, r) → print xa.1 xa.2 ++ r.val = input

/-- The parse result with the progress proof erased. -/
def IsoParser.run (p : IsoParser α fst fol v Ann) (input : List α) :
    Option ((Σ x : v, Ann x) × List α) :=
  (p.parse input).map (fun z => (z.1, z.2.val))

/-- `parse_print`, restated on `run`. -/
theorem IsoParser.run_print (p : IsoParser α fst fol v Ann) (x : v) (a : Ann x) (rest : List α)
    (h : HeadIn fol rest) : p.run (p.print x a ++ rest) = some (⟨x, a⟩, rest) :=
  p.parse_print x a rest h

/-- Fully-consumed round-trip. -/
theorem IsoParser.run_print_nil (p : IsoParser α fst fol v Ann) (x : v) (a : Ann x) :
    p.run (p.print x a) = some (⟨x, a⟩, []) := by
  have h := p.run_print x a [] (HeadIn_nil _)
  rwa [List.append_nil] at h

/-- **Every parser fails on empty input** — a theorem. -/
theorem IsoParser.run_nil (p : IsoParser α fst fol v Ann) : p.run [] = none := by
  simp only [IsoParser.run]
  rcases h : p.parse [] with _ | ⟨a, r, hr⟩
  · rfl
  · exact absurd hr (by simp)

/-- `print` is injective on `value + annotation`: a stream determines both. -/
theorem IsoParser.print_injective (p : IsoParser α fst fol v Ann)
    {x x' : v} {a : Ann x} {a' : Ann x'} (h : p.print x a = p.print x' a') :
    (⟨x, a⟩ : Σ x : v, Ann x) = ⟨x', a'⟩ := by
  have hx := p.run_print_nil x a
  rw [h, p.run_print_nil x' a'] at hx
  exact (congrArg Prod.fst (Option.some.inj hx)).symm

end LambdaLab.IsoParser
