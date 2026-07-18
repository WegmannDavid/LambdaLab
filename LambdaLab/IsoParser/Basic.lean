/-!
# `IsoParser` — a consuming biparser forced to be a partial isomorphism

`CBiparser` with two guarantees tightened into the type, so `parse` and `print` are genuine mutual
inverses, plus **FIRST/FOLLOW carried as indices** (as in `IBip`) so combinators can state their
seams without threading a side predicate.

Changes from `CBiparser α w v`:

1. **One value type, `print : v → List α`.** Source and value coincide (`v`); `print` returns only
   the tokens it consumes — no value slot for a printer to relabel, so relabeling is unrepresentable.

2. **Both round-trip directions are laws:**
   * `parse_print` — printing then parsing recovers the value, leaving any `FOLLOW`-admissible `rest`
     (`HeadIn fol rest`) untouched;
   * `print_parse` — whatever `parse` consumed, `print` reproduces exactly (unconditional).

3. **`firstOk`** — outside `FIRST`, `parse` fails; the negative claim that lets `many1`/sequencing
   know a sub-parser stops.

At `rest = []` (`HeadIn_nil`) the round-trip is unconditional, giving a bijection `v ≃ { c // run c =
some (·, []) }` between fully-parsed streams and outputs. Progress lives in the type, so `run_nil` is
free.
-/

namespace LambdaLab.IsoParser

variable {α : Type} {fst fol : α → Bool} {v : Type}

/-- The FOLLOW condition: `rest` is empty, or its head is admissible. Vacuous at `[]`. -/
def HeadIn (f : α → Bool) (rest : List α) : Prop :=
  ∀ a, rest.head? = some a → f a = true

@[simp] theorem HeadIn_nil (f : α → Bool) : HeadIn f ([] : List α) := by
  intro a h; simp at h

/-- Weaken a FOLLOW condition along `f ≤ g`. -/
theorem HeadIn.mono {f g : α → Bool} (h : ∀ a, f a = true → g a = true)
    {rest : List α} (hr : HeadIn f rest) : HeadIn g rest :=
  fun a ha => h a (hr a ha)

/-- A consuming biparser that is a partial isomorphism between input streams and outputs, indexed by
its FIRST and FOLLOW sets. -/
structure IsoParser (α : Type) (fst fol : α → Bool) (v : Type) where
  /-- Parse a prefix, returning the value and a *strictly shorter* leftover. -/
  parse : (input : List α) → Option (v × { r : List α // r.length < input.length })
  /-- Print a value to exactly the tokens it occupies — no value slot, hence no relabeling. -/
  print : v → List α
  /-- Outside FIRST, `parse` fails. -/
  firstOk : ∀ (c : α) (rest : List α), fst c = false → parse (c :: rest) = none
  /-- **Round-trip.** Printing then parsing recovers the value, leaving any admissible `rest`. -/
  parse_print : ∀ (a : v) (rest : List α), HeadIn fol rest →
      (parse (print a ++ rest)).map (fun x => (x.1, x.2.val)) = some (a, rest)
  /-- **Exactness.** Whatever `parse` consumed, `print` reproduces exactly. -/
  print_parse : ∀ (input : List α) (a : v) (r : { r : List α // r.length < input.length }),
      parse input = some (a, r) → print a ++ r.val = input

/-- The parse result with the progress proof erased. The clean laws are stated against `run`. -/
def IsoParser.run (p : IsoParser α fst fol v) (input : List α) : Option (v × List α) :=
  (p.parse input).map (fun x => (x.1, x.2.val))

/-- `parse_print`, restated on `run`. -/
theorem IsoParser.run_print (p : IsoParser α fst fol v) (a : v) (rest : List α)
    (h : HeadIn fol rest) : p.run (p.print a ++ rest) = some (a, rest) :=
  p.parse_print a rest h

/-- Fully-consumed round-trip: `run (print a) = some (a, [])`. -/
theorem IsoParser.run_print_nil (p : IsoParser α fst fol v) (a : v) :
    p.run (p.print a) = some (a, []) := by
  have h := p.run_print a [] (HeadIn_nil _)
  rwa [List.append_nil] at h

/-- **Every parser fails on empty input** — a theorem: the leftover would need length `< 0`. -/
theorem IsoParser.run_nil (p : IsoParser α fst fol v) : p.run [] = none := by
  simp only [IsoParser.run]
  rcases h : p.parse [] with _ | ⟨a, r, hr⟩
  · rfl
  · exact absurd hr (by simp)

/-- `print` is injective — the forward half of the bijection onto fully-parsed streams. -/
theorem IsoParser.print_injective (p : IsoParser α fst fol v) : Function.Injective p.print := by
  intro a b h
  have ha := p.run_print_nil a
  rw [h, p.run_print_nil b] at ha
  exact (congrArg Prod.fst (Option.some.inj ha)).symm

end LambdaLab.IsoParser
