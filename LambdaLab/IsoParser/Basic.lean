/-!
# `IsoParser` — a consuming biparser forced to be a partial isomorphism

This is `CBiparser` with two guarantees tightened into the type, so that `parse` and `print` are
genuine mutual inverses rather than merely round-tripping in one direction.

Two changes from `CBiparser α w v`:

1. **One value type, and `print : v → List α`.** Source and value coincide (`v`), and `print`
   returns *only the tokens it consumes* — there is no value slot for the printer to fill with a
   relabelled value, so relabeling is unrepresentable.

2. **Both round-trip directions are laws:**
   * `parse_print` — printing then parsing recovers the value with nothing left over;
   * `print_parse` — whatever `parse` consumes, `print` reproduces exactly.

   Together they make `print` a bijection `v ≃ { c // run c = some (·, []) }` onto the
   **fully-parsed streams**: the isomorphism between input stream and output.

As in `CBiparser`, progress lives in the type — the leftover is a *strict* suffix — so termination
is free and `run_nil` (every parser fails on empty input) is a theorem, not an assumption.

`print_parse` is stated on the raw `parse` (it is unconditional). `parse_print` is stated via the
progress-erased `run`-shape `(parse ·).map …`, because `run` cannot be named before the structure it
projects from; `run` and the clean restatements follow immediately after.
-/

namespace LambdaLab.IsoParser

variable {α v : Type}

/-- A consuming biparser that is a partial isomorphism between input streams and outputs. -/
structure IsoParser (α : Type) (v : Type) where
  /-- Parse a prefix, returning the value and a *strictly shorter* leftover. -/
  parse : (input : List α) → Option (v × { r : List α // r.length < input.length })
  /-- Print a value to exactly the tokens it occupies — no value slot, hence no relabeling. -/
  print : v → List α
  /-- **Round-trip.** Printing then parsing recovers the value with empty leftover. -/
  parse_print : ∀ a, (parse (print a)).map (fun x => (x.1, x.2.1)) = some (a, [])
  /-- **Exactness.** Whatever `parse` consumed, `print` reproduces exactly. -/
  print_parse : ∀ input a r, parse input = some (a, r) → print a ++ r.val = input

/-- The parse result with the progress proof erased. All the clean laws are stated against `run`. -/
def IsoParser.run (p : IsoParser α v) (input : List α) : Option (v × List α) :=
  (p.parse input).map (fun x => (x.1, x.2.val))

/-- **Every parser fails on empty input** — a theorem: the leftover would need length `< 0`. -/
theorem IsoParser.run_nil (p : IsoParser α v) : p.run [] = none := by
  simp only [IsoParser.run]
  rcases h : p.parse [] with _ | ⟨a, r, hr⟩
  · rfl
  · exact absurd hr (by simp)

/-- `parse_print`, restated on `run`: printing then running recovers the value, fully consumed. -/
theorem IsoParser.run_print (p : IsoParser α v) (a : v) : p.run (p.print a) = some (a, []) :=
  p.parse_print a

/-- `print` is injective — the forward half of the bijection onto fully-parsed streams. -/
theorem IsoParser.print_injective (p : IsoParser α v) : Function.Injective p.print := by
  intro a b h
  have ha := p.run_print a
  rw [h, p.run_print b] at ha
  exact (congrArg Prod.fst (Option.some.inj ha)).symm

end LambdaLab.IsoParser
