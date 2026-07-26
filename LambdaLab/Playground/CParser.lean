/-!
# `Parser.lean`, made **consuming**

Same content as `Playground/Parser.lean`, but the leftover is *strictly shorter* — and that fact
lives **in the type**:

```
CParser α := (input : List Char) → Option (α × { r // r.length < input.length })
```

Consequences, all forced by the type:

* **`pure` is impossible** — it would return its input as the leftover, which is not shorter. So
  there is no `Monad` instance; only `Bind` (progress composes by transitivity), `Functor`
  (value-only change), and `OrElse` (both branches consume) survive. `do`-blocks still work as
  long as they never use `pure`/`return` — the trailing `pure d` idiom becomes `(fun _ => d) <$> _`.
* **Every parser fails on empty input** — a free theorem (`run_nil`), not a per-parser fact.
* The parsers that *can't* be written are exactly the non-consuming ones: `pure`, optionals,
  `many0`. That's not a loss of expressiveness at the grammar level — it's the type telling you
  those belong to a different (non-consuming) layer.

This is the design step the main library took (`CBiparser`'s subtype leftover, `IsoParser`'s
"progress lives in the type, so `run_nil` is free") — and it is what would make
`RoundTripBiparser.orElse`'s `hpnil` hypothesis derivable instead of assumed.
-/

abbrev CParser (α : Type) :=
  (input : List Char) → Option (α × { r : List Char // r.length < input.length })

/-- **Every consuming parser fails on `[]`** — free: a success would need a leftover shorter than
the empty list. This is also the proof that `pure` cannot exist. -/
theorem CParser.run_nil (p : CParser α) : p [] = none := by
  match hp : p [] with
  | none => rfl
  | some (a, ⟨r, hr⟩) => exact absurd hr (by simp)

/-- Sequencing: progress composes by transitivity (`rest' < rest < input`). No `pure`, so this is
`Bind` alone — not `Monad`. -/
instance : Bind CParser where
  bind p f := fun input =>
    match p input with
    | none => none
    | some (a, ⟨rest, hr⟩) =>
      match f a rest with
      | none => none
      | some (b, ⟨rest', hr'⟩) => some (b, ⟨rest', Nat.lt_trans hr' hr⟩)

/-- Value-only change: the leftover (and its proof) pass through untouched. -/
instance : Functor CParser where
  map f p := fun input => (p input).map (fun ar => (f ar.1, ar.2))

/-- Biased choice: both branches consume, so the result does. -/
instance : OrElse (CParser α) where
  orElse p1 p2 := fun input =>
    match p1 input with
    | some res => some res
    | none => p2 () input

def pChar (c : Char) : CParser Unit := fun input =>
  match input with
  | [] => none
  | h :: t => if h = c then some ((), ⟨t, by simp⟩) else none

def pAB : CParser Unit := do
  pChar 'A'
  pChar 'B'

abbrev Digit := {c : Char // c.isDigit}

def pDigit : CParser Digit := fun input =>
  match input with
  | [] => none
  | h :: t => if Heq : h.isDigit then some (⟨h, Heq⟩, ⟨t, by simp⟩) else none

def pADigit : CParser Digit := do
  pChar 'A'
  pDigit

/-- The trailing `pure d` of the original is unavailable (no `Pure`); keep the digit through the
final `pChar` with `Functor.map` instead. -/
def pDigitB : CParser Digit := do
  let d ← pDigit
  (fun _ => d) <$> pChar 'B'

def pAAOrDigitB : CParser Digit := pADigit <|> pDigitB

#eval pAAOrDigitB ['A', '1', 'C'] -- some (⟨'1', _⟩, ['C'])
#eval pAAOrDigitB ['3', 'B', 'C'] -- some (⟨'3', _⟩, ['C'])
#eval pAAOrDigitB ['x', 'y']      -- none
#eval pAAOrDigitB []              -- none  (free: `run_nil`)

example : pAAOrDigitB [] = none := CParser.run_nil _

/-! ## `fix` — recursion, legitimately

In the *law-carrying* frameworks a `fix` combinator is unsound: the recursive reference's law only
holds on shorter inputs, and bundling a partial law leaks a `sorry` — there, recursion must be a
hand-written WF `def` with the law proved by induction. Here there is no law, so the recursor is
just **code** — and the consuming type makes it a genuine `CParser`: the strictly-shorter guard is
exactly what the type already demands. So all the combinators (`do`, `<|>`, `<$>`) apply to the
recursive reference directly.

Termination is strong recursion on the input length: the guard hands the body a recursor that
*fails* (rather than loops) on non-shorter inputs — an ill-founded grammar degrades to `none`. -/

-- `h` reads as unused: it is consumed only in `decreasing_by`.
set_option linter.unusedVariables false in
/-- A literal fixpoint of a parser transformer. The body never sees the input: the result type's
"leftover shorter than the input" dependency is carried by `CParser`'s own pi type, and the
strictly-shorter guard lives in the implementation. (The library's `fix2` threads the input into
the body only because its *law machinery* needs per-input step-laws — law-free, it can go.) -/
def fix (body : CParser α → CParser α) : CParser α
  | input =>
    body (fun input' =>
      if h : input'.length < input.length then fix body input' else none) input
termination_by input => input.length
decreasing_by exact h

/-- `P ::= 'a' | '(' P ')'` — value = nesting depth, written **entirely from combinators**, with
`self` used like any other `CParser`. (Compare `RoundTripBiparser`'s `pParens`, where the same
grammar needed a standalone recursive `def` and an induction.) -/
def pParens : CParser Nat :=
  fix fun self =>
    ((fun _ => 0) <$> pChar 'a')
      <|>
    (do
      pChar '('
      let n ← self
      (fun _ => n + 1) <$> pChar ')')

#eval pParens "a".toList      -- some (0, [])
#eval pParens "((a))".toList  -- some (2, [])
#eval pParens "((a)".toList   -- none      (unclosed)
#eval pParens "(a))x".toList  -- some (1, [')', 'x'])
#eval pParens []              -- none      (free: `run_nil`)

/-- And it composes like any other piece: `'[' P ']'`. -/
def pBracketParens : CParser Nat := do
  pChar '['
  let n ← pParens
  (fun _ => n) <$> pChar ']'

#eval pBracketParens "[((a))]".toList -- some (2, [])
