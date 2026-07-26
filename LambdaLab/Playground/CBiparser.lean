/-!
# `Biparser.lean`, made **consuming**

Same content as `Playground/Biparser.lean` (the monadic-profunctor biparser: source `α`, value
`β`, `comap`, `HOrElse` — no law), but the parse side is *consuming*: the leftover is strictly
shorter, in the type — exactly as in `CParser.lean`. This is precisely the main library's
`CBiparser` shape (the "C" is this).

`print` is untouched: consuming is a parse-side notion. (The print-side dual — "printed output is
nonempty" — is *not* imposed here; adding it is part of what makes the round-trip law provable
for alternation, as `RoundTripBiparser`'s `orElse` showed.)

Casualties, forced by the type, same as `CParser.lean`:

* **`pure` is impossible** (leftover = input is not shorter) ⇒ no `Monad`; `Bind` (progress
  composes by transitivity) + `Functor` (value-only change) survive, and `do` still works when no
  `pure`/`return` appears. The trailing `pure d` idiom becomes `(fun _ => d) <$> _`.
* **`run_nil` is a free theorem**: every consuming biparser fails to parse `[]`.
-/

structure CBiparser (α β : Type) where
  parse : (input : List Char) → Option (β × { r : List Char // r.length < input.length })
  print : α → β × List Char

/-- Every consuming biparser fails on `[]` — free (a success would need a shorter-than-empty
leftover). Also the proof that `pure` cannot exist. -/
theorem CBiparser.run_nil (p : CBiparser α β) : p.parse [] = none := by
  match hp : p.parse [] with
  | none => rfl
  | some (b, ⟨r, hr⟩) => exact absurd hr (by simp)

/-- Sequencing over a shared source: parse-side progress composes by transitivity; print-side both
components print from the same source `b`, outputs concatenated (the monadic-profunctor bind). -/
instance : Bind (CBiparser α) where
  bind p f := {
    parse := fun input =>
      match p.parse input with
      | none => none
      | some (a, ⟨rest, hr⟩) =>
        match (f a).parse rest with
        | none => none
        | some (b, ⟨rest', hr'⟩) => some (b, ⟨rest', Nat.lt_trans hr' hr⟩),
    print := fun b =>
      let (a, out) := p.print b
      let (c, out') := (f a).print b
      (c, out ++ out')
  }

/-- Value-only change, on both sides; the leftover passes through untouched. -/
instance : Functor (CBiparser α) where
  map f p := {
    parse := fun input => (p.parse input).map (fun br => (f br.1, br.2)),
    print := fun a =>
      let (b, out) := p.print a
      (f b, out)
  }

def pChar (c : Char) : CBiparser α Unit := {
  parse := fun input =>
    match input with
    | [] => none
    | h :: t => if h = c then some ((), ⟨t, by simp⟩) else none,
  print := fun _ => ((), [c])
}

def pAB : CBiparser Unit Unit := do
  pChar 'A'
  pChar 'B'

#eval pAB.parse ['A', 'B', 'C'] -- some ((), ['C'])
#eval pAB.print () -- ((), ['A', 'B'])

abbrev Digit := {c : Char // c.isDigit}

def pDigit : CBiparser Digit Digit := {
  parse := fun input =>
    match input with
    | [] => none
    | h :: t => if Heq : h.isDigit then some (⟨h, Heq⟩, ⟨t, by simp⟩) else none,
  print := fun d => (d, [d.val])
}

/-- The original's trailing `pure d` becomes `(fun _ => d) <$> pChar 'B'` (no `Pure`). -/
def pADigitB : CBiparser Digit Digit := do
  pChar 'A'
  let d ← pDigit
  (fun _ => d) <$> pChar 'B'

#eval pADigitB.parse ['A', '1', 'B', '2'] -- some (⟨'1', _⟩, ['2'])
#eval pADigitB.print ⟨'1', by decide⟩ -- (⟨'1', _⟩, ['A', '1', 'B'])

/-- Adapt the **source**: parse ignores the source, so only `print` changes. -/
def comap (g : α' → α) (p : CBiparser α β) : CBiparser α' β := {
  parse := p.parse,
  print := fun a' => p.print (g a')
}

def pADigitBDigit : CBiparser (Digit × Digit) (Digit × Digit) := do
  pChar 'A'
  let d1 ← comap Prod.fst pDigit
  pChar 'B'
  let d2 ← comap Prod.snd pDigit
  (fun _ => (d1, d2)) <$> pChar 'C'

#eval pADigitBDigit.parse ['A', '5', 'B', '6', 'C', '3'] -- some ((⟨'5', _⟩, ⟨'6', _⟩), ['3'])
#eval pADigitBDigit.print (⟨'5', by decide⟩, ⟨'6', by decide⟩) -- ((…), ['A', '5', 'B', '6', 'C'])

instance : HOrElse (CBiparser α β) (CBiparser γ δ) (CBiparser (α ⊕ γ) (β ⊕ δ)) where
  hOrElse p1 p2 := {
    parse := fun input =>
      match p1.parse input with
      | some (b, rest) => some (Sum.inl b, rest)
      | none =>
        match (p2 ()).parse input with
        | some (c, rest) => some (Sum.inr c, rest)
        | none => none,
    print := fun a =>
      match a with
      | Sum.inl a' => let (b, out) := p1.print a'; (Sum.inl b, out)
      | Sum.inr a' => let (c, out) := (p2 ()).print a'; (Sum.inr c, out)
  }

def pADigit : CBiparser Digit Digit := do
  pChar 'A'
  pDigit

def pDigitB : CBiparser Digit Digit := do
  let d ← pDigit
  (fun _ => d) <$> pChar 'B'

def pAAOrDigitB : CBiparser (Digit ⊕ Digit) (Digit ⊕ Digit) := pADigit <|> pDigitB

#eval pAAOrDigitB.parse ['A', '1', 'C'] -- some (Sum.inl '1', ['C'])
#eval pAAOrDigitB.parse ['3', 'B', 'C'] -- some (Sum.inr '3', ['C'])
#eval pAAOrDigitB.parse [] -- none  (free: `run_nil`)
#eval pAAOrDigitB.print (Sum.inl ⟨'1', by decide⟩) -- (Sum.inl '1', ['A', '1'])
#eval pAAOrDigitB.print (Sum.inr ⟨'3', by decide⟩) -- (Sum.inr '3', ['3', 'B'])

example : pAAOrDigitB.parse [] = none := CBiparser.run_nil _

/-! ## `fix` — recursion, on **both** sides

The parse side is `CParser`'s `fix`: the consuming type supplies the termination measure (input
length), and the guarded recursor is a genuine parser. The **print side is the asymmetry**: it
recurses on the *source*, and an abstract `α` carries no measure — so `fix` must ask for one
(`μ : α → Nat`), and since `print` is total (no `none` channel), also a fallback value for
ill-founded print calls. (This is why the library's printers — `flatten` — never need a `fix`:
they are structural recursions on inductive trees, where the measure is the tree itself.)

The recursor handed to the body is assembled per side: while *parsing*, its `print` field is junk;
while *printing*, its `parse` field is junk. Any combinator-built body is **componentwise** (its
parse uses only `self.parse`, its print only `self.print`), so the junk is never touched. -/

-- `h` reads as unused: it is consumed only in `decreasing_by`.
set_option linter.unusedVariables false in
def fixParse (dflt : β) (body : CBiparser α β → CBiparser α β) :
    (input : List Char) → Option (β × { r : List Char // r.length < input.length })
  | input =>
    (body {
      parse := fun input' =>
        if h : input'.length < input.length then fixParse dflt body input' else none,
      print := fun _ => (dflt, []) }).parse input
termination_by input => input.length
decreasing_by exact h

set_option linter.unusedVariables false in
def fixPrint (μ : α → Nat) (dflt : β) (body : CBiparser α β → CBiparser α β) :
    α → β × List Char
  | a =>
    (body {
      parse := fun _ => none,
      print := fun a' =>
        if h : μ a' < μ a then fixPrint μ dflt body a' else (dflt, []) }).print a
termination_by a => μ a
decreasing_by exact h

/-- The fixpoint of a biparser transformer: parse-side measured by consumption (free, from the
type), print-side by the supplied `μ` on the source. -/
def fix (μ : α → Nat) (dflt : β) (body : CBiparser α β → CBiparser α β) : CBiparser α β := {
  parse := fixParse dflt body,
  print := fixPrint μ dflt body
}

/-- The recursive body of `P ::= 'a' | '(' P ')'`, source = value = nesting depth. The source is
*dispatched* into the `<|>` sum by `comap` (depth `0` ↦ the `'a'` branch, `m+1` ↦ the paren branch
printing from `m`), and the value sum is collapsed back by `Sum.elim`. -/
def parensBody (self : CBiparser Nat Nat) : CBiparser Nat Nat :=
  Sum.elim id id <$>
    comap (fun a : Nat => match a with | 0 => Sum.inl () | m + 1 => Sum.inr m)
      (((fun _ => (0 : Nat)) <$> (pChar 'a' : CBiparser Unit Unit))
        <|>
       (do
         pChar '('
         let n ← self
         (fun _ => n + 1) <$> pChar ')'))

/-- `μ = id` is *valid* for this body: the paren branch prints `self` from `m` at source `m+1`. -/
def pParens : CBiparser Nat Nat := fix id 0 parensBody

#eval pParens.parse "a".toList      -- some (0, [])
#eval pParens.parse "((a))".toList  -- some (2, [])
#eval pParens.parse "((a)".toList   -- none
#eval pParens.print 0               -- (0, ['a'])
#eval pParens.print 3               -- (3, ['(', '(', '(', 'a', ')', ')', ')'])
#eval pParens.parse (pParens.print 4).2 -- some (4, [])   (round-trips — though here only observed, not proved)

/-! ### A *wrong* `μ` — what actually breaks

`μ` is a semantic contract, not a checked obligation: the guard enforces termination for **any**
`μ`, and Lean verifies nothing about its validity. With `μ = fun _ => 0` the body's recursive
print never satisfies the guard, so every recursive call silently returns the fallback — the
printed text is junk, and the round trip fails *observably, at run time*. The parse side is a
separate recursion with its own (canonical, always-valid) measure, so parsing is untouched.

This silent wrongness is exactly what the law-carrying framework turns into an unprovable `ok`
obligation at definition time — and why `fix` + bundled law is the hard combination. -/

def pParensBad : CBiparser Nat Nat := fix (fun _ => 0) 0 parensBody

#eval pParensBad.parse "((a))".toList -- some (2, [])   parse: unaffected by μ
#eval pParensBad.print 3 -- (1, ['(', ')'])   print: fallback fired — junk text, junk value
#eval pParensBad.parse (pParensBad.print 3).2 -- none   the round trip, visibly broken
