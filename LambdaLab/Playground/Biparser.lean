
/-- A consuming biparser. Two parameters, because parse and print pull in opposite
directions: `v` is the **value** we parse *into* (covariant), `w` is the **source** we
print *from* (contravariant). The printer returns `v × List Char` — not just the string —
so that `bind` can recover the parsed value from the source. -/
structure CBiparser (w v : Type) where
  parse : (input : List Char) → Option (v × { r : List Char // r.length < input.length })
  print : w → v × List Char

instance : Functor (CBiparser w) where
  map f p := {
    parse := fun input => (p.parse input).map (fun (a, ⟨r, hr⟩) => (f a, ⟨r, hr⟩)),
    print := fun u =>
      let (a, o) := p.print u
      (f a, o)
  }

instance : Bind (CBiparser w) where
  bind p k := {
    -- parse: unchanged — `p.parse` hands us `a`, we pick `k a`, chain the proofs.
    parse input := do
      let (a, ⟨r, hr⟩) ← p.parse input
      let (b, ⟨r', hr'⟩) ← (k a).parse r
      some (b, ⟨r', Nat.lt_trans hr' hr⟩)
    -- print: the source `u : w` is now available and shared by both printers. Running
    -- `p.print u` yields the value `a` we were missing before — which selects `k a` and
    -- lets us print the second half. The `α` hole is filled by the printer's own output.
    print u :=
      let (a, o1) := p.print u
      let (b, o2) := (k a).print u
      (b, o1 ++ o2)
  }

/-- Adapt the **source** (the contravariant slot): `comap f p` prints from `w'` by first
mapping it to `w`; parse ignores the source, so it is untouched. This is what lets a `do1`
block sequence biparsers with *different* sources — you reconcile them to a common one. -/
def comap (f : w' → w) (p : CBiparser w v) : CBiparser w' v where
  parse := p.parse
  print u := p.print (f u)

syntax "do1 " ("let " ident " ← " term ";"?)+ "return " term : term

macro_rules
  | `(do1 $[let $xs ← $ps $[;]?]* return $e) => do
      let n := xs.size
      let mut acc ← `((fun $(xs[n-1]!) => $e) <$> $(ps[n-1]!))
      for i in [0:n-1] do
        let j := n - 2 - i
        acc ← `($(ps[j]!) >>= fun $(xs[j]!) => $acc)
      return acc

/-- A fixed character. Its printing is constant (`c` regardless of source), so the source is
**polymorphic** — it slots into a `do1` block of any source without adaptation. -/
def pChar1 (c : Char) : CBiparser w Char := {
  parse input :=
    match input with
    | [] => none
    | hd :: tl => if hd = c then some (hd, ⟨tl, by simp⟩) else none,
  print := fun _ => (c, [c])
}

/-- Parse side: greedy one-or-more, well-founded on `input.length` (the strict-suffix
witness `hr` comes straight from `p.parse`). Identical to the `CParser` `many1`. -/
def many1Parse (p : CBiparser w α) (input : List Char) :
    Option (List α × { r : List Char // r.length < input.length }) :=
  match p.parse input with
  | none => none
  | some (a, ⟨r, hr⟩) =>
      match many1Parse p r with
      | none => some ([a], ⟨r, hr⟩)
      | some (as, ⟨r', hr'⟩) => some (a :: as, ⟨r', Nat.lt_trans hr' hr⟩)
termination_by input.length
decreasing_by exact hr

/-- Print side: one source per element, folded into concatenated output. Structural
recursion on the source list — no termination proof needed. -/
def many1Print (p : CBiparser w α) : List w → List α × List Char
  | [] => ([], [])
  | u :: us =>
      let (a, o)  := p.print u
      let (as, o') := many1Print p us
      (a :: as, o ++ o')

/-- `many1` for biparsers. The **source type changes** `w → List w`: greedy parse yields a
`List α`, so print needs one `w` per element. Parse and print are *separate* recursions
(parse WF on `input.length`, print structural on the list) bundled into the biparser — a
single self-referential `where`-def can't prove termination, because the recursion lives in
the field arguments (`input`, the list), not in `many1`'s own argument `p`. -/
def many1 (p : CBiparser w α) : CBiparser (List w) (List α) where
  parse := many1Parse p
  print := many1Print p

/-- Digits, as their own type. The source must carry *which* digit to print — but a `Char`
source would be **too wide**: `print 'x'` emits `"x"`, which the parser rejects. Restricting
the source to an inductive `Digit` makes that bad source **unrepresentable** rather than
merely wrong, so no well-formedness side-condition is ever needed downstream. (This is the
same move as `pChar1`'s polymorphic source: the source type is exactly the information the
printer needs, no more and no less.) -/
inductive Digit
  | d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7 | d8 | d9
deriving DecidableEq, Repr

def Digit.toChar : Digit → Char
  | .d0 => '0' | .d1 => '1' | .d2 => '2' | .d3 => '3' | .d4 => '4'
  | .d5 => '5' | .d6 => '6' | .d7 => '7' | .d8 => '8' | .d9 => '9'

def Digit.ofChar? : Char → Option Digit
  | '0' => some .d0 | '1' => some .d1 | '2' => some .d2 | '3' => some .d3 | '4' => some .d4
  | '5' => some .d5 | '6' => some .d6 | '7' => some .d7 | '8' => some .d8 | '9' => some .d9
  | _   => none

/-- A single digit: source *and* value are `Digit`. -/
def digit1 : CBiparser Digit Digit where
  parse input :=
    match input with
    | [] => none
    | hd :: tl =>
        match Digit.ofChar? hd with
        | some d => some (d, ⟨tl, by simp⟩)
        | none => none
  print d := (d, [d.toChar])

/-- A digit run, both directions. Source `List Digit` = the digits to emit. -/
def pDigitList : CBiparser (List Digit) (List Digit) := many1 digit1

/-- `dropWhile` never grows the list — needed to prove progress after skipping a
possibly-empty whitespace run. -/
theorem length_dropWhile_le {α : Type} (p : α → Bool) (l : List α) :
    (l.dropWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
      unfold List.dropWhile
      split
      · simp only [List.length_cons]; omega
      · simp

/-- One-or-more whitespace. Because ≥1 is *required*, the whitespace itself makes progress,
so this is a clean standalone `CBiparser` — no need to fuse it with the following token.
Parsing consumes the maximal whitespace run (≥1); printing emits a single space. Constant
print ⇒ **polymorphic source**, so no adaptation is needed at the use site. -/
def ws1 : CBiparser w Unit where
  parse input :=
    match input with
    | [] => none
    | hd :: tl =>
        if hd.isWhitespace then
          some ((), ⟨tl.dropWhile Char.isWhitespace, by
            have hle := length_dropWhile_le Char.isWhitespace tl
            simp only [List.length_cons]; omega⟩)
        else none
  print _ := ((), [' '])

def pDigitLists : CBiparser (List (List Digit)) (List (List Digit)) :=
  many1 (do1
    let l  ← pDigitList
    let _w ← ws1                         -- ≥1 whitespace, prints one space
    let _s ← pChar1 ';'                  -- the semicolon
    return l)

-- ≥1 whitespace (space or tab) required before each `;`, arbitrarily much accepted:
#eval pDigitLists.parse "12 ;34   ;5\t;".toList |>.map (·.1)
-- some [[d1,d2], [d3,d4], [d5]]
#eval pDigitLists.parse "12;3 ;".toList |>.map (·.1)
-- none  -- "12" has no whitespace before its `;`
-- printing normalises to exactly one space before each `;`; and there is no longer any way
-- to hand it a non-digit source, so the old `print ['x']` failure is now a *type* error:
#eval pDigitLists.print [[.d1, .d2], [.d3]]
-- ([[d1,d2], [d3]], "12 ;3 ;")
