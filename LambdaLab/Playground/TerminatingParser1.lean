/-!
# A parser that always makes at least one step — a "monad without `pure`"

`CParser α` is a parser whose leftover is a **strict** suffix: every value it
produces has consumed ≥1 character. That invariant is exactly what rules out `pure`
(`pure x` would consume nothing), so this type has `Bind` and `Functor` but *no*
`Pure`/`Monad`. `f <$> p` is the "one step, then transform" that replaces
`do let x ← p; return (f x)`.
-/

abbrev CParser (α : Type) :=
  (input : List Char) → Option (α × { r : List Char // r.length < input.length })

/-- Transform the value; consumption is untouched, so progress is preserved. This is
the `return (f x)` you wanted — but as a map, needing no unit. -/
instance : Functor CParser where
  map f p := fun input => (p input).map (fun (a, r) => (f a, r))

/-- Sequence two steps. Both shrink, so the composite shrinks (`r' < r < input`). -/
instance : Bind CParser where
  bind p k := fun input =>
    match p input with
    | none => none
    | some (a, ⟨r, hr⟩) =>
        match k a r with
        | none => none
        | some (b, ⟨r', hr'⟩) => some (b, ⟨r', Nat.lt_trans hr' hr⟩)

-- There is deliberately **no** `Pure CParser`: `pure a` would need
-- `some (a, ⟨input, _ : input.length < input.length⟩)`, which is impossible.

def pChar1 (c : Char) : CParser Char := fun input =>
  match input with
  | [] => none
  | hd :: tl => if hd = c then some (hd, ⟨tl, by simp⟩) else none

-- "one step then transform": exactly your `let x ← p1; return (f x)`, as a map.
def pA : CParser Char := (fun c => c) <$> pChar1 'a'

-- Two steps, combined at the end with a map (no `return`, so no `pure` needed):
def pAB : CParser (List Char) :=
  pChar1 'a' >>= fun x => (fun y => [x, y]) <$> pChar1 'b'

#eval pA "abc".toList |>.map (·.1)          -- some 'a'
#eval pAB "abc".toList |>.map (·.1)         -- some ['a', 'b']
#eval pAB "axc".toList |>.map (·.1)         -- none

/-- One-or-more, with **no** progress hypothesis. The strict-suffix witness `hr` comes
straight from `p`'s `CParser` return type, so it justifies the well-founded recursion
directly — contrast `TerminatingParser.many1`, which had to take `(hp : Progresses p)`.
And `many1 p` is itself a `CParser`: one-or-more still consumes ≥1. -/
def many1 (p : CParser α) (input : List Char) :
    Option (List α × { r : List Char // r.length < input.length }) :=
  match p input with
  | none => none
  | some (a, ⟨r, hr⟩) =>
      match many1 p r with
      | none => some ([a], ⟨r, hr⟩)
      | some (as, ⟨r', hr'⟩) => some (a :: as, ⟨r', Nat.lt_trans hr' hr⟩)
termination_by input.length
decreasing_by exact hr

/-- Zero-or-more falls out for free (may consume nothing, so it is a plain parser, not a
`CParser`). -/
def many (p : CParser α) (input : List Char) : List α × List Char :=
  match many1 p input with
  | none => ([], input)
  | some (as, ⟨r, _⟩) => (as, r)

#eval (many1 (pChar1 'a') ·) "aaab".toList |>.map (·.1)   -- some ['a', 'a', 'a']
#eval (many1 (pChar1 'a') ·) "baa".toList  |>.map (·.1)   -- none (needs ≥1)
#eval (many  (pChar1 'a') ·) "baa".toList  |>.fst         -- []

-- Does Lean's built-in `do` work here (Bind + Functor, no Monad)?
def pAB_do : CParser (List Char) := do
  let x ← pChar1 'a'
  (fun y => [x, y]) <$> pChar1 'b'

/-- `do1` — a `do`-block that *must* take at least one step. Works for any `Bind` +
`Functor` (no `Pure` needed): the leading `let`s become `>>=`, and the trailing
`return e` fuses into the **last** bind as a `<$>` map — so no `pure` is ever emitted,
and a zero-step block can't even be written (the grammar requires ≥1 `let`). Useful for any
"pointed"/non-unital effect where a computation must do work before it can return. -/
syntax "do1 " ("let " ident " ← " term ";"?)+ "return " term : term

macro_rules
  | `(do1 $[let $xs ← $ps $[;]?]* return $e) => do
      let n := xs.size
      let mut acc ← `((fun $(xs[n-1]!) => $e) <$> $(ps[n-1]!))
      for i in [0:n-1] do
        let j := n - 2 - i
        acc ← `($(ps[j]!) >>= fun $(xs[j]!) => $acc)
      return acc

def pAB_do_resulting : CParser (List Char) := do1
  let x ← pChar1 'a'
  let y ← pChar1 'b'
  return [x, y]

#eval pAB_do_resulting "abc".toList |>.map (·.1)   -- some ['a', 'b']

/-! ## `Parser.lean`'s `pDigitLists`, ported to the `CParser` machinery

No `partial`, no `Progresses` proofs, no `Alternative` — `digit1`/`pChar1` carry progress
in their types, `many1` inherits it for free, and `do1 … return` sequences a digit-run and
its `;` terminator. Compare `TerminatingParser.pDigitLists`, which needed a hand-built
`bind_progresses (many1_progresses …) …` progress certificate. -/

def digit1 : CParser Char := fun input =>
  match input with
  | [] => none
  | hd :: tl => if hd.isDigit then some (hd, ⟨tl, by simp⟩) else none

def pDigitList : CParser (List Char) := many1 digit1

def pDigitLists : CParser (List (List Char)) :=
  many1 (do1 let l ← pDigitList; let _s ← pChar1 ';'; return l)

#eval pDigitList  "123".toList        |>.map (·.1)   -- some ['1', '2', '3']
#eval pDigitLists "123;45;6789;".toList |>.map (·.1) -- some [['1','2','3'], ['4','5'], ['6','7','8','9']]
