import LambdaLab.IsoParser.Basic

/-!
# `fixParse` — the well-founded recursion core for recursive grammars

Recursive grammars (parens, cross-entry holes) can't be static combinator *values* in a total
language — the definition would be cyclic. The escape is recursion on **input length**: the body gets
a recursor callable only on strictly-shorter input, so it must consume before recursing.

`fixParse` is that core (the parse side). Wrapping it as a law-carrying `IsoParser` — proving
`parse_print` by induction on the value and `print_parse` by induction on input length — is the
remaining `fix` combinator; this pins down the compute first.
-/

namespace LambdaLab.IsoParser

variable {α : Type}

/-- Define a parser by well-founded recursion on input length. The body receives a recursor valid
only on strictly-shorter inputs. -/
def fixParse {v : Type}
    (body : (input : List α) →
      ((input' : List α) → input'.length < input.length →
        Option (v × { r : List α // r.length < input'.length })) →
      Option (v × { r : List α // r.length < input.length })) :
    (input : List α) → Option (v × { r : List α // r.length < input.length })
  | input => body input (fun input' _ => fixParse body input')
  termination_by input => input.length
  decreasing_by exact ‹_›

/-! ## Demonstration: nested parens `( ( x ) )`, a genuinely recursive grammar -/

/-- A nesting: a leaf `x`, or a parenthesized nesting. -/
inductive Paren where
  | leaf : Paren
  | nest : Paren → Paren
  deriving Repr

/-- Structural print. -/
def Paren.flatten : Paren → List Char
  | .leaf   => ['x']
  | .nest p => '(' :: (p.flatten ++ [')'])

/-- Parse a nesting, recursion on input length via `fixParse`. -/
def parseParen : (input : List Char) → Option (Paren × { r : List Char // r.length < input.length }) :=
  fixParse (fun input rec =>
    match input with
    | 'x' :: rest => some (.leaf, ⟨rest, by simp⟩)
    | '(' :: rest =>
      match h : rec rest (by simp) with
      | some (p, r) =>
        match hr : r.val with
        | ')' :: r2 => some (.nest p, ⟨r2, by
            have := r.property
            rw [hr] at this
            simp only [List.length_cons] at this ⊢
            omega⟩)
        | _ => none
      | none => none
    | _ => none)

/-- Round-trip a nesting string. -/
def parenRoundtrip (s : String) : Option String :=
  match parseParen s.toList with
  | some (p, r) => if r.val = [] then some (String.ofList p.flatten) else none
  | _ => none

#eval parenRoundtrip "x"        -- some "x"
#eval parenRoundtrip "(x)"      -- some "(x)"
#eval parenRoundtrip "((x))"    -- some "((x))"
#eval parenRoundtrip "(((x)))"  -- some "(((x)))"
#eval parenRoundtrip "((x)"     -- none  (unbalanced)
#eval parenRoundtrip "(y)"      -- none

end LambdaLab.IsoParser
