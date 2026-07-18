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

/-- Parse a nesting, well-founded recursion on input length (a concrete instance of `fixParse`;
written directly so its equation lemmas drive the law proofs). -/
def parseParen : (input : List Char) → Option (Paren × { r : List Char // r.length < input.length })
  | [] => none
  | c :: rest =>
    if c = 'x' then some (.leaf, ⟨rest, by simp⟩)
    else if c = '(' then
      match parseParen rest with
      | some (p, r) =>
        match hr : r.val with
        | ')' :: r2 => some (.nest p, ⟨r2, by
            have := r.property; rw [hr] at this
            simp only [List.length_cons] at this ⊢; omega⟩)
        | _ => none
      | none => none
    else none
  termination_by input => input.length
  decreasing_by simp_wf

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

/-! ## Unfolding lemmas for `parseParen` (the WF `fix` equation, at each head token) -/

theorem parseParen_x (rest : List Char) :
    parseParen ('x' :: rest) = some (Paren.leaf, ⟨rest, by simp⟩) := by
  simp [parseParen]

theorem parseParen_open (rest : List Char) :
    parseParen ('(' :: rest) =
      (match parseParen rest with
        | some (p, r) =>
          match hr : r.val with
          | ')' :: r2 => some (Paren.nest p, ⟨r2, by
              have := r.property; rw [hr] at this
              simp only [List.length_cons] at this ⊢; omega⟩)
          | _ => none
        | none => none) := by
  rw [parseParen]; rw [if_neg (by decide), if_pos rfl]

theorem parseParen_other (c : Char) (rest : List Char) (hx : c ≠ 'x') (hp : c ≠ '(') :
    parseParen (c :: rest) = none := by
  rw [parseParen]; rw [if_neg hx, if_neg hp]

end LambdaLab.IsoParser
