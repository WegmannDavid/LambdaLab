import LambdaLab.IsoParser.Notation

/-!
# Concrete grammar built from IsoParser combinators — validation

`number (+ number)*`, left-associative, built purely from `sat`/`tok`/`many1`/`gdo`/`chainl`. No
recursion (no parens), so the round-trip law comes **entirely from the combinators** — zero
sorries. Both parsers are **aligned** (source type = value type), so a parsed value can be
re-printed directly and `#eval` confirms the round-trip.
-/

namespace LambdaLab.IsoParser.Arith

open LambdaLab.IsoParser

abbrev Digit := { c : Char // c.isDigit = true }

/-- One or more digits. -/
def number := many1 (sat Char.isDigit) (fun _ _ => trivial)

/-- `+ number`. -/
def addStep : IsoParser Char (· = '+') (fun c => True ∧ ¬ c.isDigit = true)
    (NEList Digit) (NEList Digit) := gdo
  let _p ← tok '+'
  let n ← number
  return n

/-- `number (+ number)*`, left-associative (structural value: seed × steps). -/
def expr := chainl number addStep
  (by intro c hc; subst hc; exact ⟨trivial, by decide⟩)

/-- Round-trip a fully-consumed string through the parsed value (aligned, so it re-prints). -/
def roundtrip (s : String) : Option String :=
  match expr.run s.toList with
  | some (v, []) => some (String.ofList (expr.print v).2)
  | _ => none

#eval roundtrip "1+2+3"     -- some "1+2+3"
#eval roundtrip "42"        -- some "42"
#eval roundtrip "7+80+900"  -- some "7+80+900"
#eval roundtrip "1++2"      -- none  (malformed)
#eval roundtrip "+1"        -- none

/-! ## With precedence — `expr = term (+ term)*`, `term = number (* number)*` -/

/-- `* number`. -/
def mulStep : IsoParser Char (· = '*') (fun c => True ∧ ¬ c.isDigit = true)
    (NEList Digit) (NEList Digit) := gdo
  let _p ← tok '*'
  let n ← number
  return n

/-- `number (* number)*`. -/
def term := chainl number mulStep
  (by intro c hc; subst hc; exact ⟨trivial, by decide⟩)

/-- `+ term`. -/
def addStepT : IsoParser Char (· = '+')
    (fun c => (True ∧ ¬ c.isDigit = true) ∧ ¬ c = '*')
    (NEList Digit × List (NEList Digit)) (NEList Digit × List (NEList Digit)) := gdo
  let _p ← tok '+'
  let t ← term
  return t

/-- `term (+ term)*` — full two-level precedence grammar. -/
def exprPrec := chainl term addStepT
  (by intro c hc; subst hc; exact ⟨⟨trivial, by decide⟩, by decide⟩)

def roundtripP (s : String) : Option String :=
  match exprPrec.run s.toList with
  | some (v, []) => some (String.ofList (exprPrec.print v).2)
  | _ => none

#eval roundtripP "1+2*3"        -- some "1+2*3"  (parses as 1+(2*3), prints back)
#eval roundtripP "2*3+4"        -- some "2*3+4"
#eval roundtripP "1*2*3"        -- some "1*2*3"
#eval roundtripP "10*20+30*40"  -- some "10*20+30*40"

end LambdaLab.IsoParser.Arith
