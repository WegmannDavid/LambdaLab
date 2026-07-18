import LambdaLab.IsoParser.Combinators

/-!
# Concrete grammar built from IsoParser combinators — validation

`number (+ number)*`, left-associative, built purely from `sat`/`tok`/`many1`/`seq`/`chainl`. No
recursion (no parens), so the round-trip and exactness laws come **entirely from the combinators** —
zero sorries, no `parseExpr_exact`. `#eval` confirms the round-trip.
-/

namespace LambdaLab.IsoParser.Arith

open LambdaLab.IsoParser

abbrev Digit := { c : Char // c.isDigit = true }

/-- One or more digits. -/
def number := many1 (sat Char.isDigit) (fun _ _ => rfl)

/-- `+ number`. -/
def addStep := seq (tok '+') number (fun _ _ => rfl)

/-- `number (+ number)*`, left-associative (structural value `NEList Digit × List (Unit × …)`). -/
def expr := chainl number addStep
  (fun c hc => by have hc' : c = '+' := (by simpa using hc); subst hc'; decide)

/-- Round-trip a fully-consumed string through the parsed value + annotation. -/
def roundtrip (s : String) : Option String :=
  match expr.run s.toList with
  | some (⟨v, a⟩, []) => some (String.ofList (expr.print v a))
  | _ => none

#eval roundtrip "1+2+3"     -- some "1+2+3"
#eval roundtrip "42"        -- some "42"
#eval roundtrip "1+2"       -- some "1+2"
#eval roundtrip "7+80+900"  -- some "7+80+900"
#eval roundtrip "1++2"      -- none  (malformed)
#eval roundtrip "+1"        -- none

/-! ## With precedence — `expr = term (+ term)*`, `term = number (* number)*` (`*` binds tighter) -/

/-- `* number`. -/
def mulStep := seq (tok '*') number (fun _ _ => rfl)

/-- `number (* number)*`. -/
def term := chainl number mulStep
  (fun c hc => by have hc' : c = '*' := (by simpa using hc); subst hc'; decide)

/-- `+ term`. -/
def addStepT := seq (tok '+') term (fun _ _ => rfl)

/-- `term (+ term)*` — full two-level precedence grammar. -/
def exprPrec := chainl term addStepT
  (fun c hc => by have hc' : c = '+' := (by simpa using hc); subst hc'; decide)

def roundtripP (s : String) : Option String :=
  match exprPrec.run s.toList with
  | some (⟨v, a⟩, []) => some (String.ofList (exprPrec.print v a))
  | _ => none

#eval roundtripP "1+2*3"    -- some "1+2*3"  (parses as 1+(2*3), prints back)
#eval roundtripP "2*3+4"    -- some "2*3+4"
#eval roundtripP "1*2*3"    -- some "1*2*3"
#eval roundtripP "1+2+3"    -- some "1+2+3"
#eval roundtripP "10*20+30*40"  -- some "10*20+30*40"

end LambdaLab.IsoParser.Arith
