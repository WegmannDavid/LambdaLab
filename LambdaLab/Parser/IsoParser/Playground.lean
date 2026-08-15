import LambdaLab.Parser.IsoParser.Notation

namespace LambdaLab.Parser.IsoParser.Playground

open LambdaLab.Parser.IsoParser

/-! # Playground

## example 1: parse a digit, then `=`, then a digit -/

abbrev Digit := { c : Char // c.isDigit = true }

structure Binding where
  lhs : Digit
  rhs : Digit
  deriving Repr

/-- `gdo` sequences the three pieces monadically; `comap` gives each digit its slice of the
source, and `tok`'s source is polymorphic (keywords need no adaptation). -/
def binding : IsoParser Char (fun c => c.isDigit = true) (fun _ => True) Binding Binding := gdo
  let l ← comap Binding.lhs (sat Char.isDigit)
  let _eq ← tok '='
  let r ← comap Binding.rhs (sat Char.isDigit)
  return Binding.mk l r

/-- Print the parsed value back and check it matches (fully consumed; aligned, so the parsed
value re-prints directly). -/
def roundtrip (s : String) : Option String :=
  match binding.run s.toList with
  | some (v, []) => some (String.ofList (binding.print v).2)
  | _ => none

/-! ## example 2: just the two digits — `(Digit × Digit)`, no record -/

def twoDigits : IsoParser Char (fun c => c.isDigit = true) (fun _ => True)
    (Digit × Digit) (Digit × Digit) := gdo
  let a ← comap Prod.fst (sat Char.isDigit)
  let _eq ← tok '='
  let b ← comap Prod.snd (sat Char.isDigit)
  return (a, b)

-- …and it still round-trips: the printer puts the `=` back
def roundtrip2 (s : String) : Option String :=
  match twoDigits.run s.toList with
  | some (v, []) => some (String.ofList (twoDigits.print v).2)
  | _ => none

end LambdaLab.Parser.IsoParser.Playground
