import LambdaLab.IsoParser.Combinators

/-!
# Example: semicolon-terminated digit lists

Parsing/printing `"1234;567;89;"` as a `NEList (NEList Digit)` — an isomorphism between the string and
the parsed structure, built entirely from verified combinators. No whitespace: the `;` separators do
all the delimiting, and each digit run stops exactly at the non-digit `;`.

    file   = many1 group                 -- one or more groups
    group  = number <; ';'               -- digits then a terminating ';'
    number = many1 (sat isDigit)         -- one or more digits
-/

namespace LambdaLab.IsoParser.Example

open LambdaLab.IsoParser

/-- A single decimal digit, carrying its proof. -/
abbrev Digit := { c : Char // c.isDigit = true }

/-- One or more digits. FOLLOW = "not a digit". -/
def number := many1 (sat Char.isDigit) (fun _ _ => rfl)

/-- A digit run terminated by `;`, with the unit dropped. FIRST = digit, FOLLOW = ⊤. -/
def group : IsoParser Char Char.isDigit (fun _ => true) (NEList Digit) :=
  imap Prod.fst (fun d => (d, ()))
    (fun x => by obtain ⟨a, u⟩ := x; cases u; rfl) (fun _ => rfl)
    (seq number (tok ';') (fun c hc => by
      have : c = ';' := by simpa using hc
      subst this; decide))

/-- One or more `;`-terminated digit groups. -/
def file : IsoParser Char Char.isDigit (fun c => !Char.isDigit c) (NEList (NEList Digit)) :=
  many1 group (fun _ _ => rfl)

/-- Parse a whole string (must be fully consumed). -/
def parse (s : String) : Option (NEList (NEList Digit)) :=
  match file.run s.toList with
  | some (groups, []) => some groups
  | _ => none

/-- Print back to a string. -/
def print (groups : NEList (NEList Digit)) : String := String.mk (file.print groups)

-- Round-trips: parse then print recovers the original string.
#eval (parse "1234;567;89;").map print          -- some "1234;567;89;"
#eval ((parse "1234;567;89;").map print) == some "1234;567;89;"   -- true
#eval (parse "42;").map print                    -- some "42;"
#eval parse "12;3x;"                              -- none  (x is not a digit, ; missing)
#eval parse ""                                    -- none  (needs ≥1 group)

end LambdaLab.IsoParser.Example
