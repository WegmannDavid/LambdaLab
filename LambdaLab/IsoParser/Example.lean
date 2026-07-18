import LambdaLab.IsoParser.Combinators

/-!
# Example: semicolon-terminated digit lists **with variable whitespace**

`"1234 ;567  ;89 ;"` — digits, then **one or more** spaces, then `;`, repeated. The whitespace amount
is a *choice* not pinned by the value, so it lands in the **annotation**; the value (`NEList Digit`
per group) forgets it. Round-tripping through the parsed annotation reproduces the exact spacing;
forgetting the annotation identifies strings that differ only in whitespace.

    file   = many1 group
    group  = number  ws  ';'          -- ws = one-or-more spaces (its chars are the annotation)
    number = many1 (sat isDigit)
-/

namespace LambdaLab.IsoParser.Example

open LambdaLab.IsoParser

abbrev Digit := { c : Char // c.isDigit = true }

/-- Whitespace = a single space character. -/
def isSpace : Char → Bool := fun c => c == ' '

/-- One or more digits (no choice: the digits are the value). -/
def number := many1 (sat Char.isDigit) (fun _ _ => rfl)

/-- One or more spaces, **hidden into the annotation** (value `Unit`). -/
def ws := hide (many1 (sat isSpace) (fun _ _ => rfl))

/-- A digit run, then whitespace, then `;`. -/
def group :=
  seq number
    (seq ws (tok ';')
      (fun c hc => by have hc' : c = ';' := (by simpa using hc); subst hc'; decide))
    (fun c hc => by have hc' : c = ' ' := (by simpa [isSpace] using hc); subst hc'; decide)

/-- One or more `;`-terminated, whitespace-separated digit groups. -/
def file := many1 group (fun _ _ => rfl)

/-- Round-trip a fully-consumed string through the parsed value+annotation. -/
def roundtrip (s : String) : Option String :=
  match file.run s.toList with
  | some (⟨v, a⟩, []) => some (String.ofList (file.print v a))
  | _ => none

/-- The digit groups only (value, forgetting whitespace). -/
def digits (s : String) : Option (List String) :=
  match file.run s.toList with
  | some (⟨v, _⟩, []) => some (v.toList.map (fun g => String.ofList (g.1.toList.map Subtype.val)))
  | _ => none

-- Round-trip preserves the exact whitespace (the annotation captured it):
#eval roundtrip "1234 ;567  ;89 ;"     -- some "1234 ;567  ;89 ;"
#eval roundtrip "12 ;"                 -- some "12 ;"
#eval roundtrip "12   ;"               -- some "12   ;"   (3 spaces preserved)
-- The value forgets whitespace — same digits regardless of spacing:
#eval digits "12 ;"                     -- some ["12"]
#eval digits "12   ;"                   -- some ["12"]
#eval (digits "12 ;") == (digits "12   ;")   -- true
#eval digits "1234 ;567  ;89 ;"        -- some ["1234","567","89"]
-- At least one space is required:
#eval roundtrip "1234;567;89;"         -- none  (no whitespace)

end LambdaLab.IsoParser.Example
