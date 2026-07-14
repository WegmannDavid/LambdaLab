import LambdaLab.Language1.Basic
import LambdaLab.NEList

namespace LambdaLab.Language1

/-- A single declaration: `def NAME : TYPE := BODY`.

The name is a `Name` (non-keyword), not a raw `String`: a command holding the name `"def"`
would print a lexeme the parser reads back as a keyword, breaking the round-trip. Same medicine
as everywhere else — make the bad source unrepresentable. -/
inductive Command (L : Language) where
  | decl : Name → L.Ty → L.Tm → Command L

namespace Command

variable {L : Language}

def name : Command L → Name    | .decl n _ _ => n
def ty   : Command L → L.Ty    | .decl _ t _ => t
def tm   : Command L → L.Tm    | .decl _ _ b => b

end Command

/-- A program is a **non-empty** run of commands.

Why not `List (Command L)`: a one-or-more parser never *parses* an empty list, so an empty
program has no printed form to parse back — it would falsify the round-trip law. `NEList` is
also exactly the source shape `iMany1` consumes, so the vernacular parser lines up with it
with no adapter. -/
abbrev Program (L : Language) := NEList (Command L)

end LambdaLab.Language1
