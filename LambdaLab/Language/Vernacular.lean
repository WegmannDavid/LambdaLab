import LambdaLab.Language.Basic
import LambdaLab.NEList

namespace LambdaLab.Language

/-- A single declaration: `def NAME : TYPE := BODY`.

The name is the language's *own* variable name (`Var L`), not a raw `String` and not a separate
vernacular notion. Two things follow. A command holding the name `def` is unrepresentable, so it
cannot print a lexeme the parser reads back as a keyword. And a declared name is directly usable
as a term variable — `def f : T := e` puts `f` in scope for what follows, with no injection
between two kinds of name. -/
inductive Command (L : Language) where
  | decl : Var L → L.Ty → L.Tm → Command L

namespace Command

variable {L : Language}

def name : Command L → Var L   | .decl n _ _ => n
def ty   : Command L → L.Ty    | .decl _ t _ => t
def tm   : Command L → L.Tm    | .decl _ _ b => b

end Command

/-- A program is a **non-empty** run of commands.

Why not `List (Command L)`: a one-or-more parser never *parses* an empty list, so an empty
program has no printed form to parse back — it would falsify the round-trip law. `NEList` is
also exactly the source shape `iMany1` consumes, so the vernacular parser lines up with it
with no adapter. -/
abbrev Program (L : Language) := NEList (Command L)

end LambdaLab.Language
