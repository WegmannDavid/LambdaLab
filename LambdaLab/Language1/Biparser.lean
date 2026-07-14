import LambdaLab.Language1.Vernacular

/-!
# The vernacular biparser, derived

A `Language` supplies exactly two things: `pTy` and `pTm`. *Everything* here is derived from
them — the command biparser, the file biparser, and the round-trip proof. It is a *bi*parser:
one definition gives both the parser and the printer, and the law that they agree.

**There are no proof obligations left in this file.** The seams that used to be declared facts
are now definitionally true, because the interface pins `pTy`'s FOLLOW to `:=` and `pTm`'s to
`def` — the very tokens that follow them. So a command's FIRST *is* `def` and a term's FOLLOW
*is* `def`, and the `iMany1` obligation collapses to the identity function (`fun _ h => h`).

The round-trip is one line: each combinator rebuilt the law as it went, so there is nothing to
assemble at the end.
-/

namespace LambdaLab.Language1

open LambdaLab.CBiparser

/-- An identifier: one non-keyword lexeme. Source *and* value are `Name`, so a keyword source
is unrepresentable. -/
def pName : IBip isName (fun _ => true) Name Name := iSat isName

/-- One command: `def NAME : TYPE := BODY`.

Source **and** value are `Command L`. This is the multi-source node: the name, the type and the
term each print from a *different* slice of the command, so each sub-parser `iComap`s out the
projection it needs. `iTok`'s source is polymorphic, so the fixed keywords need no adaptation. -/
def Language.command (L : Language) :
    IBip (fun t => decide (t = kwDef)) followDef (Command L) (Command L) :=
  gdo
    let _kw ← iTok (w := Command L) kwDef
    let n  ← iComap Command.name pName
    let _c  ← iTok (w := Command L) kwColon
    let ty ← iComap Command.ty L.pTy
    let _a  ← iTok (w := Command L) kwAssign
    let tm ← iComap Command.tm L.pTm
    return Command.decl n ty tm

/-- **The file parser**: a non-empty run of commands. Its source is exactly `Program L`. -/
def Language.parser (L : Language) :
    IBip (fun t => decide (t = kwDef))
         (fun t => followDef t && !decide (t = kwDef))
         (Program L) (List (Command L)) :=
  -- `hrep` is now trivial: a command's FIRST *is* `def`, and a term's FOLLOW *is* `def`.
  iMany1 L.command (fun _ h => h)

/-- **The file round-trip.** Print any program, parse it back, recover it exactly with nothing
left over — for *every* language, no side-conditions. One line: the law was rebuilt by the
combinators, not proved here. -/
theorem Language.parser_roundtrip (L : Language) (prog : Program L) :
    L.parser.run (L.parser.print prog).2
      = some ((L.parser.print prog).1, []) :=
  L.parser.roundtrip prog

end LambdaLab.Language1
