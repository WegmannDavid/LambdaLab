import LambdaLab.Language1.Vernacular
import LambdaLab.IsoParser.Notation

/-!
# The vernacular biparser, derived (IsoParser, split model)

A `Language` supplies exactly two things: `pTy` and `pTm`. *Everything* here is derived from
them — the command parser, the file parser, and the round-trip proof.

**There are no proof obligations left in this file.** The seams that used to be declared facts
are now definitionally true, because the interface pins `pTy`'s FOLLOW to `:=` and `pTm`'s to
`def` — the very tokens that follow them. So every `gdo` seam and the `many1` repetition
obligation discharge by `seam`/identity.

**The product node.** The command's fields print from different slices of the shared source, so
the name, type and term sub-parsers each `comap` the projection they need; the keyword `tok`s
have polymorphic sources and need no adaptation.

**Deferred: the character level.** `viaTokens`/`layout` compose a tokenizer in front of the token
parser; that machinery is not ported to `IsoParser`, so this file stops at the token level.
-/

namespace LambdaLab.Language1

open LambdaLab.IsoParser

/-- An identifier: one non-keyword lexeme. Aligned: source and value are `Name`, so a keyword
source is unrepresentable. -/
def pName : IsoParser Token (fun t => isName t = true) (fun _ => True) Name Name := sat isName

/-- One command: `def NAME : TYPE := BODY`. The one non-trivial seam — a type may be followed by
`:=` — is definitionally true (`pTy`'s FOLLOW *is* `(· = kwAssign)`). -/
def Language.command (L : Language) :
    IsoParser Token (· = kwDef) followDef (Command L) (Command L) := gdo
  let _kw ← tok kwDef
  let n ← comap Command.name pName
  let _c ← tok kwColon
  let ty ← comap Command.ty L.pTy
  let _a ← tok kwAssign
  let tm ← comap Command.tm L.pTm
  return Command.decl n ty tm

/-- **The file parser**: a non-empty run of commands. A command's FIRST *is* `def` and its FOLLOW
*is* `def`, so the `many1` repetition obligation is the identity. Aligned: source and value are
both `Program L`. -/
def Language.parser (L : Language) :
    IsoParser Token (· = kwDef) (fun t => followDef t ∧ ¬ t = kwDef)
      (Program L) (NEList (Command L)) :=
  many1 L.command (fun _ h => h)

/-- **The file round-trip.** Print any program, parse it back, recover the printed value exactly
with nothing left over — for *every* language, no side-conditions. -/
theorem Language.parser_roundtrip (L : Language) (prog : Program L) :
    L.parser.run (L.parser.print prog).2 = some ((L.parser.print prog).1, []) :=
  L.parser.roundtrip prog

end LambdaLab.Language1
