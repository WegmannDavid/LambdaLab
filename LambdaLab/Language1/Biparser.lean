import LambdaLab.Language1.Vernacular
import LambdaLab.CBiparser.Tokenizer

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

/-! ## The character level

Everything above is over *tokens*. A file is *characters*. `viaTokens` precomposes the tokenizer,
and because the tokenizer's `Token` and the vernacular's `Token` are **the same type** — Language1
derives its alphabet from `CBiparser.Token isSep` rather than declaring a parallel one — the two
stages compose with nothing to reconcile.

The round-trip law survives the composition **with no new hypothesis**: `viaTokens_roundtrip` needs
only that every gap is a valid separator run (`Gap`), and both seams (the character one and the
token one) are vacuous at end of input.

## Layout is a free knob

The gap policy is a pure *printing* choice — `parse` never sees it. So a language can lay out its
source however it likes (a newline before each declaration, say) and the very same round-trip proof
still holds, because tokenizing collapses whatever separators the policy emitted. `layout` below is
that policy: a newline before each command keyword (`def`), a single space everywhere else. -/

/-- The gap policy: a newline before each command boundary (`def`), a space elsewhere. A pure
layout choice; parsing is oblivious to it. -/
def layout : Token → Token → List Char :=
  fun _ u => if u = kwDef then ['\n'] else [' ']

/-- Every gap `layout` emits is a nonempty run of separators — so the round-trip law applies. -/
theorem layout_gap : ∀ t u, CBiparser.Gap isSep (layout t u) := by
  intro t u
  unfold layout CBiparser.Gap
  by_cases h : u = kwDef <;> simp only [h, if_true, if_false] <;>
    refine ⟨fun c hc => ?_, by simp⟩ <;>
    · simp only [List.mem_singleton] at hc; subst hc; decide

/-- **The file parser, over characters.** Laid out with `layout`: one declaration per line. -/
def Language.fileParser (L : Language) : CBiparser Char (Program L) (List (Command L)) :=
  viaTokens isSep layout L.parser.toCBiparser

/-- Print a program to source text (one declaration per line). -/
def Language.renderProgram (L : Language) (prog : Program L) : String :=
  String.ofList (L.fileParser.print prog).2

/-- Parse a whole file: succeeds only if **everything** is consumed. -/
def Language.parseFile (L : Language) (src : String) : Option (List (Command L)) :=
  match L.fileParser.run src.toList with
  | some (cmds, []) => some cmds
  | _               => none

/-- **The file round-trip, at the character level.** Print any program to text, parse the text
back, and recover it exactly — for *every* language, with no side conditions.

This is the same one-liner as `parser_roundtrip`, now spanning both stages *and* the layout. -/
theorem Language.fileParser_roundtrip (L : Language) (prog : Program L) :
    L.fileParser.run (L.fileParser.print prog).2
      = some ((L.fileParser.print prog).1, []) :=
  viaTokens_roundtrip layout_gap L.parser.toCBiparser L.parser.ok prog

/-- The same law, in the form a user cares about: **render a program, parse the text, get it
back.** -/
theorem Language.parseFile_renderProgram (L : Language) (prog : Program L) :
    L.parseFile (L.renderProgram prog) = some ((L.fileParser.print prog).1) := by
  have h := L.fileParser_roundtrip prog
  simp only [Language.parseFile, Language.renderProgram, String.toList_ofList, h]

end LambdaLab.Language1
