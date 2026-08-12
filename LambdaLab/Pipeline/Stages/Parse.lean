import LambdaLab.Pipeline.Basic
import LambdaLab.Parser.IsoParser.Notation

/-!
# The vernacular biparser, derived — now lossy

A `Language` supplies two `LossyParser`s (`pTy`, `pTm`) and their annotation families.
*Everything* here is derived from them — the command parser, the file parser, the round-trip
proof, and (new) the `Abs` morphism.

**The derivation strategy.** The `IsoParser` combinator layer (`gdo`, `comap`, `tok`, `many1`)
is reused, not cloned: each lossy component crosses into it as an `IsoParser` over its
*annotated values* (`toIsoParser`, whose printed value is the index — definitionally), the
existing combinators assemble the grammar with the **annotated command/program as the source**,
and the assembled parser crosses back (`toLossyParserSigma`) once its printed value is shown to
be the index (`echo` — `rfl` after eta, plus one induction for `many1`).

So the seams are exactly the old ones — `pTy`'s FOLLOW is pinned to `:=`, `pTm`'s to `def`, and
every `gdo` obligation still discharges definitionally. What changed is only what flows through:
values are parsed, spellings are printed, and the annotation family records the difference.

**The payoff:** `Language.abstraction` — every plugged-in language yields an `Abs` morphism
`List Token ⇝ Program`, with the program's full surface spelling as the annotation.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Parser.IsoParser
open LambdaLab.Parser.LossyParser (LossyParser)
open LambdaLab (Abstraction)

/-- An identifier: one token the language admits as a variable name. Aligned: source and value
are `Var L`, so a name the language would reject is unrepresentable. -/
def Language.pName (L : Language) :
    IsoParser Token (fun t => L.isVarName t = true) (fun _ => True) (Var L) (Var L) :=
  sat L.isVarName

/-! ## The command -/

/-- Everything a command's surface may spell beyond the command itself: the annotations of its
type and its term. (The name and the keywords have exactly one spelling.) -/
def Command.Ann (L : Language) : Command L → Type :=
  fun c => L.AnnTy c.ty × L.AnnTm c.tm

/-- The command parser at the `IsoParser` level: the **source is the annotated command**. The
type/term sub-parsers cross in via `toIsoParser` and `comap` the slice of the source they print
from; the one non-trivial seam — a type may be followed by `:=` — is definitionally true, as
before. -/
def Language.commandIso (L : Language) :
    IsoParser Token (· = kwDef) followDef (Σ c : Command L, Command.Ann L c) (Command L) := gdo
  let _kw ← tok kwDef
  let n ← comap (fun s => s.1.name) L.pName
  let _c ← tok kwColon
  let ty ← comap (fun s => ⟨s.1.ty, s.2.1⟩) L.pTy.toIsoParser
  let _a ← tok kwAssign
  let tm ← comap (fun s => ⟨s.1.tm, s.2.2⟩) L.pTm.toIsoParser
  return Command.decl n ty tm

/-- The command parser prints the value it is indexed by — each component's `print₁` is its
index, so the composite's is the reassembled command (eta). -/
theorem Language.commandIso_echo (L : Language) :
    ∀ s : Σ c : Command L, Command.Ann L c, (L.commandIso.print s).1 = s.1
  | ⟨.decl _ _ _, _⟩ => rfl

/-- **The command parser, lossy**: value `Command L`, annotation `Command.Ann`. Canonical print
uses the sub-parsers' canonical annotations. -/
def Language.command (L : Language) :
    LossyParser Token (· = kwDef) followDef (Command L) (Command.Ann L) :=
  L.commandIso.toLossyParserSigma (fun {_} => (L.pTy.default, L.pTm.default))
    L.commandIso_echo

/-! ## The program -/

/-- Annotations for every command of a list. -/
def ListAnn (L : Language) : List (Command L) → Type
  | [] => PUnit
  | c :: cs => Command.Ann L c × ListAnn L cs

/-- Annotations for every command of a program: the full surface spelling of a file. -/
def Program.Ann (L : Language) (prog : Program L) : Type :=
  Command.Ann L prog.1 × ListAnn L prog.2

def defaultListAnn (L : Language) : (cs : List (Command L)) → ListAnn L cs
  | [] => PUnit.unit
  | _ :: cs => ((L.pTy.default, L.pTm.default), defaultListAnn L cs)

/-- Zip a command list with its annotations into `many1`'s source shape. -/
def zipAnnList (L : Language) :
    (cs : List (Command L)) → ListAnn L cs → List (Σ c : Command L, Command.Ann L c)
  | [], _ => []
  | c :: cs, (a, as) => ⟨c, a⟩ :: zipAnnList L cs as

/-- The file parser at the `IsoParser` level: the existing `many1` over `commandIso`, with the
source reshaped from `Σ prog, annotations` to `many1`'s list-of-`Σ`. A command's FIRST *is*
`def` and its FOLLOW *is* `def`, so the repetition obligation is the identity, as before. -/
def Language.parserIso (L : Language) :
    IsoParser Token (· = kwDef) (fun t => followDef t ∧ ¬ t = kwDef)
      (Σ prog : Program L, Program.Ann L prog) (NEList (Command L)) :=
  comap (fun s => (⟨s.1.1, s.2.1⟩, zipAnnList L s.1.2 s.2.2))
    (many1 L.commandIso (fun _ h => h))

/-- `many1`'s printed values over a zipped source are the original commands. -/
theorem Language.printV_zipAnnList (L : Language) :
    ∀ (cs : List (Command L)) (as : ListAnn L cs),
      many1PrintV L.commandIso (zipAnnList L cs as) = cs
  | [], _ => rfl
  | c :: cs, (a, as) => by
      simp only [zipAnnList, many1PrintV, L.printV_zipAnnList cs as,
        L.commandIso_echo ⟨c, a⟩]

/-- The file parser prints the program it is indexed by. -/
theorem Language.parserIso_echo (L : Language)
    (s : Σ prog : Program L, Program.Ann L prog) : (L.parserIso.print s).1 = s.1 := by
  show ((L.commandIso.print ⟨s.1.1, s.2.1⟩).1,
    many1PrintV L.commandIso (zipAnnList L s.1.2 s.2.2)) = s.1
  rw [L.commandIso_echo ⟨s.1.1, s.2.1⟩, L.printV_zipAnnList s.1.2 s.2.2]

/-- **The file parser, lossy**: value `Program L` (as `NEList (Command L)`), annotation the full
surface spelling. Canonical print = every command in canonical form. -/
def Language.parser (L : Language) :
    LossyParser Token (· = kwDef) (fun t => followDef t ∧ ¬ t = kwDef)
      (NEList (Command L)) (Program.Ann L) :=
  L.parserIso.toLossyParserSigma
    (fun {prog} => ((L.pTy.default, L.pTm.default), defaultListAnn L prog.2))
    L.parserIso_echo

/-- **The file round-trip.** Print a program under *any* spelling, parse it back, recover the
program exactly with nothing left over — for every language, no side-conditions. -/
theorem Language.parser_roundtrip (L : Language) (prog : Program L)
    (ann : Program.Ann L prog) :
    L.parser.run (L.parser.print ann) = some (prog, []) :=
  L.parser.roundtrip prog ann

/-- **Every language is an `Abs` morphism** `List Token ⇝ Program`: the whole-file abstraction,
whose annotation is the file's surface spelling. Composes with the tokenizer
(`Abstraction/Tokenizer.lean`) for the `List Char` pipeline. -/
def Language.abstraction (L : Language) :
    Abstraction (List Token) (NEList (Command L)) (Program.Ann L) :=
  L.parser.toAbstraction

end LambdaLab.Pipeline
