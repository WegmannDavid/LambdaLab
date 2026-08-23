import LambdaLab.Pipeline.Stages.Parse
import LambdaLab.Pipeline.Stages.Elaborate
import LambdaLab.Abstraction.Tokenizer

/-!
# Chaining the stages: fill in a `Language`, get a front end

Every stage is an `Abs` morphism, and `Abs` composes, so the front end is not written here — it is
*assembled* here. This file contains no stage of its own; each one is defined elsewhere and this is
the only place they are joined.

```
List Char  ⇝  List Token  ⇝  Program  ⇝  Elaborated
           ①             ②           ③
```

① `Abstraction/Tokenizer.lean` — generic, shared by every language, so it has no file under
  `Stages/`. Instantiated below at the vernacular's own separator (`isSep`, whitespace), so the
  alphabet agreement between ① and ② is by construction rather than coincidence. It knows nothing
  of commands; the layout that puts one per line is imposed here, on the composite.
② `Stages/Parse.lean` — `Language.abstraction`, built from the language's two parsers.
③ `Stages/Elaborate.lean` — `Language.elabStage`, built from its type system.

## Two chains, because ③ is conditional

① and ② need nothing but a `Language`. ③ additionally needs
`[TypeSystem.Named.PrincipalElaborate (Var L) L.Tm L.Ty]` — the language's own types and terms must
satisfy the elaboration interface. So there are two composites, each named for how far it goes:

* `parsePipeline : List Char ⇝ Program`, and its `String`-level API `parseFile`/`renderProgram`;
* `elabPipeline : List Char ⇝ Elaborated`, and `elaborateFile`/`renderElaborated`.

Neither is "the" pipeline, and neither is named as though it were. A language with no semantics
attached — `Arith` — simply stops at the first, and that is a fact about `Arith`, not a gap.

## What composition buys

`abstract` is the file reader (whole input, `none` on any error), `realize` re-renders any recorded
spelling, and `realize ∘ default` is the canonical printer. Because the *composite* is a single
`Abs` morphism, its round-trip law covers every stage at once: `elaborateFile_renderElaborated`
below says that rendering an elaborated program and reading it back re-tokenizes, re-parses **and**
re-elaborates to exactly what you started with. That theorem is one line, because composition did
the work.

The annotation of a composite is the pair of its parts' annotations — for `parsePipeline`, a
spelling of every command together with the whitespace gaps of the resulting token rendering:

```
Σ (spellings of every command) , (the whitespace gaps of the token rendering)
```

Note the tokenizer is Agda-style: tokens must be whitespace-separated — write `( x )`, not `(x)`.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Abstraction

open LambdaLab.Parser.IsoParser (many1PrintOut)

open LambdaLab.TypeSystem.Named.Vernacular (elabProgram?)

/-! ## The canonical layout

Pretty-printing lives here, and it *has* to: it is a statement about whitespace (①) indexed by
where the commands end (②), so it is expressible only where both stages are in scope. Neither
stage can state it alone — which is why it is not a stage, but a choice of `default` on the
composite (`withDefault`).

The parser emits a command's tokens as a block and concatenates the blocks (`many1PrintOut`), so
the gaps split the same way: `defaultInner ' '` inside a block, a newline at each seam
(`joinInner`). The word `def` appears nowhere below — a line ends because a *command* ended.
-/

/-- The newline seam between two commands. -/
def nlSeam : NEGap isSep := scGap '\n' (by decide)

/-- Layout for the commands after the first: mirrors `many1PrintOut`'s own recursion. -/
def Language.layoutTail (L : Language) :
    (cs : List (Command L)) → (as : ListAnn L cs) →
      Inner isSep (many1PrintOut L.commandIso (zipAnnList L cs as))
  | [], _ => PUnit.unit
  | c :: cs, (a, as) =>
      joinInner nlSeam
        (L.commandIso.print ⟨c, a⟩).2 (defaultInner ' ' (by decide) _)
        (many1PrintOut L.commandIso (zipAnnList L cs as)) (L.layoutTail cs as)

/-- **The canonical layout of a program**: one command per line, single spaces within a command,
no leading or trailing whitespace. An annotation of the composite's gap component, so it is a
legal `default` and nothing about the morphism changes. -/
def Language.layout (L : Language) {prog : Program L} (ann : Program.Ann L prog) :
    Gaps isSep (L.parser.print ann) :=
  ⟨emptyRun,
    joinInner nlSeam
      (L.commandIso.print ⟨prog.1, ann.1⟩).2 (defaultInner ' ' (by decide) _)
      (many1PrintOut L.commandIso (zipAnnList L prog.2 ann.2)) (L.layoutTail prog.2 ann.2)⟩

/-! ## ① ∘ ② — reading, no semantics required -/

/-- **Characters to program**, in `Abs`: the tokenizer composed with the language's parsing stage.
Available for every `Language`, since neither stage knows what a program means. -/
def Language.parsePipeline (L : Language) :
    Abstraction (List Char) (NEList (Command L))
      (fun prog => Σ ann : Program.Ann L prog, Gaps isSep (L.parser.print ann)) :=
  ((tokenizer (sep := isSep) ' ' (by decide)).comp L.abstraction).withDefault
    (fun {_prog} => ⟨L.parser.default, L.layout L.parser.default⟩)

/-- Parse a source file into a program. Whole-input: leading/trailing whitespace is fine,
anything unconsumed is not. -/
def Language.parseFile (L : Language) (s : String) : Option (Program L) :=
  L.parsePipeline.abstract s.toList

/-- Render a program canonically: every command in its canonical spelling, one per line. -/
def Language.renderProgram (L : Language) (prog : Program L) : String :=
  String.ofList (L.parsePipeline.realize (L.parsePipeline.default (a := prog)))

/-! ## ① ∘ ② ∘ ③ — and type checking, when the language has a type system

Everything below is the same construction with one more stage on the end. The only new
requirement is the `PrincipalElaborate` instance; the moment a language's own types and terms
satisfy it, the whole front end exists with nothing further to supply. -/

variable (L : Language) [TypeSystem.Named.PrincipalElaborate (Var L) L.Tm L.Ty]

/-- **Characters to an elaborated program**, in `Abs`. Parsing and elaboration are one morphism,
so the round-trip law covers both — `realize` of any annotation re-parses *and* re-elaborates to
exactly the value it indexes. -/
def Language.elabPipeline :
    Abstraction (List Char) L.Elaborated
      (fun p => Σ ann : { q : Program L // elabProgram? q = some p.val },
        Σ a : Program.Ann L ann.val, Gaps isSep (L.parser.print a)) :=
  L.parsePipeline.comp L.elabStage

/-- Parse *and* elaborate a source file. -/
def Language.elaborateFile (s : String) : Option L.Elaborated :=
  L.elabPipeline.abstract s.toList

/-- Render an elaborated program canonically: every declaration on its own line, in its canonical
spelling, with the types elaboration solved written out. -/
def Language.renderElaborated (p : L.Elaborated) : String :=
  String.ofList (L.elabPipeline.realize (L.elabPipeline.default (a := p)))

/-- **The front end round-trips.** Render an elaborated program and read it back, and elaboration
returns it — the canonical-print guarantee, covering tokenizing, parsing and type checking at
once. -/
theorem Language.elaborateFile_renderElaborated (p : L.Elaborated) :
    L.elaborateFile (L.renderElaborated p) = some p := by
  show L.elabPipeline.abstract (String.ofList
    (L.elabPipeline.realize (L.elabPipeline.default (a := p)))).toList = some p
  rw [String.toList_ofList]
  exact L.elabPipeline.abstract_realize p L.elabPipeline.default

end LambdaLab.Pipeline
