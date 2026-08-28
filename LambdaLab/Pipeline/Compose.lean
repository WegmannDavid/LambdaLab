import LambdaLab.Pipeline.Stages.Parse
import LambdaLab.Pipeline.Stages.Elaborate
import LambdaLab.Pipeline.Stages.Evaluate
import LambdaLab.Abstraction.Tokenizer
import LambdaLab.Abstraction.Chain

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

open LambdaLab.TypeSystem.Named.Vernacular (elabProgram? evalProgram)

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

/-- ① as a 1-cell — the annotation family bundled in, so the stage can sit in a `Chain`. -/
def tokenCell : OneCell (List Char) (List Token) :=
  ⟨Gaps isSep, tokenizer (sep := isSep) ' ' (by decide)⟩

/-- ② as a 1-cell. -/
def Language.parseCell (L : Language) : OneCell (List Token) (Program L) :=
  ⟨Program.Ann L, L.abstraction⟩

/-- **Characters to program**, in `Abs`: the tokenizer composed with the language's parsing stage.
Available for every `Language`, since neither stage knows what a program means. -/
def Language.parsePipeline (L : Language) :
    Abstraction (List Char) (NEList (Command L))
      (fun prog => Σ ann : Program.Ann L prog, Gaps isSep (L.parser.print ann)) :=
  (tokenCell.hom.comp L.abstraction).withDefault
    (fun {_prog} => ⟨L.parser.default, L.layout L.parser.default⟩)

/-- Parse a source file into a program. Whole-input: leading/trailing whitespace is fine,
anything unconsumed is not. -/
def Language.parseFile (L : Language) (s : String) : Option (Program L) :=
  L.parsePipeline.abstract s.toList

/-- Render a program canonically: every command in its canonical spelling, one per line. -/
def Language.renderProgram (L : Language) (prog : Program L) : String :=
  String.ofList (L.parsePipeline.realize (L.parsePipeline.default (a := prog)))

/-! ## The same two stages, uncollapsed

`parsePipeline` is the pipeline as one morphism; `parseChain` is the same pipeline as the list of
its stages. The composite is what carries the round-trip law — one law covering every stage is the
whole point of composing — but it has forgotten that there *were* stages, and a compiler needs
that back: to show the token stream on the way past, and to say which stage rejected a file
instead of only that something did. `Abstraction/Chain.lean` has the argument in full.

The two are not two pipelines. `parseChain_abstract` below proves they read a file the same way,
and they differ only in `default` — the chain folds each stage's own canonical annotation, while
the composite re-chooses it (`withDefault`) to get one command per line, which is a choice only
expressible where both stages are in scope. So the *stages* carry the renderers already defined
above rather than deriving them, and `programStage` renders with `renderProgram`, layout and all.
-/

/-- The file, as read. -/
def sourceStage : Stage where
  Carrier := List Char
  name := "source"
  render := String.ofList

/-- After ①: the token stream, shown re-rendered with single spaces. -/
def tokenStage : Stage where
  Carrier := List Token
  name := "tokens"
  render := fun ts => String.ofList (tokenCell.hom.realize (tokenCell.hom.default (a := ts)))

/-- After ②: the program, shown in its canonical layout. -/
def Language.programStage (L : Language) : Stage where
  Carrier := Program L
  name := "program"
  render := L.renderProgram

/-- **Characters to program, stage by stage.** -/
def Language.parseChain (L : Language) : Chain sourceStage L.programStage :=
  Chain.cons (Y := tokenStage) (Chain.one tokenCell) L.parseCell

/-- Stepping through the stages reads a file exactly as collapsing them does. -/
@[simp] theorem Language.parseChain_abstract (L : Language) (cs : List Char) :
    L.parseChain.compose.hom.abstract cs = L.parsePipeline.abstract cs := by
  rw [parseChain, Chain.compose_cons, Chain.compose_one]
  simp only [parsePipeline, parseCell, Abstraction.comp, Abstraction.withDefault_abstract,
    OneCell.hcomp_abstract]
  rfl

/-- What the driver relies on: running the chain over a file agrees with `parseFile`. -/
theorem Language.parseChain_run (L : Language) (s : String) :
    (L.parseChain.run s.toList).2.toOption = L.parseFile s :=
  (L.parseChain.run_eq_abstract _).trans (L.parseChain_abstract _)

/-! ## ① ∘ ② ∘ ③ — and type checking, when the language has a type system

Everything below is the same construction with one more stage on the end. The only new
requirement is the `PrincipalElaborate` instance; the moment a language's own types and terms
satisfy it, the whole front end exists with nothing further to supply. -/

section Elaborating

/-! The instance binder is scoped. Leaking it past the section would put a bare
`PrincipalElaborate` beside the `Runnable` of the next one, and a *local* instance outranks
`Runnable.toPrincipalElaborate` — so `Elaborated` would be built from a different judgement than
the one `eval` accepts, which is the very diamond `Runnable` exists to close. -/

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

/-! ## All three stages, uncollapsed -/

/-- ③ as a 1-cell. -/
def Language.elabCell : OneCell (Program L) L.Elaborated :=
  ⟨fun p => { q : Program L // elabProgram? q = some p.val }, L.elabStage⟩

/-- After ③: the program with every metavariable solved. -/
def Language.elaboratedStage : Stage where
  Carrier := L.Elaborated
  name := "elaborated program"
  render := L.renderElaborated

/-- **The whole front end, stage by stage** — `parseChain` with elaboration on the end. Note that
this is `cons`, not a new pipeline: the parsing chain is literally a prefix of it, which is the
statement that a language with no type system stops one stage short rather than doing something
else. -/
def Language.elabChain : Chain sourceStage L.elaboratedStage :=
  L.parseChain.cons L.elabCell

/-- Stepping through all three stages agrees with collapsing them. -/
@[simp] theorem Language.elabChain_abstract (cs : List Char) :
    L.elabChain.compose.hom.abstract cs = L.elabPipeline.abstract cs := by
  rw [elabChain, Chain.compose_cons, OneCell.hcomp_abstract, L.parseChain_abstract]
  simp only [elabPipeline, elabCell, Abstraction.comp]
  rfl

/-- What the driver relies on: running the chain over a file agrees with `elaborateFile`. -/
theorem Language.elabChain_run (s : String) :
    (L.elabChain.run s.toList).2.toOption = L.elaborateFile s :=
  (L.elabChain.run_eq_abstract _).trans (L.elabChain_abstract _)

end Elaborating

/-! ## ① ∘ ② ∘ ③ ∘ ④ — and running, when the language has an evaluator

One more stage on the end, on the same terms as ③: it exists exactly when the language can supply
it. `Runnable` is `PrincipalElaborate` and `LawfulHasEval` sharing one judgement — see its
docstring for why the conjunction has to be a class rather than two hypotheses.

`Arith` stops at ②, `Stlc` goes to ④. Neither is "the" pipeline; the chain a language supports is
a fact about the language. -/

section Running

variable (L : Language) [TypeSystem.Named.Runnable (Var L) L.Tm L.Ty]

/-- **Characters to a normalized program**, in `Abs`. The round-trip law covers all four stages at
once, for the reason it covered three: it is one morphism. -/
def Language.evalPipeline :
    Abstraction (List Char) L.Evaluated
      (fun q => Σ ann : { p : L.Elaborated // evalProgram p.val p.property = q.val },
        Σ e : { r : Program L // elabProgram? r = some ann.val.val },
          Σ a : Program.Ann L e.val, Gaps isSep (L.parser.print a)) :=
  L.elabPipeline.comp L.evalStage

/-- Parse, elaborate *and* run a source file. -/
def Language.evaluateFile (s : String) : Option L.Evaluated :=
  L.evalPipeline.abstract s.toList

/-- Render a normalized program canonically. -/
def Language.renderEvaluated (q : L.Evaluated) : String :=
  String.ofList (L.evalPipeline.realize (L.evalPipeline.default (a := q)))

/-- **The whole front end round-trips, evaluation included.** Rendering a normalized program and
reading it back re-tokenizes, re-parses, re-elaborates *and* re-runs to exactly what you started
with — the last step because a normal form runs to itself. -/
theorem Language.evaluateFile_renderEvaluated (q : L.Evaluated) :
    L.evaluateFile (L.renderEvaluated q) = some q := by
  show L.evalPipeline.abstract (String.ofList
    (L.evalPipeline.realize (L.evalPipeline.default (a := q)))).toList = some q
  rw [String.toList_ofList]
  exact L.evalPipeline.abstract_realize q L.evalPipeline.default

/-! ### The fourth stage, uncollapsed -/

/-- ④ as a 1-cell. -/
def Language.evalCell : OneCell L.Elaborated L.Evaluated :=
  ⟨fun q => { p : L.Elaborated // evalProgram p.val p.property = q.val }, L.evalStage⟩

/-- After ④: the program with every redex gone. -/
def Language.evaluatedStage : Stage where
  Carrier := L.Evaluated
  name := "evaluated program"
  render := L.renderEvaluated

/-- **The whole front end, stage by stage.** `elabChain` with evaluation on the end. -/
def Language.evalChain : Chain sourceStage L.evaluatedStage :=
  L.elabChain.cons L.evalCell

/-- Stepping through all four stages agrees with collapsing them. -/
@[simp] theorem Language.evalChain_abstract (cs : List Char) :
    L.evalChain.compose.hom.abstract cs = L.evalPipeline.abstract cs := by
  rw [evalChain, Chain.compose_cons, OneCell.hcomp_abstract, L.elabChain_abstract]
  simp only [evalPipeline, evalCell, Abstraction.comp]
  rfl

/-- What the driver relies on: running the chain over a file agrees with `evaluateFile`. -/
theorem Language.evalChain_run (s : String) :
    (L.evalChain.run s.toList).2.toOption = L.evaluateFile s :=
  (L.evalChain.run_eq_abstract _).trans (L.evalChain_abstract _)

end Running

end LambdaLab.Pipeline
