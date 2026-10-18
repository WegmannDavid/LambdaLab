import LambdaLab.Pipeline.Stages.Parse
import LambdaLab.Pipeline.Stages.Elaborate
import LambdaLab.Pipeline.Stages.Evaluate
import LambdaLab.Abstraction.Tokenizer
import LambdaLab.Abstraction.Chain
import LambdaLab.Semantics.Walk

/-!
# Chaining the stages: fill in a `Language`, get a front end

Every stage is an `Abs` morphism, and `Abs` composes, so the front end is not written here — it is
*assembled* here. This file contains no stage of its own; each one is defined elsewhere and this is
the only place they are joined.

```
List Char  ⇝  List Token  ⇝  Program  ⇝  (a walk)  ⇝  (another walk)  ⇝  …
           ①             ②           ③              ④
```

① `Abstraction/Tokenizer.lean` — generic, shared by every language, so it has no file under
  `Stages/`. Instantiated below at the language's own lexicon (`Language.lex`), the same one its
  parser reads, so the alphabet agreement between ① and ② is by construction rather than
  coincidence. It knows nothing of declarations; the layout that puts one per line is imposed
  here, on the composite.
② `Stages/Parse.lean` — `Language.abstraction`, built from the language's declaration forms.
③, ④, … — whatever **walks** the language has (`Semantics/Walk.lean`): a state carried through the
  declarations, each one rewritten on the way. A walk becomes a stage with `Walk.stage` (the first)
  or `Walk.stageOn` (one after another), and a pipeline cell and display with `walkCell` and
  `walkStage` below.

## How far a language goes is a fact about the language

① and ② need nothing but a `Language`, so every language has `parsePipeline`/`parseChain`. Which
walks follow, if any, is up to the language. The `def`-languages (`Pipeline/Def.lean`) get two
from their type system when it supplies them — elaboration, given `PrincipalElaborate`, and
evaluation after it, given `Runnable`:

* `parsePipeline : List Char ⇝ Program`, and its `String`-level API `parseFile`/`renderProgram`;
* `elabPipeline : List Char ⇝ Elaborated`, and `elaborateFile`/`renderElaborated`;
* `evalPipeline : List Char ⇝ Evaluated`, and `evaluateFile`/`renderEvaluated`.

None is "the" pipeline, and none is named as though it were. A language with no type system has
neither of the last two: `Float` has one walk of its own, evaluation, and is a `walkChain` (below)
— a fact about `Float`, not a gap.

## What composition buys

`abstract` is the file reader (whole input, a diagnostic on any error), `realize` re-renders any
recorded spelling, and `realize ∘ default` is the canonical printer. Because the *composite* is a single
`Abs` morphism, its round-trip law covers every stage at once: `elaborateFile_renderElaborated`
below says that rendering an elaborated program and reading it back re-tokenizes, re-parses **and**
re-elaborates to exactly what you started with. That theorem is one line, because composition did
the work.

Whether `(x)` needs to be written `( x )` is the lexicon's call: in a lexicon where the
parentheses are self-delimiting both spellings read the same, and the canonical one hugs them.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Abstraction

open LambdaLab.Parser.IsoParser (many1PrintOut Lexicon Token)
open LambdaLab.Semantics (Walk)

/-! ## The canonical layout

Pretty-printing lives here, and it *has* to: it is a statement about whitespace (①) indexed by
where the declarations end (②), so it is expressible only where both stages are in scope. Neither
stage can state it alone — which is why it is not a stage, but a choice of `default` on the
composite (`withDefault`).

The parser emits a declaration's tokens as a block and concatenates the blocks (`many1PrintOut`),
so the gaps split the same way: `defaultInner` inside a block, a newline at each seam
(`joinInner`). No keyword appears below — a line ends because a *declaration* ended.
-/

/-- The newline seam between two declarations. -/
def nlSeam (lex : Lexicon) : NEGap lex := scGap '\n' lex.newline_sep

/-- Layout for the declarations after the first: mirrors `many1PrintOut`'s own recursion. -/
def Language.layoutTail (L : Language) :
    (ds : List L.Decl) → (as : ListAnn L ds) →
      Inner L.lex (many1PrintOut L.declIso (zipAnnList L ds as))
  | [], _ => PUnit.unit
  | d :: ds, (a, as) =>
      joinInner (nlSeam L.lex)
        (L.declIso.print ⟨d, a⟩).2 (defaultInner L.lex _)
        (many1PrintOut L.declIso (zipAnnList L ds as)) (L.layoutTail ds as)

/-- **The canonical layout of a program**: one declaration per line, single spaces within a
declaration (none where the lexicon hugs a bracket), no leading or trailing whitespace. An
annotation of the composite's gap component, so it is a legal `default` and nothing about the
morphism changes. -/
def Language.layout (L : Language) {prog : Program L} (ann : Program.Ann L prog) :
    Gaps L.lex (L.parser.print ann) :=
  ⟨emptyRun,
    joinInner (nlSeam L.lex)
      (L.declIso.print ⟨prog.1, ann.1⟩).2 (defaultInner L.lex _)
      (many1PrintOut L.declIso (zipAnnList L prog.2 ann.2)) (L.layoutTail prog.2 ann.2)⟩

/-! ## ① ∘ ② — reading, no semantics required -/

/-- ① as a 1-cell — the annotation family bundled in, so the stage can sit in a `Chain`. -/
def tokenCell (lex : Lexicon) : OneCell (List Char) (List (Token lex)) :=
  ⟨Gaps lex, tokenizer lex⟩

/-- ② as a 1-cell. -/
def Language.parseCell (L : Language) : OneCell (List (Token L.lex)) (Program L) :=
  ⟨Language.ParseAnn L, L.abstraction⟩

/-- **Characters to program**, in `Abs`: the tokenizer composed with the language's parsing stage.
Available for every `Language`, since neither stage knows what a program means. -/
def Language.parsePipeline (L : Language) :
    Abstraction (List Char) (Program L)
      (fun prog => Σ β : Language.ParseAnn L prog, Gaps L.lex β.val) :=
  ((tokenCell L.lex).hom.comp L.abstraction).withDefault
    (fun {prog} => ⟨L.abstraction.default (a := prog), L.layout L.parser.default⟩)

/-- Parse a source file into a program. Whole-input: leading/trailing whitespace is fine,
anything unconsumed is not. -/
def Language.parseFile (L : Language) (s : String) : Except Diag (Program L) :=
  L.parsePipeline.abstract s.toList

/-- Render a program canonically: every declaration in its canonical spelling, one per line. -/
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
the composite re-chooses it (`withDefault`) to get one declaration per line, which is a choice only
expressible where both stages are in scope. So the *stages* carry the renderers already defined
above rather than deriving them, and `programStage` renders with `renderProgram`, layout and all.
-/

/-- The file, as read. -/
def sourceStage : Stage where
  Carrier := List Char
  name := "source"
  render := String.ofList

/-- After ①: the token stream, shown re-rendered with canonical spacing. -/
def tokenStage (lex : Lexicon) : Stage where
  Carrier := List (Token lex)
  name := "tokens"
  render := fun ts =>
    String.ofList ((tokenCell lex).hom.realize ((tokenCell lex).hom.default (a := ts)))

/-- After ②: the program, shown in its canonical layout. -/
def Language.programStage (L : Language) : Stage where
  Carrier := Program L
  name := "program"
  render := L.renderProgram

/-- **Characters to program, stage by stage.** -/
def Language.parseChain (L : Language) : Chain sourceStage L.programStage :=
  Chain.cons (Y := tokenStage L.lex) (Chain.one (tokenCell L.lex)) L.parseCell

/-- Stepping through the stages reads a file exactly as collapsing them does. -/
@[simp] theorem Language.parseChain_abstract (L : Language) (cs : List Char) :
    L.parseChain.compose.hom.abstract cs = L.parsePipeline.abstract cs := by
  rw [parseChain, Chain.compose_cons, Chain.compose_one, OneCell.hcomp_abstract]
  simp only [parsePipeline, Abstraction.withDefault_abstract, Abstraction.comp, parseCell]
  rfl

/-- …and points its diagnostics the same way. -/
theorem Language.parseChain_locate (L : Language) (cs : List Char) :
    L.parseChain.compose.hom.locate cs = L.parsePipeline.locate cs := by
  rw [parseChain, Chain.compose_cons, Chain.compose_one]
  simp only [parsePipeline, OneCell.hcomp, Abstraction.withDefault, Abstraction.comp, parseCell]
  rfl

/-- What the driver relies on: running the chain over a file agrees with `parseFile`. -/
theorem Language.parseChain_run (L : Language) (s : String) :
    ((L.parseChain.run s.toList).2.map Prod.fst).toOption = (L.parseFile s).toOption :=
  (L.parseChain.run_eq_abstract _).trans (congrArg Except.toOption (L.parseChain_abstract _))

/-! ## Walks, as stages

A language's semantics is whatever walks it has. Each becomes one more cell on the chain and one
more morphism in the composite; these say how, once, for every language. A walk's output is a
program of the same language, so it is shown the way the program stage is — `renderProgram`,
layout and all. -/

section Walks

variable (L : Language)

/-- What a walk produces, as a pipeline vertex. -/
def Language.walkStage (name : String) (w : Walk L.Decl) : Stage where
  Carrier := w.Fixed
  name := name
  render q := L.renderProgram q.val

/-- What a later walk produces, as a pipeline vertex. -/
def Language.walkStageOn (name : String) (w : Walk L.Decl) (P : Program L → Prop) : Stage where
  Carrier := w.FixedOn P
  name := name
  render q := L.renderProgram q.val

/-- The first walk, as a 1-cell from the parsed programs. -/
def Language.walkCell (w : Walk L.Decl) (h : w.Idempotent) : OneCell (Program L) w.Fixed :=
  ⟨_, w.stage h⟩

/-- A later walk, as a 1-cell from what the stage before it produced. -/
def Language.walkCellOn (w : Walk L.Decl) {P : Program L → Prop} (h : w.LawfulOn P) :
    OneCell { p : Program L // P p } (w.FixedOn P) :=
  ⟨_, w.stageOn h⟩

end Walks

/-! ## ① ∘ ② ∘ ③ — one walk after parsing

The front end of a language with one walk, assembled once for all of them: the composite, the
file reader, the renderer, its round trip, and the chain the driver runs. -/

section OneWalk

variable (L : Language) (w : Walk L.Decl) (h : w.Idempotent)

/-- **Characters to what the walk produces**, in `Abs`. Parsing and the walk are one morphism, so
the round-trip law covers both. -/
def Language.walkPipeline := L.parsePipeline.comp (w.stage h)

/-- Read a source file and run the walk over it. -/
def Language.walkFile (s : String) : Except Diag w.Fixed := (L.walkPipeline w h).abstract s.toList

/-- Render what the walk produced canonically: one declaration per line, each in its canonical
spelling. -/
def Language.renderWalked (q : w.Fixed) : String :=
  String.ofList ((L.walkPipeline w h).realize ((L.walkPipeline w h).default (a := q)))

/-- **The front end round-trips.** Render what the walk produced and read it back, and the walk
returns it — tokenizing, parsing and the walk at once. -/
theorem Language.walkFile_renderWalked (q : w.Fixed) :
    L.walkFile w h (L.renderWalked w h q) = .ok q := by
  show (L.walkPipeline w h).abstract (String.ofList
    ((L.walkPipeline w h).realize ((L.walkPipeline w h).default (a := q)))).toList = .ok q
  rw [String.toList_ofList]
  exact (L.walkPipeline w h).abstract_realize q (L.walkPipeline w h).default

/-- **The front end, stage by stage** — `parseChain` with the walk on the end. -/
def Language.walkChain (name : String) : Chain sourceStage (L.walkStage name w) :=
  L.parseChain.cons (L.walkCell w h)

/-- Stepping through the stages agrees with collapsing them. -/
@[simp] theorem Language.walkChain_abstract (name : String) (cs : List Char) :
    (L.walkChain w h name).compose.hom.abstract cs = (L.walkPipeline w h).abstract cs := by
  rw [walkChain, Chain.compose_cons, OneCell.hcomp_abstract]
  simp only [walkPipeline, Abstraction.comp, walkCell]
  exact Abstraction.compAbstract_congr _ _ _ _ _ (L.parseChain_abstract cs)
    (L.parseChain_locate cs) rfl

/-- …and points its diagnostics the same way. -/
theorem Language.walkChain_locate (name : String) (cs : List Char) :
    (L.walkChain w h name).compose.hom.locate cs = (L.walkPipeline w h).locate cs := by
  rw [walkChain, Chain.compose_cons]
  simp only [walkPipeline, OneCell.hcomp, Abstraction.comp, walkCell]
  rw [L.parseChain_abstract cs, L.parseChain_locate cs]
  rfl

/-- What the driver relies on: running the chain over a file agrees with `walkFile`. -/
theorem Language.walkChain_run (name : String) (s : String) :
    (((L.walkChain w h name).run s.toList).2.map Prod.fst).toOption = (L.walkFile w h s).toOption :=
  ((L.walkChain w h name).run_eq_abstract _).trans
    (congrArg Except.toOption (L.walkChain_abstract w h name _))

end OneWalk

/-! ## ① ∘ ② ∘ ③ — and type checking, for a `def`-language with a type system

Everything below is the same construction with one more stage on the end: the elaborator walk. The
only new requirement is the `PrincipalElaborate` instance; the moment a language's own types and
terms satisfy it, the whole front end exists with nothing further to supply. -/

section Elaborating

/-! The instance binder is scoped. Leaking it past the section would put a bare
`PrincipalElaborate` beside the `Runnable` of the next one, and a *local* instance outranks
`Runnable.toPrincipalElaborate` — so `Elaborated` would be built from a different judgement than
the one `eval` accepts, which is the very diamond `Runnable` exists to close. -/

variable (D : DefLanguage) [TypeSystem.Named.PrincipalElaborate (Var D) D.Tm D.Ty]

/-- **Characters to an elaborated program**, in `Abs`. Parsing and elaboration are one morphism,
so the round-trip law covers both — `realize` of any annotation re-parses *and* re-elaborates to
exactly the value it indexes. -/
abbrev DefLanguage.elabPipeline :=
  D.toLanguage.walkPipeline D.elabWalk TypeSystem.Named.Vernacular.elabWalk_idempotent

/-- Parse *and* elaborate a source file. -/
abbrev DefLanguage.elaborateFile (s : String) : Except Diag D.Elaborated :=
  D.toLanguage.walkFile D.elabWalk TypeSystem.Named.Vernacular.elabWalk_idempotent s

/-- Render an elaborated program canonically: every declaration on its own line, in its canonical
spelling, with the types elaboration solved written out. -/
abbrev DefLanguage.renderElaborated (p : D.Elaborated) : String :=
  D.toLanguage.renderWalked D.elabWalk TypeSystem.Named.Vernacular.elabWalk_idempotent p

/-- **The front end round-trips.** Render an elaborated program and read it back, and elaboration
returns it — the canonical-print guarantee, covering tokenizing, parsing and type checking at
once. -/
theorem DefLanguage.elaborateFile_renderElaborated (p : D.Elaborated) :
    D.elaborateFile (D.renderElaborated p) = .ok p :=
  D.toLanguage.walkFile_renderWalked _ _ p

/-! ### All three stages, uncollapsed -/

/-- After ③: the program with every metavariable solved. -/
abbrev DefLanguage.elaboratedStage : Stage :=
  D.toLanguage.walkStage "elaborated program" D.elabWalk

/-- **The whole front end, stage by stage** — `parseChain` with elaboration on the end. Note that
this is `cons`, not a new pipeline: the parsing chain is literally a prefix of it, which is the
statement that a language with no type system stops one stage short rather than doing something
else. -/
abbrev DefLanguage.elabChain : Chain sourceStage D.elaboratedStage :=
  D.toLanguage.walkChain D.elabWalk TypeSystem.Named.Vernacular.elabWalk_idempotent
    "elaborated program"

/-- Stepping through all three stages agrees with collapsing them. -/
theorem DefLanguage.elabChain_abstract (cs : List Char) :
    D.elabChain.compose.hom.abstract cs = D.elabPipeline.abstract cs :=
  D.toLanguage.walkChain_abstract _ _ _ cs

/-- What the driver relies on: running the chain over a file agrees with `elaborateFile`. -/
theorem DefLanguage.elabChain_run (s : String) :
    ((D.elabChain.run s.toList).2.map Prod.fst).toOption = (D.elaborateFile s).toOption :=
  D.toLanguage.walkChain_run _ _ _ s

end Elaborating

/-! ## ① ∘ ② ∘ ③ ∘ ④ — and running, when the language has an evaluator

One more stage on the end, on the same terms as ③: it exists exactly when the language can supply
it. `Runnable` is `PrincipalElaborate` and `LawfulHasEval` sharing one judgement — see its
docstring for why the conjunction has to be a class rather than two hypotheses.

`Float` has one walk and no type system; `Stlc` goes to ④ through its type system. Neither is
"the" pipeline; the chain a language supports is a fact about the language. -/

section Running

variable (D : DefLanguage) [TypeSystem.Named.Runnable (Var D) D.Tm D.Ty]

/-- **Characters to a normalized program**, in `Abs`. The round-trip law covers all four stages at
once, for the reason it covered three: it is one morphism. -/
def DefLanguage.evalPipeline := D.elabPipeline.comp D.evalStage

/-- Parse, elaborate *and* run a source file. -/
def DefLanguage.evaluateFile (s : String) : Except Diag D.Evaluated :=
  D.evalPipeline.abstract s.toList

/-- Render a normalized program canonically. -/
def DefLanguage.renderEvaluated (q : D.Evaluated) : String :=
  String.ofList (D.evalPipeline.realize (D.evalPipeline.default (a := q)))

/-- **The whole front end round-trips, evaluation included.** Rendering a normalized program and
reading it back re-tokenizes, re-parses, re-elaborates *and* re-runs to exactly what you started
with — the last step because evaluation leaves a normalized program unchanged. -/
theorem DefLanguage.evaluateFile_renderEvaluated (q : D.Evaluated) :
    D.evaluateFile (D.renderEvaluated q) = .ok q := by
  show D.evalPipeline.abstract (String.ofList
    (D.evalPipeline.realize (D.evalPipeline.default (a := q)))).toList = .ok q
  rw [String.toList_ofList]
  exact D.evalPipeline.abstract_realize q D.evalPipeline.default

/-! ### The fourth stage, uncollapsed -/

/-- After ④: the program with every redex gone. -/
def DefLanguage.evaluatedStage : Stage :=
  D.toLanguage.walkStageOn "evaluated program" D.evalWalk (fun p => D.elabWalk.run p = .ok p)

/-- **The whole front end, stage by stage.** `elabChain` with evaluation on the end. -/
def DefLanguage.evalChain : Chain sourceStage D.evaluatedStage :=
  D.elabChain.cons (Z := D.evaluatedStage)
    (D.toLanguage.walkCellOn D.evalWalk TypeSystem.Named.Vernacular.evalWalk_lawfulOn)

/-- Stepping through all four stages agrees with collapsing them. -/
@[simp] theorem DefLanguage.evalChain_abstract (cs : List Char) :
    D.evalChain.compose.hom.abstract cs = D.evalPipeline.abstract cs := by
  rw [evalChain, Chain.compose_cons, OneCell.hcomp_abstract]
  simp only [evalPipeline, Abstraction.comp, Language.walkCellOn, evalStage]
  exact Abstraction.compAbstract_congr _ _ _ _ _ (D.elabChain_abstract cs)
    (D.toLanguage.walkChain_locate _ _ _ cs) rfl

/-- What the driver relies on: running the chain over a file agrees with `evaluateFile`. -/
theorem DefLanguage.evalChain_run (s : String) :
    ((D.evalChain.run s.toList).2.map Prod.fst).toOption = (D.evaluateFile s).toOption :=
  (D.evalChain.run_eq_abstract _).trans (congrArg Except.toOption (D.evalChain_abstract _))

end Running

/-! ## A preparation step before elaboration

Some languages want a program rewritten before it is elaborated: STLC numbers its anonymous
metavariables `_` apart (`Languages/Stlc/Named/Holes.lean`). Any idempotent function on programs
is a stage (`Abstraction.ofIdempotent`), onto what it leaves unchanged; elaboration and evaluation
then run on those programs (`Walk.stageOn`). All the language must show is that the function is
idempotent and leaves alone what elaboration and evaluation produce — well-typed programs. -/

section Prepared

variable (D : DefLanguage) [TypeSystem.Named.Runnable (Var D) D.Tm D.Ty]
  (f : Program D.toLanguage → Program D.toLanguage)

/-- Elaboration, on prepared programs: what it produces is well typed, so still prepared. -/
theorem DefLanguage.elab_lawfulOn_prepared
    (htyped : ∀ q, TypeSystem.Named.Vernacular.HasType q → f q = q) :
    D.elabWalk.LawfulOn (fun p => f p = p) where
  preserve _ q _ h := htyped q (TypeSystem.Named.Vernacular.elabWalk_sound h)
  idem p q _ h := TypeSystem.Named.Vernacular.elabWalk_idempotent p q h

/-- Evaluation, on elaborated prepared programs: what it produces is well typed, so prepared and
elaborated. -/
theorem DefLanguage.eval_lawfulOn_prepared
    (htyped : ∀ q, TypeSystem.Named.Vernacular.HasType q → f q = q) :
    D.evalWalk.LawfulOn (fun p => f p = p ∧ D.elabWalk.run p = .ok p) where
  preserve _ q _ h :=
    have hq := TypeSystem.Named.Vernacular.evalWalk_sound h
    ⟨htyped q hq, TypeSystem.Named.Vernacular.elabWalk_self hq⟩
  idem p q _ h :=
    Walk.idempotent_of_step _ TypeSystem.Named.Vernacular.evalWalk_stepIdempotent p q h

variable (hidem : ∀ p, f (f p) = f p)
  (htyped : ∀ q, TypeSystem.Named.Vernacular.HasType q → f q = q)

/-- After preparation. -/
def DefLanguage.preparedStage (name : String) : Stage where
  Carrier := { p : Program D.toLanguage // f p = p }
  name := name
  render p := D.toLanguage.renderProgram p.val

/-- After elaboration, of prepared programs. -/
abbrev DefLanguage.elaboratedStageOn : Stage :=
  D.toLanguage.walkStageOn "elaborated program" D.elabWalk (fun p => f p = p)

/-- After evaluation, of elaborated prepared programs. -/
abbrev DefLanguage.evaluatedStageOn : Stage :=
  D.toLanguage.walkStageOn "evaluated program" D.evalWalk
    (fun p => f p = p ∧ D.elabWalk.run p = .ok p)

/-- **The front end, stage by stage, with the preparation step**: source, tokens, program,
prepared program, elaborated program, evaluated program. -/
def DefLanguage.evalChainVia (name : String) : Chain sourceStage (D.evaluatedStageOn f) :=
  have := hidem; have := htyped
  ((D.toLanguage.parseChain.cons (Z := D.preparedStage f name)
      ⟨_, Abstraction.ofIdempotent f hidem⟩).cons (Z := D.elaboratedStageOn f)
      (D.toLanguage.walkCellOn D.elabWalk (D.elab_lawfulOn_prepared f htyped))).cons
    (Z := D.evaluatedStageOn f)
    (D.toLanguage.walkCellOn D.evalWalk (D.eval_lawfulOn_prepared f htyped))

/-- **Characters to an evaluated program, with the preparation step**, in `Abs`: one morphism,
so one round-trip law. -/
def DefLanguage.evalPipelineVia :=
  ((D.toLanguage.parsePipeline.comp (Abstraction.ofIdempotent f hidem)).comp
    (D.elabWalk.stageOn (D.elab_lawfulOn_prepared f htyped))).comp
    (D.evalWalk.stageOn (D.eval_lawfulOn_prepared f htyped))

/-- Read, prepare, elaborate and run a source file. -/
def DefLanguage.evaluateFileVia (s : String) : Except Diag (D.evaluatedStageOn f).Carrier :=
  (D.evalPipelineVia f hidem htyped).abstract s.toList

/-- Render an evaluated program canonically. -/
def DefLanguage.renderEvaluatedVia (q : (D.evaluatedStageOn f).Carrier) : String :=
  String.ofList ((D.evalPipelineVia f hidem htyped).realize
    ((D.evalPipelineVia f hidem htyped).default (a := q)))

/-- **The whole front end round-trips, preparation included.** -/
theorem DefLanguage.evaluateFileVia_renderEvaluatedVia (q : (D.evaluatedStageOn f).Carrier) :
    D.evaluateFileVia f hidem htyped (D.renderEvaluatedVia f hidem htyped q) = .ok q := by
  show (D.evalPipelineVia f hidem htyped).abstract (String.ofList
    ((D.evalPipelineVia f hidem htyped).realize
      ((D.evalPipelineVia f hidem htyped).default (a := q)))).toList = .ok q
  rw [String.toList_ofList]
  exact (D.evalPipelineVia f hidem htyped).abstract_realize q _

/-- Stepping through the stages reads a file exactly as collapsing them does. -/
theorem DefLanguage.evalChainVia_abstract (name : String) (cs : List Char) :
    (D.evalChainVia f hidem htyped name).compose.hom.abstract cs =
      (D.evalPipelineVia f hidem htyped).abstract cs := by
  have h1a : ((D.toLanguage.parseChain.cons (Z := D.preparedStage f name)
      ⟨_, Abstraction.ofIdempotent f hidem⟩).compose.hom.abstract cs) =
      (D.toLanguage.parsePipeline.comp (Abstraction.ofIdempotent f hidem)).abstract cs := by
    rw [Chain.compose_cons, OneCell.hcomp_abstract]
    exact Abstraction.compAbstract_congr _ _ _ _ _ (D.toLanguage.parseChain_abstract cs)
      (D.toLanguage.parseChain_locate cs) rfl
  have h1l : ((D.toLanguage.parseChain.cons (Z := D.preparedStage f name)
      ⟨_, Abstraction.ofIdempotent f hidem⟩).compose.hom.locate cs) =
      (D.toLanguage.parsePipeline.comp (Abstraction.ofIdempotent f hidem)).locate cs := by
    rw [Chain.compose_cons]
    exact Abstraction.comp_locate_congr _ _ _ _ _ (D.toLanguage.parseChain_abstract cs)
      (D.toLanguage.parseChain_locate cs) rfl
  have h2a := Abstraction.compAbstract_congr _ _
    (D.elabWalk.stageOn (D.elab_lawfulOn_prepared f htyped))
    (D.elabWalk.stageOn (D.elab_lawfulOn_prepared f htyped)) cs h1a h1l rfl
  have h2l := Abstraction.comp_locate_congr _ _
    (D.elabWalk.stageOn (D.elab_lawfulOn_prepared f htyped))
    (D.elabWalk.stageOn (D.elab_lawfulOn_prepared f htyped)) cs h1a h1l rfl
  have h2a' : (((D.toLanguage.parseChain.cons (Z := D.preparedStage f name)
      ⟨_, Abstraction.ofIdempotent f hidem⟩).cons (Z := D.elaboratedStageOn f)
      (D.toLanguage.walkCellOn D.elabWalk (D.elab_lawfulOn_prepared f htyped))).compose.hom.abstract
        cs) = ((D.toLanguage.parsePipeline.comp (Abstraction.ofIdempotent f hidem)).comp
          (D.elabWalk.stageOn (D.elab_lawfulOn_prepared f htyped))).abstract cs := by
    rw [Chain.compose_cons, OneCell.hcomp_abstract]
    exact h2a
  have h2l' : (((D.toLanguage.parseChain.cons (Z := D.preparedStage f name)
      ⟨_, Abstraction.ofIdempotent f hidem⟩).cons (Z := D.elaboratedStageOn f)
      (D.toLanguage.walkCellOn D.elabWalk (D.elab_lawfulOn_prepared f htyped))).compose.hom.locate
        cs) = ((D.toLanguage.parsePipeline.comp (Abstraction.ofIdempotent f hidem)).comp
          (D.elabWalk.stageOn (D.elab_lawfulOn_prepared f htyped))).locate cs := by
    rw [Chain.compose_cons]
    exact h2l
  rw [evalChainVia, Chain.compose_cons, OneCell.hcomp_abstract]
  exact Abstraction.compAbstract_congr _ _ _ _ _ h2a' h2l' rfl

/-- What the driver relies on: running the chain over a file agrees with `evaluateFileVia`. -/
theorem DefLanguage.evalChainVia_run (name : String) (s : String) :
    (((D.evalChainVia f hidem htyped name).run s.toList).2.map Prod.fst).toOption =
      (D.evaluateFileVia f hidem htyped s).toOption :=
  ((D.evalChainVia f hidem htyped name).run_eq_abstract _).trans
    (congrArg Except.toOption (D.evalChainVia_abstract f hidem htyped name _))

end Prepared

end LambdaLab.Pipeline
