import LambdaLab.Pipeline.Basic
import LambdaLab.Parser.IsoParser.Notation

/-!
# The file parser, derived from a language's forms

A `Language` supplies its declaration forms: a keyword and a body parser for each. *Everything*
here is derived from them — the declaration parser, the file parser, the round-trip proof, and the
`Abs` morphism.

```
declaration  =  keyword of form f, then f's body        (formIso, then dispatch on the keyword)
file         =  one or more declarations                (many1)
```

**The derivation strategy.** The `IsoParser` combinator layer (`gdo`, `tok`, `dispatch`, `comap`,
`many1`) is reused, not cloned: each lossy body crosses into it as an `IsoParser` over its
*annotated values* (`toIsoParser`, whose printed value is the index — definitionally), the
combinators assemble the grammar with the **annotated declaration/program as the source**, and the
assembled parser crosses back (`toLossyParserSigma`) once its printed value is shown to be the
index (`echo` — the `Iso`'s inverse law, plus one induction for `many1`).

**The seams.** Into a body: the keyword's FOLLOW is `⊤`. Out of a body: its FOLLOW admits every
keyword, which is exactly what the next declaration starts with. Between declarations: a
declaration's FIRST is the keywords and its FOLLOW is the keywords, so `many1`'s repetition
obligation is the inclusion of one in the other. None of them asks anything of a language beyond
`Language.body`'s type.

**The payoff:** `Language.abstraction` — every language yields an `Abs` morphism
`List Token ⇝ Program`.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Parser.IsoParser
open LambdaLab.Parser.LossyParser (LossyParser)
open LambdaLab (Abstraction)

variable (L : Language)

/-! ## A declaration -/

/-- One form: its keyword, then its body. The source is the annotated body. -/
def Language.formIso (f : L.Form) :
    IsoParser (Token L.lex) (· = L.head f) (fun t => t ∈ L.heads)
      (Σ b : L.Body f, L.BodyAnn f b) (L.Body f) := gdo
  let _kw ← tok (L.head f)
  let b ← (L.body f).toIsoParser
  return b

/-- Any form, chosen by its keyword. -/
def Language.formsIso :
    IsoParser (Token L.lex) (fun c => ∃ f, c = L.head f) (fun t => t ∈ L.heads)
      (Σ f, Σ b : L.Body f, L.BodyAnn f b) (Σ f, L.Body f) :=
  dispatch L.head L.formOf L.formOf_head L.formIso

/-- **The declaration parser**: the source is the annotated declaration, read through `decl` as a
form and an annotated body. -/
def Language.declIso :
    IsoParser (Token L.lex) (fun c => ∃ f, c = L.head f) (fun t => t ∈ L.heads)
      (Σ d : L.Decl, L.DeclAnn d) L.Decl :=
  map L.decl.invFun
    (comap (fun s => ⟨(L.decl.toFun s.1).1, (L.decl.toFun s.1).2, s.2⟩) L.formsIso)

/-- The declaration parser prints the declaration it is indexed by: each body prints its own
index, so the form-and-body printed is `decl s.1`, and `decl`'s inverse takes it back. -/
theorem Language.declIso_echo (s : Σ d : L.Decl, L.DeclAnn d) : (L.declIso.print s).1 = s.1 := by
  show L.decl.invFun (L.decl.toFun s.1) = s.1
  exact L.decl.left_inv s.1

/-- A declaration's canonical spelling: its body's. -/
def Language.defaultDeclAnn (d : L.Decl) : L.DeclAnn d := (L.body (L.decl.toFun d).1).default

/-! ## The program -/

/-- Annotations for every declaration of a list. -/
def ListAnn : List L.Decl → Type
  | [] => PUnit
  | d :: ds => L.DeclAnn d × ListAnn ds

/-- Annotations for every declaration of a program: the full surface spelling of a file. -/
def Program.Ann (prog : Program L) : Type :=
  L.DeclAnn prog.1 × ListAnn L prog.2

def defaultListAnn : (ds : List L.Decl) → ListAnn L ds
  | [] => PUnit.unit
  | d :: ds => (L.defaultDeclAnn d, defaultListAnn ds)

/-- Zip a declaration list with its annotations into `many1`'s source shape. -/
def zipAnnList : (ds : List L.Decl) → ListAnn L ds → List (Σ d : L.Decl, L.DeclAnn d)
  | [], _ => []
  | d :: ds, (a, as) => ⟨d, a⟩ :: zipAnnList ds as

/-- The file parser at the `IsoParser` level: `many1` over `declIso`, with the source reshaped
from `Σ prog, annotations` to `many1`'s list-of-`Σ`. A declaration's FIRST is the keywords and so
is its FOLLOW, so the repetition obligation is that every FIRST token is a keyword. -/
def Language.parserIso :
    IsoParser (Token L.lex) (fun c => ∃ f, c = L.head f)
      (fun t => t ∈ L.heads ∧ ¬ ∃ f, t = L.head f)
      (Σ prog : Program L, Program.Ann L prog) (NEList L.Decl) :=
  comap (fun s => (⟨s.1.1, s.2.1⟩, zipAnnList L s.1.2 s.2.2))
    (many1 L.declIso (by rintro c ⟨f, rfl⟩; exact L.head_mem_heads f))

/-- `many1`'s printed values over a zipped source are the original declarations. -/
theorem Language.printV_zipAnnList :
    ∀ (ds : List L.Decl) (as : ListAnn L ds), many1PrintV L.declIso (zipAnnList L ds as) = ds
  | [], _ => rfl
  | d :: ds, (a, as) => by
      simp only [zipAnnList, many1PrintV, Language.printV_zipAnnList ds as, L.declIso_echo ⟨d, a⟩]

/-- The file parser prints the program it is indexed by. -/
theorem Language.parserIso_echo (s : Σ prog : Program L, Program.Ann L prog) :
    (L.parserIso.print s).1 = s.1 := by
  show ((L.declIso.print ⟨s.1.1, s.2.1⟩).1,
    many1PrintV L.declIso (zipAnnList L s.1.2 s.2.2)) = s.1
  rw [L.declIso_echo ⟨s.1.1, s.2.1⟩, L.printV_zipAnnList s.1.2 s.2.2]

/-- **The file parser, lossy**: value `Program L`, annotation the full surface spelling. Canonical
print = every declaration in canonical form. -/
def Language.parser :
    LossyParser (Token L.lex) (fun c => ∃ f, c = L.head f)
      (fun t => t ∈ L.heads ∧ ¬ ∃ f, t = L.head f)
      (Program L) (Program.Ann L) :=
  L.parserIso.toLossyParserSigma
    (fun {prog} => (L.defaultDeclAnn prog.1, defaultListAnn L prog.2))
    L.parserIso_echo

/-- **The file round-trip.** Print a program under *any* spelling, parse it back, recover the
program exactly with nothing left over — for every language, no side-conditions. -/
theorem Language.parser_roundtrip (prog : Program L) (ann : Program.Ann L prog) :
    L.parser.run (L.parser.print ann) = some (prog, []) :=
  L.parser.roundtrip prog ann

/-! ## The stage -/

/-- The parse stage's annotation family: **every token list that parses to this program**.

The tautological fiber, rather than `Program.Ann`'s structured account of a spelling. Both give the
same canonical print — `saturate` keeps `default` where it was — but only this one makes the stage
complete without a proof, since an annotation *is* an accepted input.

`Program.Ann` has not gone anywhere: it is still what `L.parser` prints from, and still what the
layout in `Compose.lean` is written against. It is no longer what indexes the *morphism*. -/
abbrev Language.ParseAnn (prog : Program L) : Type :=
  { ts : List (Token L.lex) // L.parser.wholeInput ts = some prog }

/-- **Every language is an `Abs` morphism** `List Token ⇝ Program`: the whole-file abstraction,
whose annotation is every token list the program can be written as. Composes with the tokenizer
(`Abstraction/Tokenizer.lean`) for the `List Char` pipeline. -/
def Language.abstraction : Abstraction (List (Token L.lex)) (Program L) (Language.ParseAnn L) :=
  L.parser.toAbstraction

/-- **The parse stage forgets nothing** — a projection, not a theorem. What the structured family
`Program.Ann` would have cost is `Exact` for `L.parser`, and through it exactness for every
combinator it is built from (`tok`, `bind`, `dispatch`, `comap`, `many1`); the tautological family
reaches the same conclusion with none of it, and `LossyParser.toAbstractionOfExact` is waiting for
the day those land. -/
theorem Language.abstraction_lossless (ts : List (Token L.lex)) (prog : Program L)
    (h : L.abstraction.abstract ts = some prog) :
    ∃ ann : Language.ParseAnn L prog, L.abstraction.realize ann = ts :=
  L.abstraction.lossless ts prog h

end LambdaLab.Pipeline
