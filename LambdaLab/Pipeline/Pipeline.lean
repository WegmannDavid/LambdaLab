import LambdaLab.Pipeline.Biparser
import LambdaLab.Abstraction.Tokenizer

/-!
# The full pipeline: fill in a `Language`, get `List Char ⇝ Program`

The last derivation step. `Biparser.lean` turns a `Language`'s two parsers into the token-level
`Abs` morphism `Language.abstraction`; composing the vernacular's tokenizer in front of it gives
**the whole front end as one `Abs` morphism** — raw characters to parsed commands, with the
composite annotation recording everything the source wrote that the program forgot:

```
Σ (spellings of every command) , (the whitespace gaps of the token rendering)
```

`abstract` is the file parser (whole input, `none` on any error), `realize` re-renders any
recorded spelling, and `realize ∘ default` is the canonical printer: canonical spellings,
single-space gaps. `parseFile`/`renderProgram` package those as the `String`-level API.

The tokenizer is instantiated at the vernacular's own separator (`isSep`, whitespace), so the
alphabet agreement between the two stages is by construction, not coincidence. Note the
tokenizer is Agda-style: tokens must be whitespace-separated — write `( x )`, not `(x)`.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Abstraction

/-- **The full pipeline** of a language: characters to program, in `Abs`. The annotation over a
program pairs a spelling of every command with the whitespace gaps of the resulting token
rendering — the composite of the two stages' annotations. -/
def Language.pipeline (L : Language) :
    Abstraction (List Char) (NEList (Command L))
      (fun prog => Σ ann : Program.Ann L prog, Gaps isSep (L.parser.print ann)) :=
  (tokenizer (sep := isSep) ' ' (by decide)).comp L.abstraction

/-- Parse a source file into a program. Whole-input: leading/trailing whitespace is fine,
anything unconsumed is not. -/
def Language.parseFile (L : Language) (s : String) : Option (Program L) :=
  L.pipeline.abstract s.toList

/-- Render a program canonically: every command in its canonical spelling, single spaces. -/
def Language.renderProgram (L : Language) (prog : Program L) : String :=
  String.ofList (L.pipeline.realize (L.pipeline.default (a := prog)))

end LambdaLab.Pipeline
