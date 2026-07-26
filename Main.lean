import LambdaLab.Arith
import LambdaLab.Stlc.Named.Lang1
import LambdaLab.Language1.Pipeline

/-!
# Vernacular demo — two plugged-in languages, one derived pipeline

Reads a source file, parses it through the framework-derived `List Char ⇝ Program` pipeline of
the language matching its extension, and prints the program back out as normalised source:

* `.arith` — `def NAME : TYPE := EXPR`, types `N`/`Z`/`R` with `→`, mixfix arithmetic terms
  (truncated: redundant parens are forgotten and re-inserted canonically);
* `.stlc`  — types `*` with `→`, lambda-calculus terms `λ x . e` (multi-entry grammar;
  binder parens and redundant parens truncate away).

* `lake exe playground`                — parse the bundled `examples/demo.{arith,stlc}`
* `lake exe playground path/to/file`   — parse the given file (language by extension)

`parseFile`/`renderProgram` are `Language.pipeline`'s API — the whole front end is one `Abs`
morphism per language. The *parsers* run verified code; the round-trip *proofs* are still
conditional on the open mixfix `ok` lemma. The executable exercises the parsers, not the proofs.
-/

open LambdaLab.Language1 LambdaLab.Arith LambdaLab.Stlc.Named

/-- Parse `src` with `L`, then re-render it canonically. `none` if not a well-formed program. -/
def roundtripWith (L : Language) (src : String) : Option String := do
  let prog ← L.parseFile src
  some (L.renderProgram prog)

/-- Pick the language from the file extension (default: arith). -/
def languageFor (path : String) : Language :=
  if path.endsWith ".stlc" then stlcLanguage else arithLanguage

def run (label : String) (L : Language) (src : String) : IO Unit := do
  IO.println s!"── {label} ──"
  IO.println "input:"
  for line in ((src.splitOn "\n").filter (fun l => !l.isEmpty)) do
    IO.println s!"  {line}"
  match roundtripWith L src with
  | some out =>
      IO.println "parsed & re-rendered:"
      IO.println s!"  {out}"
  | none => IO.println "  ⟹  rejected (not a well-formed program)"
  IO.println ""

def runPath (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  run path (languageFor path) src

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
      runPath "examples/demo.arith"
      runPath "examples/demo.stlc"
  | path :: _ => runPath path
