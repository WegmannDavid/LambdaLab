import LambdaLab.Arith
import LambdaLab.Stlc.Named.Lang
import LambdaLab.Language.Pipeline

/-!
# Vernacular demo — two plugged-in languages, one derived pipeline

Reads a source file, parses it through the framework-derived `List Char ⇝ Program` pipeline of
the language matching its extension, and prints the program back out as normalised source:

* `.arith` — `def NAME : TYPE := EXPR`, types `N`/`Z`/`R` with `→`, mixfix arithmetic terms
  (truncated: redundant parens are forgotten and re-inserted canonically);
* `.stlc`  — types `⋆` with `→`, lambda-calculus terms `λ x . e` (multi-entry grammar;
  binder parens and redundant parens truncate away), **and type checked**: `.stlc` files are run
  through `stlcElaboratable.elaborateFile`, the parse-and-elaborate pipeline, which is one `Abs`
  morphism covering both stages. Elaboration rejects a declaration whose type is not ground, so
  `def poly : ?0 → ?0 := …` parses and then fails to elaborate — the two stages fail
  independently, which is the point of their being separate morphisms.

* `lake exe playground`                — parse the bundled `examples/demo.{arith,stlc}`
* `lake exe playground path/to/file`   — parse the given file (language by extension)

`parseFile`/`renderProgram` are `Language.pipeline`'s API — the whole front end is one `Abs`
morphism per language. The *parsers* run verified code; the round-trip *proofs* are still
conditional on the open mixfix `ok` lemma. The executable exercises the parsers, not the proofs.
-/

open LambdaLab.Language LambdaLab.Arith LambdaLab.Stlc.Named

/-- Parse `src` with `L`, then re-render it canonically. `none` if not a well-formed program. -/
def roundtripWith (L : Language) (src : String) : Option String := do
  let prog ← L.parseFile src
  some (L.renderProgram prog)

/-- Parse *and* elaborate `src`, then re-render the elaborated program. This is the composite
`List Char ⇝ … ⇝ elaborated Program`, not two passes glued by hand. -/
def typecheckStlc (src : String) : Option String := do
  let prog ← stlcElaboratable.elaborateFile src
  some (stlcElaboratable.renderElaborated prog)

/-- Pick the language from the file extension (default: arith). `.stlc` also gets a type checker;
`arith` has no semantics attached, so it stops after parsing. -/
def languageFor (path : String) : Language × Option (String → Option String) :=
  if path.endsWith ".stlc" then (stlcLanguage, some typecheckStlc) else (arithLanguage, none)

def run (label : String) (L : Language) (check : Option (String → Option String))
    (src : String) : IO Unit := do
  IO.println s!"── {label} ──"
  IO.println "input:"
  for line in ((src.splitOn "\n").filter (fun l => !l.isEmpty)) do
    IO.println s!"  {line}"
  match roundtripWith L src with
  | some out =>
      IO.println "parsed & re-rendered:"
      IO.println s!"  {out}"
  | none => IO.println "  ⟹  rejected (not a well-formed program)"
  match check with
  | none => pure ()
  | some f =>
      match f src with
      | some out =>
          IO.println "type-checked & re-rendered:"
          IO.println s!"  {out}"
      | none => IO.println "  ⟹  parses, but does not elaborate"
  IO.println ""

def runPath (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  let (L, check) := languageFor path
  run path L check src

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
      runPath "examples/demo.arith"
      runPath "examples/demo.stlc"
      runPath "examples/demo-typed.stlc"
  | path :: _ => runPath path
