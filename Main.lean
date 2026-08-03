import LambdaLab.Arith
import LambdaLab.Stlc.Named.Lang
import LambdaLab.Pipeline.Pipeline

/-!
# Vernacular demo — two plugged-in languages, one derived pipeline

Reads a source file, parses it through the framework-derived `List Char ⇝ Program` pipeline of
the language matching its extension, and prints the program back out as normalised source:

* `.arith` — `def NAME : TYPE := EXPR`, types `N`/`Z`/`R` with `→`, mixfix arithmetic terms
  (truncated: redundant parens are forgotten and re-inserted canonically);
* `.stlc`  — types `⋆` with `→`, lambda-calculus terms `λ x . e` (multi-entry grammar;
  binder parens and redundant parens truncate away), **and elaborated**: `.stlc` files are run
  through `elaborateFile`, the parse-and-elaborate pipeline, which is one `Abs` morphism covering
  both stages. Elaboration solves metavariables by constraint generation, so `def id : ?0 → ?0 :=
  λ x : ⋆ . x` comes back as `⋆ → ⋆`, and then refuses to let any *unsolved* one survive a
  declaration.

* `lake exe playground`                — parse the bundled `examples/demo.{arith,stlc}`
* `lake exe playground path/to/file`   — parse the given file (language by extension)

`parseFile`/`renderProgram` are `Language.pipeline`'s API — the whole front end is one `Abs`
morphism per language. The *parsers* run verified code; the round-trip *proofs* are still
conditional on the open mixfix `ok` lemma. The executable exercises the parsers, not the proofs.
-/

open LambdaLab.Pipeline LambdaLab.Arith LambdaLab.Stlc.Named

/-- Parse `src` with `L`, then re-render it canonically. `none` if not a well-formed program. -/
def roundtripWith (L : Language) (src : String) : Option String := do
  let prog ← L.parseFile src
  some (L.renderProgram prog)

/-- Pick the language from the file extension (default: arith), together with the elaborators to
run after parsing. `arith` has no semantics attached, so it stops after parsing; `.stlc` gets
both metavariable policies, which differ only in whether an unsolved `?n` may survive a
declaration. Each is `elaborateFile`, the composite `List Char ⇝ … ⇝ elaborated Program` — not
two passes glued together here. -/
def languageFor (path : String) : Language × List (String × (String → Option String)) :=
  if path.endsWith ".stlc" then
    (stlcLanguage, [("elaborated", elaborateSource)])
  else (arithLanguage, [])

def run (label : String) (L : Language) (checks : List (String × (String → Option String)))
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
  for (name, f) in checks do
    match f src with
    | some out =>
        IO.println s!"{name}:"
        IO.println s!"  {out}"
    | none => IO.println s!"{name}:  ⟹  rejected"
  IO.println ""

def runPath (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  let (L, checks) := languageFor path
  run path L checks src

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
      runPath "examples/demo.arith"
      runPath "examples/demo.stlc"
  | path :: _ => runPath path
