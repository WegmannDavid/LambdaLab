import LambdaLab.Language1.Arith

/-!
# Arithmetic vernacular demo

Reads a source file in the `arithLanguage` vernacular — `def NAME : (N|Z|R) := EXPR`, one command
per declaration, `EXPR` a mixfix arithmetic expression — parses it, and prints the AST back out as
normalised source. Round-tripping the text is the whole point: the printed form is what the parser
would read back to the same tree.

* `lake exe playground`                — parse the bundled `examples/demo.arith`
* `lake exe playground path/to/file`   — parse the given file

Note: the *parser* here is the verified mixfix parser; the round-trip *proof* for this language is
still conditional on the open unambiguity lemmas (see `LambdaLab/Language1/Arith.lean`). The
executable exercises the running parser, not the proof.
-/

open LambdaLab.Language1

/-- Recover a non-empty program from the flat command list `parseFile` returns. -/
def toProgram : List (Command arithLanguage) → Option (Program arithLanguage)
  | []      => none
  | c :: cs => some (c, cs)

/-- Parse `src`, then re-render it. `none` if the file is not a well-formed program.

`parseFile` requires the *entire* character stream to be consumed, but the tokenizer leaves any
trailing whitespace (a final newline, say) as leftover characters even though it tokenizes to
nothing. Trimming is a preprocessing choice on the way in — it does not touch the verified core,
and `renderProgram` never emits trailing separators, so the round-trip theorem is unaffected. -/
def roundtrip (src : String) : Option String := do
  let cmds ← arithLanguage.parseFile src.trim
  let prog ← toProgram cmds
  some (arithLanguage.renderProgram prog)

def run (label : String) (src : String) : IO Unit := do
  IO.println s!"── {label} ──"
  IO.println "input:"
  for line in ((src.splitOn "\n").filter (fun l => !l.isEmpty)) do
    IO.println s!"  {line}"
  match roundtrip src with
  | some out =>
      IO.println "parsed & re-rendered:"
      for line in out.splitOn "\n" do IO.println s!"  {line}"
  | none => IO.println "  ⟹  rejected (not a well-formed program)"
  IO.println ""

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
      let path := "examples/demo.arith"
      let src ← IO.FS.readFile path
      run path src
  | path :: _ =>
      let src ← IO.FS.readFile path
      run path src
