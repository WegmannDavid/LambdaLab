import LambdaLab

/-!
# STLC vernacular runner

CLI driver for the named-STLC vernacular parser. Reads each path given
on the command line, parses it as a sequence of vernacular commands
(`def`, `eval`, `check`), and prints the parsed result.

Usage:

```
lake exe lambdalab-stlc examples/identity.stlc
lake exe lambdalab-stlc examples/combinators.stlc examples/parse_failures.stlc
```
-/

open LambdaLab.Stlc.Named LambdaLab.Stlc.Named.Parser LambdaLab.Language

/-- The STLC vernacular language. -/
abbrev stlcLang : Language := LambdaLab.Stlc.Named.lang

/-- Render a parsed command. -/
def showCommand (c : Command stlcLang) : String :=
  match c with
  | .decl d =>
      let tyToks   : List String := Ty.toTokens   (d.type : Ty)
      let bodyToks : List String := Term.toTokens (d.body : Term)
      s!"  def {d.name} : {" ".intercalate tyToks}\n      := {" ".intercalate bodyToks}"
  | .eval e =>
      let toks : List String := Term.toTokens (e : Term)
      s!"  eval {" ".intercalate toks}"
  | .check e =>
      let toks : List String := Term.toTokens (e : Term)
      s!"  check {" ".intercalate toks}"

def runOne (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  IO.println s!"=== {path} ==="
  match parse stlcLang src with
  | none =>
      IO.println "  PARSE FAILED"
  | some cmds =>
      if cmds.isEmpty then
        IO.println "  (empty program)"
      else
        for c in cmds do
          IO.println (showCommand c)
  IO.println ""

def main (args : List String) : IO Unit := do
  if args.isEmpty then
    -- No args: run all bundled examples.
    let bundled := [
      "examples/identity.stlc",
      "examples/combinators.stlc",
      "examples/parse_failures.stlc"
    ]
    for p in bundled do
      runOne p
  else
    for p in args do
      runOne p
