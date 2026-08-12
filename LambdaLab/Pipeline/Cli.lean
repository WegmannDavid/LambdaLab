import LambdaLab.Pipeline.Compose

/-!
# A command-line front end, shared by every language

`Compose.lean` assembles a `Language` into a function from source text to a program. This turns
that into a program you can run: read the files named on the command line, report what happened,
exit non-zero if anything failed.

## Why one driver rather than one per language

The only thing a language contributes is `String → Except String String` — source in, rendered
output or an error message out. Everything else (argument handling, reading files, choosing a
stream to print on, the exit code) is the same for all of them, so it is written once here and
each executable is three lines.

Two such functions are supplied below, matching the two chains in `Compose.lean`:
`compileParse` for a language that only reads, and `compileElab` for one whose types and terms
satisfy the elaboration interface. A language picks whichever it can support — `Arith` has no type
system, so it stops at the first.

## No paths are baked in

The files to process come from `argv` and nowhere else. There is no default directory and no
default file: a run with no arguments is a usage error, exactly as a compiler behaves.
-/

namespace LambdaLab.Pipeline

/-- **Read, then re-render.** Everything a `Language` can do on its own, with no type system:
`none` from the parser becomes the error message. -/
def Language.compileParse (L : Language) (src : String) : Except String String :=
  match L.parseFile src with
  | none => .error "parse error: not a well-formed program"
  | some prog => .ok (L.renderProgram prog)

/-- **Read, then elaborate.** The same, one stage further on, for a language whose own types and
terms satisfy `PrincipalElaborate`. A `none` here means either the source did not parse or it did
not type — the two are not distinguished, because the composite is a single `Abs` morphism and
that is precisely what makes its round-trip law cover both stages. -/
def Language.compileElab (L : Language)
    [TypeSystem.PrincipalElaborate (Var L) L.Tm L.Ty] (src : String) : Except String String :=
  match L.elaborateFile src with
  | none => .error "error: not a well-formed program, or it does not elaborate"
  | some p => .ok (L.renderElaborated p)

/-- Usage text, on the same shape every language's executable shares. -/
def usage (name : String) : String :=
  s!"usage: {name} FILE...\n\
     \n\
     Reads each FILE, processes it, and writes the canonical rendering to stdout.\n\
     Exits non-zero if any file is missing, unreadable, or rejected."

/-- Process one file. Diagnostics go to stderr and output to stdout, so the result of a successful
run can be piped without stripping anything. Returns whether it succeeded. -/
def processFile (compile : String → Except String String) (path : String) : IO Bool := do
  if !(← System.FilePath.pathExists path) then
    IO.eprintln s!"{path}: error: no such file"
    return false
  match compile (← IO.FS.readFile path) with
  | .error msg =>
      IO.eprintln s!"{path}: {msg}"
      return false
  | .ok out =>
      IO.println out
      return true

/-- **The driver.** Every file named on the command line is processed, rather than stopping at the
first failure — a compiler that reports one error per run is annoying to use. The exit code is 0
only if all of them succeeded. -/
def cli (name : String) (compile : String → Except String String) (args : List String) :
    IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    IO.println (usage name)
    return 0
  if args.isEmpty then
    IO.eprintln (usage name)
    return 1
  let mut failed := false
  for path in args do
    unless ← processFile compile path do failed := true
  return if failed then 1 else 0

end LambdaLab.Pipeline
