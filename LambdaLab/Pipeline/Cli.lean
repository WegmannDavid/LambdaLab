import LambdaLab.Pipeline.Compose

/-!
# A command-line front end, shared by every language

`Compose.lean` assembles a `Language` into a chain of stages from source text to a program. This
turns that into a program you can run: read the files named on the command line, report what
happened, exit non-zero if anything failed.

## Why one driver rather than one per language

The only thing a language contributes is its chain — source text in, and however many stages it
has. `compile` turns any chain into `Bool → String → Except String String`: rendered output or an
error message out, the flag saying whether to show the working. Everything else (argument handling,
reading files, choosing a stream to print on, the exit code) is the same for all of them, so it is
written once here and each executable is three lines. A language passes whichever chain it has —
`Float` has no type system, so it passes its parser and its one walk, `floatChain`.

## `--stages`

`compile` is `Chain.report`, so it does not enumerate the stages and does not know how many there
are; adding a stage to a chain shows up here with no edit. `--stages` prints the input at every
stage rather than only the last — up to the stage that rejected it, if one did.

## Diagnostics

A rejection carries the rejecting stage's diagnostic, its location already pulled back through
the earlier stages to a character span of the source (`Chain.run`). The driver turns that span into
`file:line:col` and shows the source line with the span marked, the way compilers do.
`Language.parseChain_run`, `DefLanguage.elabChain_run` and `DefLanguage.evalChain_run` prove that
what is printed without the flag is what `parseFile`/`elaborateFile`/`evaluateFile` would have
said, so the readable version and the composite version are not two different compilers.

## No paths are baked in

The files to process come from `argv` and nowhere else. There is no default directory and no
default file: a run with no arguments is a usage error, exactly as a compiler behaves.
-/

namespace LambdaLab.Pipeline

/-- **A chain, as a compiler**: source in, the last stage's rendering out — or every stage's, with
`showStages`. Parse failure and type failure *are* distinguished, and without any stage having to
say so: the chain names the stage it did not reach. -/
def compile {Y : Abstraction.Stage} (c : Abstraction.Chain sourceStage Y) (showStages : Bool)
    (src : String) :
    Except (List Abstraction.Step × Abstraction.Failure) String :=
  c.report showStages src.toList

/-- The line and column, both counted from `1`, of a character offset. -/
def lineCol (src : List Char) (off : Nat) : Nat × Nat :=
  let before := src.take off
  ((before.filter (· == '\n')).length + 1, (before.reverse.takeWhile (· != '\n')).length + 1)

/-- **A diagnostic, as a compiler prints it**: `path:line:col: error: message`, then the source
line with the span underlined — to the end of the line, if the span runs past it. -/
def renderDiag (path : String) (src : String) (d : Diag) : String :=
  match d.loc with
  | .chars lo hi =>
      let cs := src.toList
      let (line, col) := lineCol cs lo
      let text := String.ofList ((cs.drop (lo - (col - 1))).takeWhile (· != '\n'))
      let width := max 1 (min (hi - lo) (text.length - (col - 1)))
      let gutter := toString line
      let pad := String.ofList (List.replicate gutter.length ' ')
      s!"{path}:{line}:{col}: error: {d.msg}\n{pad} |\n{gutter} | {text}\n{pad} | " ++
        String.ofList (List.replicate (col - 1) ' ') ++ String.ofList (List.replicate width '^')
  | _ => s!"{path}: error: {d.msg}"

/-- Usage text, on the same shape every language's executable shares. -/
def usage (name ext : String) : String :=
  s!"usage: {name} [--stages] PATH...\n\
     \n\
     Each PATH is a source file, or a directory to search recursively for `.{ext}` files.\n\
     Writes the canonical rendering of each to stdout, diagnostics to stderr.\n\
     Exits non-zero if any path is missing, unreadable, or rejected.\n\
     \n\
     --stages  show the input at every stage of the pipeline, not only the result."

/-- Every `.ext` file at or under `p`, in a deterministic order.

Sorted by name at each level, so a directory argument gives the same output every run — a tool
whose output depends on `readDir`'s order is not much use in a pipe or a test. An explicitly named
file is *not* filtered by extension: naming it is the instruction. -/
partial def filesUnder (ext : String) (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let entries := (← p.readDir).qsort (fun a b => decide (a.fileName < b.fileName))
    let mut acc := #[]
    for e in entries do
      acc := acc ++ (← filesUnder ext e.path)
    return acc
  else
    return if p.extension == some ext then #[p] else #[]

/-- Turn one command-line argument into the files it names, or say why it names none. -/
def expand (ext : String) (path : String) : IO (Except String (Array System.FilePath)) := do
  let p : System.FilePath := path
  if !(← p.pathExists) then
    return .error "error: no such file or directory"
  if ← p.isDir then
    let files ← filesUnder ext p
    if files.isEmpty then
      return .error s!"error: no .{ext} files under this directory"
    return .ok files
  return .ok #[p]

/-- Process one file. Diagnostics go to stderr and output to stdout, so the result of a successful
run can be piped without stripping anything. Returns whether it succeeded.

The read is guarded: a path can exist and still not be readable — a directory, a broken symlink, a
permissions problem — and an unhandled `IO.Error` reaches the user as `uncaught exception`, which
is not a diagnostic. -/
def processFile (ext : String) (showStages : Bool)
    (compile : String → Except (List Abstraction.Step × Abstraction.Failure) String)
    (path : System.FilePath) : IO Bool := do
  match ← (IO.FS.readFile path).toBaseIO with
  | .error e =>
      IO.eprintln s!"{path}: error: {e}"
      return false
  | .ok src =>
      match compile src with
      | .error (steps, f) =>
          if showStages then
            for st in steps do
              IO.println s!"== {st.stage} ==\n{st.text}"
            (← IO.getStdout).flush
          IO.eprintln (renderDiag path.toString src f.diag)
          -- Only on failure, and only when the suffix disagrees: pointing a language's compiler
          -- at another language's file fails for a reason the parse error never mentions, and
          -- that is a confusing way to spend ten minutes. Saying it unconditionally would nag at
          -- the deliberate case, which stays allowed.
          if path.extension != some ext then
            IO.eprintln s!"{path}: note: this is not a .{ext} file — wrong compiler?"
          return false
      | .ok out =>
          IO.println out
          return true

/-- **The driver.** Every file named on the command line is processed, rather than stopping at the
first failure — a compiler that reports one error per run is annoying to use. The exit code is 0
only if all of them succeeded. -/
def cli (name ext : String)
    (compile : Bool → String → Except (List Abstraction.Step × Abstraction.Failure) String)
    (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    IO.println (usage name ext)
    return 0
  let showStages := args.contains "--stages"
  let paths := args.filter (· != "--stages")
  if paths.isEmpty then
    IO.eprintln (usage name ext)
    return 1
  let compile := compile showStages
  let mut failed := false
  for arg in paths do
    match ← expand ext arg with
    | .error msg =>
        IO.eprintln s!"{arg}: {msg}"
        failed := true
    | .ok files =>
        for path in files do
          unless ← processFile ext showStages compile path do failed := true
  return if failed then 1 else 0

end LambdaLab.Pipeline
