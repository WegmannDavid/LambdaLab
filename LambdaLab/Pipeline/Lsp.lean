import LambdaLab.Pipeline.Cli
import LambdaLab.Pipeline.Json

/-!
# A language server, shared by every language

`Cli.lean` turns a language's chain into a compiler. This turns the same chain into a **language
server** — the process an editor starts and talks to over the Language Server Protocol (JSON-RPC
messages on stdin and stdout) — so the editor can check a file as it is typed. Like the compiler, it
is written once: what a language contributes is its `Language` and its chain.

What it offers:

* **diagnostics** — on every change the chain runs, and every failure it reports (`Chain.report`,
  which recovers past what it can) is published at its span;
* **document symbols** — the outline: every declaration, under its name. A declaration is found the
  way the parse stage finds it, by its keyword, and its name is the token after the keyword;
* **formatting** — the parsed program in its canonical layout. That cannot change what the file
  means: rendering a program and parsing it back gives the same program, which is the round-trip
  law of the parse pipeline (`Language.parsePipeline`).

The editor keeps the whole text and sends all of it on each change (full synchronization).
Positions are counted the way the protocol counts them, in UTF-16 code units within a line.

Plumbing: informal, nothing proved — like the compiler driver.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Abstraction (Chain Stage tokenSpans)
open LambdaLab.Parser.IsoParser (Token tokens)

/-! ## Messages on the wire

Each message is a header — `Content-Length`, counting bytes of UTF-8 — a blank line, and a JSON
body. -/

/-- Read exactly `n` bytes, or what there is before the end of input. -/
partial def readBytes (h : IO.FS.Stream) (n : Nat) (acc : ByteArray := .empty) : IO ByteArray := do
  if acc.size ≥ n then return acc
  let chunk ← h.read (n - acc.size).toUSize
  if chunk.isEmpty then return acc
  readBytes h n (acc ++ chunk)

/-- Read one message; `none` at the end of input. -/
partial def readMessage (h : IO.FS.Stream) : IO (Option Json) := do
  let mut len : Option Nat := none
  repeat
    let line ← h.getLine
    if line.isEmpty then return none
    let line := line.trimAsciiEnd.toString
    if line.isEmpty then break
    if line.startsWith "Content-Length:" then
      len := (line.drop "Content-Length:".length).trimAscii.toString.toNat?
  match len with
  | none => readMessage h
  | some n =>
      let bytes ← readBytes h n
      match String.fromUTF8? bytes with
      | some s => return (Json.parse s).getD .null
      | none => return some .null

/-- Write one message. -/
def writeMessage (h : IO.FS.Stream) (j : Json) : IO Unit := do
  let body := j.render
  h.putStr s!"Content-Length: {body.utf8ByteSize}\r\n\r\n{body}"
  h.flush

def respond (h : IO.FS.Stream) (id : Json) (result : Json) : IO Unit :=
  writeMessage h (.mkObj [("jsonrpc", "2.0"), ("id", id), ("result", result)])

def respondError (h : IO.FS.Stream) (id : Json) (code : Int) (msg : String) : IO Unit :=
  writeMessage h (.mkObj [("jsonrpc", "2.0"), ("id", id),
    ("error", .mkObj [("code", .num code), ("message", .str msg)])])

def notify (h : IO.FS.Stream) (method : String) (params : Json) : IO Unit :=
  writeMessage h (.mkObj [("jsonrpc", "2.0"), ("method", .str method), ("params", params)])

/-! ## Positions -/

/-- How many UTF-16 code units a character takes. -/
def utf16Len (c : Char) : Nat := if c.toNat > 0xFFFF then 2 else 1

/-- The protocol's position of a character offset: line, and UTF-16 units into it. -/
def lspPos (cs : List Char) (off : Nat) : Json :=
  let before := cs.take off
  let line : Nat := (before.filter (· == '\n')).length
  let col : Nat := ((before.reverse.takeWhile (· != '\n')).map utf16Len).foldl (· + ·) 0
  .mkObj [("line", .num line), ("character", .num col)]

def lspRange (cs : List Char) (lo hi : Nat) : Json :=
  .mkObj [("start", lspPos cs lo), ("end", lspPos cs hi)]

/-! ## What the server computes -/

/-- **Diagnostics**: every failure the chain reports, at its span. -/
def diagnosticsOf {Y : Stage} (name : String) (c : Chain sourceStage Y) (text : String) : Json :=
  let cs := text.toList
  match c.report false cs with
  | .ok _ => .arr #[]
  | .error (_, fs) =>
      .arr (fs.toArray.map fun f =>
        let range := match f.diag.loc with
          | .chars lo hi => lspRange cs lo hi
          | _ => lspRange cs 0 0
        .mkObj [("range", range), ("severity", 1), ("source", .str name),
          ("message", .str f.diag.msg)])

/-- The kind of symbol a declaration form declares, by its keyword. -/
def symbolKind (kw : String) : Nat :=
  if kw == "inductive" then 10       -- Enum
  else if kw == "type" then 26       -- TypeParameter
  else if kw == "float" then 13      -- Variable
  else 12                            -- Function

/-- **The outline**: each declaration, from its keyword to the next one, named by the token after
its keyword. -/
def symbolsOf (L : Language) (text : String) : Json :=
  let cs := text.toList
  let ts := tokens L.lex cs
  let spans := (tokenSpans L.lex cs 0).toArray
  let starts := L.declStarts ts
  .arr <| (List.range starts.length).toArray.filterMap fun k => do
    let i ← starts[k]?
    let kw ← ts[i]?
    let nm ← ts[i + 1]?
    let (lo, _) ← spans[i]?
    let (nlo, nhi) ← spans[i + 1]?
    let last := ((starts[k + 1]?).getD ts.length) - 1
    let (_, hi) ← spans[last]?
    pure <| .mkObj [("name", .str nm.val), ("detail", .str kw.val),
      ("kind", .num (symbolKind kw.val)), ("range", lspRange cs lo hi),
      ("selectionRange", lspRange cs nlo nhi)]

/-- **Formatting**: the parsed program in its canonical layout, replacing the whole text — or
nothing, if the text does not parse. -/
def formattingOf (L : Language) (text : String) : Json :=
  match L.parseFile text with
  | .ok prog =>
      let cs := text.toList
      .arr #[.mkObj [("range", lspRange cs 0 cs.length),
        ("newText", .str (L.renderProgram prog ++ "\n"))]]
  | .error _ => .arr #[]

/-! ## The server -/

/-- What the server answers `initialize` with. -/
def capabilities (name : String) : Json :=
  .mkObj [
    ("capabilities", .mkObj [
      ("textDocumentSync", 1),
      ("documentSymbolProvider", true),
      ("documentFormattingProvider", true)]),
    ("serverInfo", .mkObj [("name", .str s!"lambdalab-{name}")])]

/-- **The server**: read messages until the editor says `exit` or closes the stream. -/
partial def serve {Y : Stage} (name : String) (L : Language) (c : Chain sourceStage Y) :
    IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let docs ← IO.mkRef ([] : List (String × String))
  let publish (uri text : String) : IO Unit :=
    notify stdout "textDocument/publishDiagnostics"
      (.mkObj [("uri", .str uri), ("diagnostics", diagnosticsOf name c text)])
  let textOf (uri : String) : IO String := do
    return (((← docs.get).find? (·.1 == uri)).map (·.2)).getD ""
  let rec loop : IO Unit := do
    let some msg ← readMessage stdin | return
    let method := (msg.get? "method").bind Json.str?
    let id := msg.get? "id"
    let params := (msg.get? "params").getD .null
    let uri := (params.getStr? ["textDocument", "uri"]).getD ""
    match method, id with
    | some "initialize", some id => respond stdout id (capabilities name); loop
    | some "shutdown", some id => respond stdout id .null; loop
    | some "exit", _ => return
    | some "textDocument/didOpen", _ =>
        let text := (params.getStr? ["textDocument", "text"]).getD ""
        docs.modify fun ds => (uri, text) :: ds.filter (·.1 != uri)
        publish uri text
        loop
    | some "textDocument/didChange", _ =>
        let changes := ((params.get? "contentChanges").bind Json.arr?).getD #[]
        match changes.back? |>.bind (·.getStr? ["text"]) with
        | some text =>
            docs.modify fun ds => (uri, text) :: ds.filter (·.1 != uri)
            publish uri text
        | none => pure ()
        loop
    | some "textDocument/didClose", _ =>
        docs.modify fun ds => ds.filter (·.1 != uri)
        notify stdout "textDocument/publishDiagnostics"
          (.mkObj [("uri", .str uri), ("diagnostics", .arr #[])])
        loop
    | some "textDocument/documentSymbol", some id =>
        respond stdout id (symbolsOf L (← textOf uri)); loop
    | some "textDocument/formatting", some id =>
        respond stdout id (formattingOf L (← textOf uri)); loop
    | some m, some id => respondError stdout id (-32601) s!"unsupported method {m}"; loop
    | _, _ => loop
  loop

/-- **An executable's `main`**: the language server with `--lsp`, the compiler otherwise. -/
def driver {Y : Stage} (name ext : String) (L : Language) (c : Chain sourceStage Y)
    (args : List String) : IO UInt32 := do
  if args.contains "--lsp" then
    serve name L c
    return 0
  else cli name ext (compile c) args

end LambdaLab.Pipeline
