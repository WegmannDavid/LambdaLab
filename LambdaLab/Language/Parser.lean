import LambdaLab.Language.Basic
import LambdaLab.Parser.Mixfix.Parser

/-!
# Vernacular parser

A small command language sitting above the term/type language. Parametric
on a `Language`, which supplies the sub-parsers for types and terms.

## Surface syntax (v1)

A vernacular file is a sequence of commands terminated by `;`:

```
def NAME : TYPE := BODY ;
eval BODY ;
check BODY ;
…
```

* `def NAME : TYPE := BODY` introduces a binding and brings `NAME` into
  scope for subsequent commands.
* `eval BODY` requests the body's normal form.
* `check BODY` requests the body's type.

Future commands (`axiom`, `import`, …) extend the operator set on
`vernacularGrammar`.

## Implementation

The token stream is pre-split on `;`: each chunk is one declaration, and
the body's parser never sees the terminator (which would otherwise be
swallowed by juxtaposition since `;` is no operator's name-part in any
underlying language grammar).

A `def` chunk is parsed by a prefix mixfix operator:

```
nameParts := ["def", ":", ":="]   -- prefix arity = 3
holes     := [.sub stringSub, .sub L.typeSub, .sub L.termSub]
build     := fun n ty body => some ⟨n, ty, body⟩
```

The grammar's `α` is `Option (Decl L)` so the atom-fallback (which fires
on chunks that don't start with `def`) returns `none` rather than
silently producing a bogus `Decl`. `parseProgram` splits on `;`, then
runs `parseAll` on each chunk.
-/

namespace LambdaLab.Language

open LambdaLab.Parser.Mixfix

/-- A single top-level declaration introduced by `def`. -/
structure Decl (L : Language) where
  name : String
  type : L.Ty
  body : L.Term

/-- A vernacular command. -/
inductive Command (L : Language) where
  /-- `def NAME : TYPE := BODY` — introduces a binding. -/
  | decl  : Decl L → Command L
  /-- `eval BODY` — evaluate the term. -/
  | eval  : L.Term → Command L
  /-- `check BODY` — show the term's type. -/
  | check : L.Term → Command L

/-- The mixfix operator for `def NAME : TYPE := BODY`. -/
def declOp (L : Language) : Operator (Option (Command L)) := {
  fixity := .prefix
  nameParts := ["def", ":", ":="]
  nameParts_ne_nil := by decide
  holes := [.sub stringParser, .sub L.typeParser, .sub L.termParser]
  holes_match_arity := rfl
  build := fun (n : String) (ty : L.Ty) (b : L.Term) =>
    some (.decl { name := n, type := ty, body := b })
}

/-- The mixfix operator for `eval BODY`. -/
def evalOp (L : Language) : Operator (Option (Command L)) := {
  fixity := .prefix
  nameParts := ["eval"]
  nameParts_ne_nil := by decide
  holes := [.sub L.termParser]
  holes_match_arity := rfl
  build := fun (e : L.Term) => some (.eval e)
}

/-- The mixfix operator for `check BODY`. -/
def checkOp (L : Language) : Operator (Option (Command L)) := {
  fixity := .prefix
  nameParts := ["check"]
  nameParts_ne_nil := by decide
  holes := [.sub L.termParser]
  holes_match_arity := rfl
  build := fun (e : L.Term) => some (.check e)
}

/-- The vernacular grammar. Atom fallback returns `none` so `parseTree`
producing an `.atom` (i.e. input not starting with a known command
keyword) is detectable as a parse error. -/
def vernacularGrammar (L : Language) : Grammar (Option (Command L)) := {
  levels := [[declOp L, evalOp L, checkOp L]]
  atomBuild := fun _ => none
  juxtBuild := none
}

/-- Split a token list at occurrences of a delimiter token. Like
`String.splitOn` but for token lists. -/
def splitTokensOn (delim : String) : List String → List (List String)
  | [] => [[]]
  | x :: rest =>
      if x == delim then
        [] :: splitTokensOn delim rest
      else
        match splitTokensOn delim rest with
        | head :: tail => (x :: head) :: tail
        | []           => [[x]]  -- unreachable: splitTokensOn always returns non-empty

/-- Parse a single chunk (one command's tokens, not including the
trailing `;`) into a `Command`. -/
def parseChunk (L : Language) (chunk : List String) : Option (Command L) :=
  match parseAll (vernacularGrammar L) chunk with
  | some (some cmd) => some cmd
  | _               => none

/-- Parse a token list into a list of commands. Splits on `;`, parses
each chunk, drops any empty trailing chunk (which corresponds to the
source ending in `;`). -/
def parseProgram (L : Language) (input : List String) : Option (List (Command L)) :=
  let chunks := (splitTokensOn ";" input).filter (· ≠ [])
  chunks.foldr
    (fun chunk acc =>
      match parseChunk L chunk, acc with
      | some c, some cs => some (c :: cs)
      | _,      _       => none)
    (some [])

/-- Tokenize a vernacular source by whitespace, dropping empty pieces.
Newlines are treated like spaces. -/
def tokenize (s : String) : List String :=
  -- replace newlines with spaces, then split on space
  let s' := s.replace "\n" " " |>.replace "\t" " "
  s'.splitOn " " |>.filter (· != "")

/-- Parse a vernacular source string into a list of commands. -/
def parse (L : Language) (s : String) : Option (List (Command L)) :=
  parseProgram L (tokenize s)

end LambdaLab.Language
