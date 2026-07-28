import LambdaLab.Language1.Pipeline
import LambdaLab.Language1.FreeName
import LambdaLab.Parser.IsoParser.Adapters

/-!
# A plug-in language

The simplest possible plug-in: terms and types are each a single identifier. It exists to show
what a language author actually has to supply — and that the file parser, printer, and
round-trip proof all come back **for free**.
-/

namespace LambdaLab.Language1

open LambdaLab.Parser.IsoParser

/-- Terms and types are both a bare identifier.

`sat isName`'s real indices are FIRST = `isName`, FOLLOW = ⊤ (a single token is self-delimiting,
so anything may follow). Adapt both to what the interface asks for: `enlargeFirst` widens FIRST
up to `anyTok` (sound: `firstOk` is a negative claim); `weakenFollow` narrows FOLLOW down to the
key token (sound: the round-trip is antitone in FOLLOW). -/
-- Trivial substitution structures, as *instances*, so `elaborate`'s type — which mentions the
-- fields being defined — can still resolve them.
local instance : HasSubst Name Name := trivialHasSubst _ _
local instance : HasSubst (Context Name Name) Name := trivialHasSubst _ _

def trivialLanguage : Language where
  Tm := Name
  Ty := Name
  AnnTy := fun _ => Unit
  AnnTm := fun _ => Unit
  -- Variables are any non-keyword lexeme — the same `Name` the terms themselves are.
  isVarName := isName
  varAlphabet := inferInstance
  keywords_excluded := by decide

  -- No typing discipline: every term has every type. Enough to satisfy the interface, and it
  -- documents honestly that this language has no semantics.
  tyHasSubst := inferInstance
  tmHasSubst := inferInstance
  ctxHasSubst := inferInstance
  freshTy := fun _ => ⟨⟨"A", by decide⟩, by decide⟩
  tyPSubstEmpty := fun _ => rfl
  HasType := fun _ _ _ => True
  -- `pSubst` is definitionally the identity here, so `∅` is most general by `rfl`.
  elaborate := fun _ _ _ => .ok ⟨∅, trivial, fun _ _ => ⟨∅, fun _ => rfl⟩⟩
  eval := fun {_ e _} _ => e

  pTy := (((sat isName).weakenFollow (fun _ _ => trivial)).enlargeFirst
    (fun _ hf => absurd trivial hf)).toLossyParserUnit (fun _ => rfl)
  pTm := (((sat isName).weakenFollow (fun _ _ => trivial)).enlargeFirst
    (fun _ hf => absurd trivial hf)).toLossyParserUnit (fun _ => rfl)

/-- `def x : A := e` — one command. -/
def prog : Program trivialLanguage :=
  (Command.decl ⟨⟨"x", by decide⟩, by decide⟩ ⟨⟨"A", by decide⟩, by decide⟩ ⟨⟨"e", by decide⟩, by decide⟩, [])

/-- Two commands. -/
def prog2 : Program trivialLanguage :=
  (Command.decl ⟨⟨"x", by decide⟩, by decide⟩ ⟨⟨"A", by decide⟩, by decide⟩ ⟨⟨"e", by decide⟩, by decide⟩,
   [Command.decl ⟨⟨"y", by decide⟩, by decide⟩ ⟨⟨"B", by decide⟩, by decide⟩ ⟨⟨"f", by decide⟩, by decide⟩])

/-- The canonical spelling of a program — `print` at the `default` annotation. -/
def canonPrint (p : Program trivialLanguage) : List Token :=
  trivialLanguage.parser.print (trivialLanguage.parser.default (v := p))

-- printing:  ["def", "x", ":", "A", ":=", "e"]
#eval (canonPrint prog).map (·.val)
-- and back — the leftover is `[]`, i.e. the whole file was consumed:
#eval (trivialLanguage.parser.run (canonPrint prog)).map (·.2.map (·.val))
-- the parsed names, recovered:
#eval (trivialLanguage.parser.run (canonPrint prog)).map
        (fun r => r.1.toList.map (fun c => c.name.val.val))

-- two commands round-trip too — the `many1` seam ("no further `def`") holds at end-of-input
#eval (canonPrint prog2).map (·.val)
#eval (trivialLanguage.parser.run (canonPrint prog2)).isSome

/-- The round-trip, instantiated: **free**, inherited from the framework — now for *any*
spelling `ann`, not only the canonical one. -/
example (p : Program trivialLanguage) (ann : Program.Ann trivialLanguage p) :
    trivialLanguage.parser.run (trivialLanguage.parser.print ann) = some (p, []) :=
  trivialLanguage.parser_roundtrip p ann

/-! ## The full pipeline: `List Char ⇝ Program`

`Language.pipeline` (and its `String`-level API `parseFile`/`renderProgram`) come with the
framework — one `Abs` morphism from raw characters to parsed commands. Since `trivialLanguage`
is sorry-free, the whole pipeline is too. -/

/-- Parse a file, print the declared names. -/
def parseNames (s : String) : Option (List String) :=
  (trivialLanguage.parseFile s).map fun p => p.toList.map (fun c => c.name.val.val)

/-- Parse a file, re-render it canonically (single spaces, canonical spellings). -/
def reprint (s : String) : Option String :=
  (trivialLanguage.parseFile s).map trivialLanguage.renderProgram

#eval parseNames "def x : A := e   def y : B := f"   -- some ["x", "y"]
#eval reprint    "def x : A := e   def y : B := f"   -- some "def x : A := e def y : B := f"
#eval reprint    "  def   x :   A := e  "            -- some "def x : A := e"   (normalized)
#eval parseNames "def x : A e"                       -- none  (missing `:=`)
#eval parseNames ""                                  -- none  (a program is non-empty)

end LambdaLab.Language1
