import LambdaLab.Pipeline.Pipeline
import LambdaLab.Pipeline.ElabStage
import LambdaLab.TypedLanguage.FreeName
import LambdaLab.Parser.IsoParser.Adapters

/-!
# A plug-in language

The simplest possible plug-in: terms and types are each a single identifier. It exists to show
what a language author actually has to supply — and that the file parser, printer, and
round-trip proof all come back **for free**.
-/

namespace LambdaLab.Pipeline

open LambdaLab.TypedLanguage (Context)

open LambdaLab.Parser.IsoParser

/-- Terms and types are both a bare identifier.

`sat isName`'s real indices are FIRST = `isName`, FOLLOW = ⊤ (a single token is self-delimiting,
so anything may follow). Adapt both to what the interface asks for: `enlargeFirst` widens FIRST
up to `anyTok` (sound: `firstOk` is a negative claim); `weakenFollow` narrows FOLLOW down to the
key token (sound: the round-trip is antitone in FOLLOW). -/
def trivialLanguage : Language where
  Tm := Name
  Ty := Name
  AnnTy := fun _ => Unit
  AnnTm := fun _ => Unit
  -- Variables are any non-keyword lexeme — the same `Name` the terms themselves are.
  isVarName := isName
  varAlphabet := inferInstance
  keywords_excluded := by decide

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

/-! ## Giving it a semantics

`trivialLanguage` is a `Language`, so it parses. Making it an `ElaboratableLanguage` gets the
whole front end *including* type checking, again for free.

Terms here are just names, and `Var` is the same `Name`, so a term is literally a variable
reference — which makes the only interesting judgement scope-and-agreement: a name already
declared must be used at the type it was declared with. A name not yet declared is unconstrained,
so a file can open with anything.

Small as it is, this exercises the part that only exists at the vernacular level: the context is
threaded through the declarations, so what the *second* command means depends on what the first
one elaborated to.
-/

/-- `t` may be used at `τ`: either it is unbound, or it was declared at `τ`. -/
def declaredAt (Γ : Context Name Name) (t τ : Name) : Bool :=
  match Γ.get? t with
  | none => true
  | some σ => σ == τ

/-- The trivial language with a semantics. Elaboration is the identity — nothing is inferred —
so all the content is in `declaredAt`. -/
def trivialElaboratable : ElaboratableLanguage where
  toLanguage := trivialLanguage
  Elaborates Γ t t' τ τ' := t' = t ∧ τ' = τ ∧ declaredAt Γ t τ = true
  elaborates_unique h₁ h₂ := by
    obtain ⟨rfl, rfl, -⟩ := h₁; obtain ⟨rfl, rfl, -⟩ := h₂; exact ⟨rfl, rfl⟩
  elaborate Γ t τ :=
    if h : declaredAt Γ t τ = true then some ⟨(t, τ), rfl, rfl, h⟩ else none
  elaborate_complete h := by
    obtain ⟨rfl, rfl, hok⟩ := h; simp [hok]
  quote t' τ' := (t', τ')
  quote_elaborates h := by
    obtain ⟨t, τ, rfl, rfl, hok⟩ := h; exact ⟨rfl, rfl, hok⟩

/-- Parse and elaborate, reporting the declared names of the *elaborated* program. -/
def checkNames (s : String) : Option (List String) :=
  (trivialElaboratable.elaborateFile s).map fun p =>
    p.val.toList.map (fun c => c.name.val.val)

-- accepted: `y` is unbound at its use, then `x` is used at the `A` it was declared with
#eval checkNames "def x : A := y   def z : A := x"     -- some ["x", "z"]
-- rejected: `x` was declared at `A`, so using it at `B` does not elaborate
#eval checkNames "def x : A := y   def z : B := x"     -- none
-- the parse still succeeds on the rejected file — it is elaboration that refuses
#eval parseNames "def x : A := y   def z : B := x"     -- some ["x", "z"]
-- and the whole front end still round-trips: elaborate, then render
#eval (trivialElaboratable.elaborateFile "  def x : A := y   def z : A := x ").map
        trivialElaboratable.renderElaborated

/-- The round trip, now over the *elaborating* pipeline: any source that means `p` re-parses and
re-elaborates to exactly `p`. Free, as before. -/
example (p : ElaborableProgram trivialElaboratable)
    (ann : Σ a : { q // Program.Elaborates trivialElaboratable q p.val },
      Σ b : Program.Ann trivialElaboratable.toLanguage a.val,
        Abstraction.Gaps isSep (trivialElaboratable.parser.print b)) :
    trivialElaboratable.pipeline.abstract (trivialElaboratable.pipeline.realize ann) = some p :=
  trivialElaboratable.pipeline.abstract_realize p ann

end LambdaLab.Pipeline
