import LambdaLab.Pipeline.Compose
import LambdaLab.TypeSystem.FreeName
import LambdaLab.Parser.IsoParser.Adapters

/-!
# A plug-in language

The simplest possible plug-in: terms and types are each a single identifier. It exists to show
what a language author actually has to supply — and that the file parser, printer, and
round-trip proof all come back **for free**.
-/

namespace LambdaLab.Pipeline

open LambdaLab.TypeSystem (Context)

open LambdaLab.Parser.IsoParser

/-- Terms and types are both a bare identifier.

`sat isName`'s real indices are FIRST = `isName`, FOLLOW = ⊤ (a single token is self-delimiting,
so anything may follow). Adapt both to what the interface asks for: `enlargeFirst` widens FIRST
up to `anyTok` (sound: `firstOk` is a negative claim); `weakenFollow` narrows FOLLOW down to the
key token (sound: the round-trip is antitone in FOLLOW).

`reducible` for the reason `stlcLanguage` is: instance search has to see through the definition to
find the `PrincipalElaborate` instance at `Var trivialLanguage`. -/
@[reducible] def trivialLanguage : Language where
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

`Language.parsePipeline` (and its `String`-level API `parseFile`/`renderProgram`) come with the
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

`trivialLanguage` is a `Language`, so it parses. Making its *types and terms* satisfy
`TypeSystem.PrincipalElaborate` gets the whole front end including type checking — and note where the
work happens: everything below is an instance of a `TypeSystem` class, with no mention of a
parser, a token or a `Language`. The pipeline picks it up on its own.

Terms here are just names, and `Var` is the same `Name`, so a term is literally a variable
reference — which makes the only interesting judgement scope-and-agreement: a name already
declared must be used at the type it was declared with. A name not yet declared is unconstrained,
so a file can open with anything.

Small as it is, this exercises the part that only exists at the vernacular level: the context is
threaded through the declarations, so whether the *second* command checks depends on what the
first one declared.
-/

/-! ### The object language

Names carry no metavariables, so substitution is the identity and every law about it is `rfl`.
That is not a cheat — it is what a language with no inference looks like, and it is exactly the
degenerate case the interface has to admit if the general one is to mean anything. -/

/-! Terms and types are the same type here, so `Name` must have `HasVars` — and that makes the
*key-aware* `HashMap` substitution instance apply to `Context Name Name` and outrank the
context-specific one, which is deliberately `low`. The generic vernacular code was elaborated
where no `HasVars N` was in scope, so its goals carry the context instance; raising its priority
here makes the concrete lemmas below talk about the same `pSubst` those goals do. -/

attribute [local instance 2000] LambdaLab.TypeSystem.instHasSubstContext

instance : HasSubst Name Name where
  pSubst t _ := t
  isFree _ _ := False
  fresh _ := 0
  fresh_gt_free := by intro _ _ h; cases h

instance : GroundStable Name Name where pSubst_ground _ _ := rfl
instance : LawfulComp Name Name where pSubst_comp _ _ _ := rfl
instance : LawfulRestrict Name Name where pSubst_restrictBelow _ _ _ _ := rfl

/-- Nothing is ever free, so everything is ground — decidably. -/
instance : DecidablePred (HasVars.Ground : Name → Prop) := fun _ => isTrue (fun _ h => h)

/-- `t` may be used at `τ`: either it is unbound, or it was declared at `τ`. -/
def declaredAt (Γ : Context Name Name) (t τ : Name) : Bool :=
  match Γ.get? t with
  | none => true
  | some σ => σ == τ

/-- Substituting a context cannot change what it says, since substitution fixes every value.
Stated at `declaredAt` rather than as `pSubst Γ σ = Γ`, which `Std.HashMap` does not let anyone
prove — the same reason `LawfulTypeSystem.cong` exists. -/
theorem declaredAt_pSubst (Γ : Context Name Name) (σ : Subst Name) (t τ : Name) :
    declaredAt (HasSubst.pSubst Γ σ) t τ = declaredAt Γ t τ := by
  rw [declaredAt, declaredAt, Context.pSubst_get?]
  cases Γ.get? t <;> rfl

instance : TypeSystem.HasType Name Name Name where
  HasType Γ t τ := declaredAt Γ t τ = true

/-- Nothing reduces, so preservation is vacuous. -/
instance : TypeSystem.Step Name where Step _ _ := False

instance : TypeSystem.TypeSystem Name Name Name where
instance : TypeSystem.LawfulTypeSystem Name Name Name where
  Preservation _ hs := hs.elim
  cong h ht := by
    show declaredAt _ _ _ = true
    rw [declaredAt, ← h]
    exact ht

instance : TypeSystem.MVars Name Name Name where
  tmSubst := inferInstance
  tySubst := inferInstance

instance : TypeSystem.LawfulMVars Name Name Name where
  Stability := by
    intro Γ t τ σ ht
    show declaredAt (HasSubst.pSubst Γ σ) t τ = true
    rw [declaredAt_pSubst]
    exact ht
  tyGroundStable := inferInstance
  tmGroundStable := inferInstance
  tyLawfulComp := inferInstance
  tmLawfulComp := inferInstance
  tyLawfulRestrict := inferInstance
  tmLawfulRestrict := inferInstance

/-- The decision procedure. `declaredAt` is a `Bool`, and substitution changes nothing, so all
three obligations are immediate — the negative one is a genuine proof that *no* substitution helps
rather than a report of a failed search, and most-generality is free: substitution on `Name` is the
identity, so the empty answer is at least as general as anything with the empty witness.

Worth noting against STLC, where the same field costs a `sorry`. Most-generality is only hard when
there is inference to be most general *about*. -/
instance : TypeSystem.PrincipalElaborate Name Name Name where
  tyGroundDec := inferInstance
  tmGroundDec := inferInstance
  elaborate Γ t τ :=
    if h : declaredAt Γ t τ = true then
      .mgu ∅
        (by
          show declaredAt (HasSubst.pSubst Γ (∅ : Subst Name)) t τ = true
          rw [declaredAt_pSubst]; exact h)
        (fun _ _ => ⟨∅, fun _ => rfl⟩)
    else
      .impossible (fun σ hσ => h (by
        have h' : declaredAt (HasSubst.pSubst Γ σ) t τ = true := hσ
        rwa [declaredAt_pSubst] at h'))

/-! ### The pipeline, for free

`elaborateFile` is `Language.parsePipeline` composed with the elaboration stage — one `Abs` morphism
from characters to a *well-typed* program. -/

/-- Parse and elaborate, reporting the declared names of the elaborated program. -/
def checkNames (s : String) : Option (List String) :=
  (trivialLanguage.elaborateFile s).map fun p =>
    p.val.toList.map (fun c => c.name.val.val)

-- accepted: `y` is unbound at its use, then `x` is used at the `A` it was declared with
#eval checkNames "def x : A := y   def z : A := x"     -- some ["x", "z"]
-- rejected: `x` was declared at `A`, so using it at `B` does not check
#eval checkNames "def x : A := y   def z : B := x"     -- none
-- the parse still succeeds on the rejected file — it is elaboration that refuses
#eval parseNames "def x : A := y   def z : B := x"     -- some ["x", "z"]
-- and the whole front end still round-trips: elaborate, then render
#eval (trivialLanguage.elaborateFile "  def x : A := y   def z : A := x ").map
        trivialLanguage.renderElaborated

/-- The round trip over the *elaborating* pipeline: render an elaborated program and read it back,
and you land on exactly the program you started from — parsing and type checking together. Free,
as before. -/
example (p : trivialLanguage.Elaborated) :
    trivialLanguage.elaborateFile (trivialLanguage.renderElaborated p) = some p :=
  trivialLanguage.elaborateFile_renderElaborated p

end LambdaLab.Pipeline