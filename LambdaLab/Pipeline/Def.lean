import LambdaLab.Pipeline.Basic
import LambdaLab.Parser.IsoParser.Notation
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Nominal.Atom
import LambdaLab.TypeSystem.Named.Vernacular.Basic

/-!
# `def x : T := e` — the one-form language

The vernacular every language here used to be locked into: a file is a run of
`def NAME : TYPE := BODY`. It is now one configuration of `Language` among many — a single form,
keyword `def`, whose body is a name, a type and a term — and `DefLanguage` is the interface for
writing such a language: supply a term parser and a type parser, get the `Language`.

The declaration type is `TypeSystem.Named.Vernacular.Command`, so the semantics over it
(`Vernacular/Typing.lean`, `Elaborate.lean`, `Evaluate.lean`) is the one this form has always had.

## Names

A declaration's name is a *term variable* of the language (`Var`), not a vernacular notion of its
own: `def f : T := e` puts `f` in scope as an ordinary variable, with no injection between two
kinds of name. That is a fact about this form, which is why the name alphabet and its `Atom`
instance are fields here and not of `Language`.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Parser.IsoParser
open LambdaLab.Parser.LossyParser (LossyParser)
open LambdaLab.Nominal (Atom)
open LambdaLab (Iso)

/-! ## The keywords

`def`, `:` and `:=` are tokens of whatever lexicon the language chose — provided it admits them:
`:=` is two characters, so a lexicon that made `:` or `=` self-delimiting would split it in two.
`DefKeywords lex` is that proviso. For a concrete lexicon `decide` settles it, so it is an
auto-parameter everywhere it is asked for. -/

/-- The lexicon admits the form's keywords as tokens. -/
structure DefKeywords (lex : Lexicon) : Prop where
  def_tok : isToken lex "def" = true := by decide
  colon_tok : isToken lex ":" = true := by decide
  assign_tok : isToken lex ":=" = true := by decide

section Keywords

variable (lex : Lexicon) (k : DefKeywords lex := by exact {})

def kwDef    : Token lex := ⟨"def", k.def_tok⟩
def kwColon  : Token lex := ⟨":",   k.colon_tok⟩
def kwAssign : Token lex := ⟨":=",  k.assign_tok⟩

/-- The form's own keywords, as a list. -/
def vernacularReserved : List (Token lex) := [kwDef lex k, kwColon lex k, kwAssign lex k]

/-- Any lexeme that is not one of the form's keywords. -/
abbrev isName : Token lex → Bool := isFree (vernacularReserved lex k)

abbrev Name := FreeName (vernacularReserved lex k)

/-- The FOLLOW a type must accept: exactly `:=`. -/
abbrev followAssign : Token lex → Prop := fun t => t = kwAssign lex k

/-- The FOLLOW a term must accept: exactly `def`, which starts the next declaration. -/
abbrev followDef : Token lex → Prop := fun t => t = kwDef lex k

end Keywords

/-! ## The interface -/

/-- **A `def`-language**: a term parser and a type parser, and which tokens name a variable.

Both parsers have FIRST `anyTok`, for the reason a body does (`Pipeline/Basic.lean`): each follows
a keyword whose FOLLOW is `⊤`. Their FOLLOWs are pinned. `pTy` is followed by `:=`, and `pTm` ends
the declaration, so it is followed by the next one's keyword — its FOLLOW at `def` is the
termination seam. -/
structure DefLanguage where
  /-- What a token is (`IsoParser/Token.lean`). -/
  lex : Lexicon
  /-- The lexicon admits `def`, `:` and `:=`; by `decide`. -/
  kw : DefKeywords lex := by exact {}
  Tm : Type
  Ty : Type
  /-- Surface spellings a type value may have beyond the canonical one — redundant parens,
  sugar, elided (`_`) annotations. `fun _ => Unit` for a canonical-form-only language. -/
  AnnTy : Ty → Type
  /-- Surface spellings a term value may have. -/
  AnnTm : Tm → Type
  /-- The type parser: must stop at `:=` rather than swallowing the assignment. **Lossy**:
  parses to the value, prints any annotated spelling; `pTy.default` is the canonical printer.
  A lossless (`IsoParser`) parser plugs in via `toLossyParserUnit`. -/
  pTy : LossyParser (Token lex) anyTok (followAssign lex kw) Ty AnnTy
  /-- The term parser: must stop at the next declaration's `def`. Lossy — this is what lets a
  language *truncate*: accept `((((a))))`, remember only `a`, and still round-trip. -/
  pTm : LossyParser (Token lex) anyTok (followDef lex kw) Tm AnnTm
  /-- Which tokens may name a variable — and hence a declaration. -/
  isVarName : Token lex → Bool
  /-- Names must carry an `Atom` instance: decidable, hashable, and inexhaustible (capture-avoiding
  substitution has to invent names). A language that simply excludes a finite reserved list gets
  this from `FreeName`'s instance — `isVarName := isFree myReserved` and `inferInstance`. One
  with a genuine lexical class ("identifiers start with a letter") supplies its own, which is
  why this is a field rather than being derived from a reserved list. -/
  varAtom : Atom { t : Token lex // isVarName t = true }

/-- A language's variable names — and its declaration names, which are the same thing. -/
abbrev Var (D : DefLanguage) : Type := { t : Token D.lex // D.isVarName t = true }

instance (D : DefLanguage) : Atom (Var D) := D.varAtom

/-- A single declaration of `D`: `def NAME : TYPE := BODY`, named by `D`'s own variables. -/
abbrev Command (D : DefLanguage) : Type := TypeSystem.Named.Vernacular.Command (Var D) D.Tm D.Ty

/-- The constructor at the instantiated arity. `match_pattern` so it reads as a constructor on
both sides of an equation, not only in construction. -/
@[match_pattern] abbrev Command.decl {D : DefLanguage} (n : Var D) (τ : D.Ty) (t : D.Tm) :
    Command D := TypeSystem.Named.Vernacular.Command.decl n τ t

/-! ## The body: `NAME : TYPE := BODY` -/

/-- An identifier: one token the language admits as a variable name. Aligned: source and value
are `Var D`, so a name the language would reject is unrepresentable. -/
def DefLanguage.pName (D : DefLanguage) :
    IsoParser (Token D.lex) (fun t => D.isVarName t = true) (fun _ => True) (Var D) (Var D) :=
  sat D.isVarName

/-- Everything a declaration's surface may spell beyond the declaration itself: the annotations of
its type and its term. (The name and the keywords have exactly one spelling.) -/
def Command.Ann (D : DefLanguage) : Command D → Type :=
  fun c => D.AnnTy c.ty × D.AnnTm c.tm

/-- What follows `def`, at the `IsoParser` level: the **source is the annotated declaration**.
The type and term parsers cross in via `toIsoParser` and `comap` the slice of the source they print
from. Two adapters at the ends: FIRST is widened to `anyTok` (a name is what really starts it), and
the term's FOLLOW is restated as the one-keyword list `Language.body` asks for. -/
def DefLanguage.bodyIso (D : DefLanguage) :
    IsoParser (Token D.lex) anyTok (· ∈ [kwDef D.lex D.kw]) (Σ c : Command D, Command.Ann D c)
      (Command D) :=
  IsoParser.enlargeFirst (fun _ h => absurd trivial h) <| gdo
    let n ← comap (fun s => s.1.name) D.pName
    let _c ← tok (kwColon D.lex D.kw)
    let ty ← comap (fun s => ⟨s.1.ty, s.2.1⟩) D.pTy.toIsoParser
    let _a ← tok (kwAssign D.lex D.kw)
    let tm ← comap (fun s => ⟨s.1.tm, s.2.2⟩)
      (D.pTm.toIsoParser.weakenFollow (fun _ h => List.mem_singleton.mp h))
    return Command.decl n ty tm

/-- The body prints the declaration it is indexed by — each component's printed value is its
index, so the composite's is the reassembled declaration (eta). -/
theorem DefLanguage.bodyIso_echo (D : DefLanguage) :
    ∀ s : Σ c : Command D, Command.Ann D c, (D.bodyIso.print s).1 = s.1
  | ⟨.decl _ _ _, _⟩ => rfl

/-- **The body, lossy**: value `Command D`, annotation `Command.Ann`. Canonical print uses the type
and term parsers' canonical annotations. -/
def DefLanguage.body (D : DefLanguage) :
    LossyParser (Token D.lex) anyTok (· ∈ [kwDef D.lex D.kw]) (Command D) (Command.Ann D) :=
  D.bodyIso.toLossyParserSigma (fun {_} => (D.pTy.default, D.pTm.default)) D.bodyIso_echo

/-! ## The language -/

/-- **The one-form language**: keyword `def`, body `NAME : TYPE := BODY`, and the declaration
type `Command` itself — related to `Σ f, Body f` by the trivial bijection, there being one form.

`reducible` for the reason the languages built from it are: instance search has to see through it
to the `Command` the type-system instances are stated at. -/
@[reducible] def DefLanguage.toLanguage (D : DefLanguage) : Language where
  lex := D.lex
  Form := Unit
  forms := [()]
  forms_complete _ := List.mem_singleton.mpr rfl
  head _ := kwDef D.lex D.kw
  head_injective _ _ _ := rfl
  Body _ := Command D
  BodyAnn _ := Command.Ann D
  body _ := D.body
  Decl := Command D
  decl := ⟨fun c => ⟨(), c⟩, fun s => s.2, fun _ => rfl, fun _ => rfl⟩

end LambdaLab.Pipeline
