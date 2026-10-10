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

/-! ## The keywords -/

def kwDef    : Token := ⟨"def", by decide⟩
def kwColon  : Token := ⟨":",   by decide⟩
def kwAssign : Token := ⟨":=",  by decide⟩

/-- The form's own keywords, as a list. -/
def vernacularReserved : List Token := [kwDef, kwColon, kwAssign]

/-- Any lexeme that is not one of the form's keywords. -/
abbrev isName : Token → Bool := isFree vernacularReserved

abbrev Name := FreeName vernacularReserved

/-- The FOLLOW a type must accept: exactly `:=`. -/
abbrev followAssign : Token → Prop := fun t => t = kwAssign

/-- The FOLLOW a term must accept: exactly `def`, which starts the next declaration. -/
abbrev followDef : Token → Prop := fun t => t = kwDef

/-! ## The interface -/

/-- **A `def`-language**: a term parser and a type parser, and which tokens name a variable.

Both parsers have FIRST `anyTok`, for the reason a body does (`Pipeline/Basic.lean`): each follows
a keyword whose FOLLOW is `⊤`. Their FOLLOWs are pinned. `pTy` is followed by `:=`, and `pTm` ends
the declaration, so it is followed by the next one's keyword — its FOLLOW at `def` is the
termination seam. -/
structure DefLanguage where
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
  pTy : LossyParser Token anyTok followAssign Ty AnnTy
  /-- The term parser: must stop at the next declaration's `def`. Lossy — this is what lets a
  language *truncate*: accept `((((a))))`, remember only `a`, and still round-trip. -/
  pTm : LossyParser Token anyTok followDef Tm AnnTm
  /-- Which tokens may name a variable — and hence a declaration. -/
  isVarName : Token → Bool
  /-- Names must carry an `Atom` instance: decidable, hashable, and inexhaustible (capture-avoiding
  substitution has to invent names). A language that simply excludes a finite reserved list gets
  this from `FreeName`'s instance — `isVarName := isFree myReserved` and `inferInstance`. One
  with a genuine lexical class ("identifiers start with a letter") supplies its own, which is
  why this is a field rather than being derived from a reserved list. -/
  varAtom : Atom { t : Token // isVarName t = true }

/-- A language's variable names — and its declaration names, which are the same thing. -/
abbrev Var (D : DefLanguage) : Type := { t : Token // D.isVarName t = true }

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
    IsoParser Token (fun t => D.isVarName t = true) (fun _ => True) (Var D) (Var D) :=
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
    IsoParser Token anyTok (· ∈ [kwDef]) (Σ c : Command D, Command.Ann D c) (Command D) :=
  IsoParser.enlargeFirst (fun _ h => absurd trivial h) <| gdo
    let n ← comap (fun s => s.1.name) D.pName
    let _c ← tok kwColon
    let ty ← comap (fun s => ⟨s.1.ty, s.2.1⟩) D.pTy.toIsoParser
    let _a ← tok kwAssign
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
    LossyParser Token anyTok (· ∈ [kwDef]) (Command D) (Command.Ann D) :=
  D.bodyIso.toLossyParserSigma (fun {_} => (D.pTy.default, D.pTm.default)) D.bodyIso_echo

/-! ## The language -/

/-- **The one-form language**: keyword `def`, body `NAME : TYPE := BODY`, and the declaration
type `Command` itself — related to `Σ f, Body f` by the trivial bijection, there being one form.

`reducible` for the reason the languages built from it are: instance search has to see through it
to the `Command` the type-system instances are stated at. -/
@[reducible] def DefLanguage.toLanguage (D : DefLanguage) : Language where
  Form := Unit
  forms := [()]
  forms_complete _ := List.mem_singleton.mpr rfl
  head _ := kwDef
  head_injective _ _ _ := rfl
  Body _ := Command D
  BodyAnn _ := Command.Ann D
  body _ := D.body
  Decl := Command D
  decl := ⟨fun c => ⟨(), c⟩, fun s => s.2, fun _ => rfl, fun _ => rfl⟩

end LambdaLab.Pipeline
