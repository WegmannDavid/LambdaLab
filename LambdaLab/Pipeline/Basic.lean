import LambdaLab.Parser.LossyParser.Basic
import LambdaLab.Parser.IsoParser.Token
import LambdaLab.Abstraction.Basic
import LambdaLab.NEList

namespace LambdaLab.Pipeline

open LambdaLab.Parser.IsoParser
open LambdaLab.Parser.LossyParser (LossyParser)
open LambdaLab (Iso)

/-! ## Lexemes

The parser's alphabet is *tokens*, but tokens are printed back as text, so the token type has
to be narrow enough that printing one and re-lexing it gives that same token back. What counts as
a token is each language's choice — its `Lexicon` (`IsoParser/Token.lean`): which characters
separate, which are tokens on their own, and how the latter are spaced when printed. A language
names its lexicon, and the tokenizer and the parser are both instantiated at it, so they agree by
construction rather than by coincidence. -/

variable {lex : Lexicon}

/-- Tokens available as names: everything the given list has not reserved. The `Atom`
instance for the resulting subtype lives in `TypeSystem/Named/FreeName.lean` (it needs a
fresh-name generator); the definitions live here so that a language's name type can be stated in
terms of them. -/
def isFree (reserved : List (Token lex)) (t : Token lex) : Bool := decide (t ∉ reserved)

/-- The atoms determined by a reserved list. -/
abbrev FreeName (reserved : List (Token lex)) : Type :=
  { t : Token lex // isFree reserved t = true }

/-! ## A language: declaration forms

A file is a non-empty run of declarations, and a declaration starts with a keyword. That keyword
is the only thing the framework fixes about it: it says which **form** the declaration has, and
everything after it is the form's own business — `def x : T := e`, `type α : κ := τ`,
`float x := 4` are three forms, and the framework knows none of their insides.

What it does need is to know where a declaration *ends*. The next declaration starts with a
keyword, so every form's body must stop in front of any declaration keyword — not consume it, and
not be confused by it. That is the **termination seam**, and it is the one obligation a body
carries: its FOLLOW must admit every keyword (`body`'s type says so).

**Keywords are ordinary tokens.** `Token` does not exclude them. A body may well use one
internally, and what stops it from swallowing the next declaration's keyword is its FOLLOW set —
the same mechanism by which a digit run stops at whitespace. For a mixfix body the seam is
`follow G e t = true` for each keyword `t`, which `decide` settles, and it fails exactly when the
keyword could start or continue an expression (`Mixfix/Complete.lean`'s `follow`).

**Why FIRST is unconstrained.** A body always follows its form's keyword, whose FOLLOW is `⊤`, so
the seam into a body is `FIRST ⊆ ⊤` — true for any FIRST whatsoever. And `firstOk` is a purely
negative claim ("outside FIRST, I fail"), so widening FIRST only ever weakens it. So bodies have
FIRST `anyTok`.

**The plug-in boundary.** A body states its *real* FIRST and FOLLOW and then adapts: widen FIRST
up to `anyTok` (`enlargeFirst`, sound because `firstOk` is negative) and narrow FOLLOW down to the
keywords (`weakenFollow`, sound because the round trip is antitone in FOLLOW, `HeadIn.mono`). Both
are sound in exactly one direction, and that direction is the one needed. -/

/-- FIRST is **unconstrained** for a body, so the interface allows everything. -/
abbrev anyTok : Token lex → Prop := fun _ => True

/-- A **pluggable language**: its declaration forms, each a keyword and a parser for what follows
it. The file parser, its round trip, and the `Abs` morphism are *derived* (`Stages/Parse.lean`).

Nothing here mentions types, terms or a type system. What a declaration *means* is a separate
concern, supplied as walks over `Decl` (`Semantics/Walk.lean`); a language with none still parses
and pretty-prints. `Pipeline/Def.lean` builds the one-form language `def x : T := e` from a term
and a type parser, which is how every language before this structure is expressed in it. -/
structure Language where
  /-- What a token is: separators, self-delimiting characters, and their printed spacing. -/
  lex : Lexicon
  /-- The declaration forms. -/
  Form : Type
  /-- Every form, listed — so that the keywords form a finite list. -/
  forms : List Form
  forms_complete : ∀ f, f ∈ forms
  /-- The keyword that starts a declaration of form `f`. -/
  head : Form → Token lex
  /-- **One keyword, one form.** This is what lets the file parser choose a form by reading one
  token. -/
  head_injective : ∀ f g, head f = head g → f = g
  /-- What follows the keyword: the value a declaration of form `f` carries. -/
  Body : Form → Type
  /-- The surface spellings a body may have beyond its canonical one — redundant parentheses,
  sugar. `fun _ _ => Unit` for a canonical-form-only body. -/
  BodyAnn : (f : Form) → Body f → Type
  /-- The parser for what follows the keyword. **Lossy** — it parses to the value and prints any
  annotated spelling, `default` being the canonical one. Its FOLLOW admits every keyword: the
  termination seam. -/
  body : (f : Form) →
    LossyParser (Token lex) anyTok (fun t => t ∈ forms.map head) (Body f) (BodyAnn f)
  /-- The type a declaration is, for whatever walks over it. A language may take
  `Σ f, Body f` itself; one with its own inductive gives it here and relates the two by `decl`. -/
  Decl : Type
  /-- A declaration *is* a form and a body, up to this bijection. -/
  decl : Iso Decl (Σ f, Body f)

namespace Language

variable (L : Language)

/-- The keywords that start a declaration — what every body must stop in front of. -/
def heads : List (Token L.lex) := L.forms.map L.head

theorem head_mem_heads (f : L.Form) : L.head f ∈ L.heads :=
  List.mem_map.mpr ⟨f, L.forms_complete f, rfl⟩

/-- The form a keyword starts, if it starts one. -/
def formOf (t : Token L.lex) : Option L.Form := L.forms.find? (fun f => L.head f == t)

theorem formOf_head (f : L.Form) : L.formOf (L.head f) = some f := by
  unfold formOf
  cases h : L.forms.find? (fun g => L.head g == L.head f) with
  | none =>
      rw [List.find?_eq_none] at h
      exact absurd (beq_self_eq_true (L.head f)) (h f (L.forms_complete f))
  | some g =>
      have hg := List.find?_some h
      rw [beq_iff_eq] at hg
      rw [L.head_injective g f hg]

/-- The surface spellings of a declaration: those of its body. -/
def DeclAnn (d : L.Decl) : Type := L.BodyAnn (L.decl.toFun d).1 (L.decl.toFun d).2

end Language

/-- A **program**: a non-empty run of declarations.

Why not a `List`: a one-or-more parser never *parses* an empty list, so an empty program has no
printed form to parse back — it would falsify the file parser's round-trip law. -/
abbrev Program (L : Language) : Type := NEList L.Decl

end LambdaLab.Pipeline
