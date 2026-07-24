import LambdaLab.Parser.LossyParser.Basic
import LambdaLab.Parser.IsoParser.Token

namespace LambdaLab.Language1

open LambdaLab.Parser.IsoParser
open LambdaLab.Parser.LossyParser (LossyParser)

/-! ## Lexemes

The parser's alphabet is *tokens*, but tokens are printed back as text, so the token type has
to be narrow enough that printing one and re-lexing it gives that same token back. Two ways it
could fail, and they are the same failure we keep meeting — a source wider than the printable
set:

* an **empty** token prints nothing, so it cannot be read back;
* a token **containing a separator** prints as text that re-lexes into *two* tokens.

So neither is representable. Which characters separate tokens is a parameter: `isSep`. -/

/-- Which characters separate tokens. A token is a maximal run of non-separator characters. -/
def isSep (c : Char) : Bool := c.isWhitespace

/-- The parser's alphabet — **derived**, by instantiating `IsoParser.Token` at our separator.
It is not a type of our own: the alphabet is fixed above the vernacular, in
`IsoParser/Token.lean`, which knows nothing about this vernacular, so any tokenizer and this
parser must agree by construction rather than by coincidence. By construction, printing a
`Token` and re-lexing recovers it.

`IsoParser.isToken` is a *decidable* `Bool`, which is why the keyword literals below can be
discharged by `decide`. -/
abbrev Token := _root_.LambdaLab.Parser.IsoParser.Token isSep

/-! ## The vernacular -/

/-- The reserved lexemes of the file format (`def NAME : TYPE := BODY`). A *language*'s own
keywords (`\lambda`, `->`, …) are a separate, per-language concern living inside `pTm`/`pTy`,
invisible here. -/
def kwDef    : Token := ⟨"def", by decide⟩
def kwColon  : Token := ⟨":",   by decide⟩
def kwAssign : Token := ⟨":=",  by decide⟩

def isVernacularKeyword (t : Token) : Bool :=
  t.val == "def" || t.val == ":" || t.val == ":="

/-- A name is any non-keyword lexeme. The subtype is load-bearing: a `Command` holding the name
`def` would print a lexeme the parser reads back as a keyword. -/
def isName (t : Token) : Bool := !isVernacularKeyword t

abbrev Name := { t : Token // isName t = true }

/-! ## The plug-in interface

**Design note.** `Token` deliberately does *not* exclude the vernacular keywords. Making it do
so is appealing — `pTm`/`pTy` then literally could not consume `def` — but it does not survive
contact: `Language.parser` *must* consume those keywords, so it would need a different alphabet
and a lift across alphabets. Worse, "a type may be followed by `:=`" would not even be
*expressible*, since `:=` would not inhabit `pTy`'s FOLLOW domain.

So keywords are ordinary tokens, and what stops a term parser from swallowing them is its
**FOLLOW set** — the same mechanism by which a digit run stops at whitespace. The guarantee
becomes the two facts a language declares below. -/

/-- The FOLLOW a type must accept: exactly `:=`. -/
abbrev followAssign : Token → Prop := fun t => t = kwAssign

/-- The FOLLOW a term must accept: exactly `def` (the next command). -/
abbrev followDef : Token → Prop := fun t => t = kwDef

/-- FIRST is **unconstrained** by the vernacular, so the interface simply allows everything. -/
abbrev anyTok : Token → Prop := fun _ => True

/-- A **pluggable language**: a term parser and a type parser. That is the whole interface.
Everything above it — commands, programs, and the file round-trip — is *derived*.

**Why there are no FIRST fields.** FIRST never constrains anything here: `pTy` and `pTm` are
each preceded by a fixed keyword (`:`, `:=`) whose FOLLOW is `⊤`, so their seams are
`FIRST ⊆ ⊤` — true for any FIRST whatsoever. And `firstOk` is a purely *negative* claim
("outside FIRST, I fail"), so widening FIRST only ever *weakens* it. So the interface asks for
nothing: `anyTok`.

**Why FOLLOW is pinned instead.** FOLLOW is what carries the real guarantee. `pTm`'s law at
`followDef` says: *print a term, append anything starting with `def`, re-parse → you get the
term back with the `def` untouched.* That is a **proof** that a term parser stops at a command
boundary — and it is why the two seam obligations vanished; they are now definitionally true.

**The plug-in boundary.** A language states its parser's *real* FIRST and FOLLOW and then adapts:
widen FIRST up to `anyTok` (sound because `firstOk` is negative — a larger FIRST promises less) and
narrow FOLLOW down to the key token (sound because the round-trip is antitone in FOLLOW, `HeadIn.mono`).
Both are sound in exactly one direction, and that direction is the one you need. -/
structure Language where
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
  /-- The term parser: must stop at a command boundary (`def`). Lossy — this is what lets a
  language *truncate*: accept `((((a))))`, remember only `a`, and still round-trip. -/
  pTm : LossyParser Token anyTok followDef Tm AnnTm

end LambdaLab.Language1
