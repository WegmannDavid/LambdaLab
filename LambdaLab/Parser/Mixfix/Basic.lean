/-!
# Mixfix parser: core data types

User-facing types for declaring mixfix operators. Following Danielsson &
Norell, *Parsing Mixfix Operators* (IFL 2008), generalised so that each
hole may be either a recursive sub-expression of the operator's result
type or an arbitrarily-typed value parsed by a user-supplied sub-parser.

This file only declares the data; the parser implementation, soundness
proof, and completeness proof live in subsequent files.
-/

namespace LambdaLab.Parser.Mixfix

/-! ## Fixity and arity -/

/-- Associativity for infix operators. -/
inductive Associativity where
  | left
  | right
  | nonAssoc
  deriving DecidableEq, Repr

/-- The fixity of a mixfix operator: where its argument holes sit
relative to its name-parts. -/
inductive Fixity where
  /-- All holes between/inside name-parts. E.g. `[_,_]`, `(_)`, `nil`. -/
  | closed
  /-- Holes between/inside, plus a trailing hole. E.g. `λ_._`, `if_then_else_`. -/
  | prefix
  /-- A leading hole, plus holes between/inside. E.g. `_!`. -/
  | postfix
  /-- A leading and a trailing hole. E.g. `_+_`. -/
  | infix (assoc : Associativity)
  deriving DecidableEq, Repr

/-- Arity (number of argument holes) of an operator, as a function of its
fixity and the number of name-parts. -/
def fixityArity : Fixity → Nat → Nat
  | .closed,    n => n - 1
  | .prefix,    n => n
  | .postfix,   n => n
  | .infix _,   n => n + 1

/-! ## Parsers and printers

A `Parser β` consumes some prefix of a token list and produces a `β`
together with the leftover tokens. Its round-trip companion is a
`Printer β` — given a `β`, return the tokens that the parser would
re-consume to produce that value.

The user-facing intent is that for any sub-parser-printer pair, the
round-trip law `∀ b ts, parser.run (printer b ++ ts) = some (b, ts)`
holds. The parser-correctness proofs in later files take this as a
precondition; we don't attempt to verify it here. -/

/-- A token-list printer: the round-trip companion of a `Parser β`. -/
abbrev Printer (β : Type) := β → List String

/-- A token-list parser producing values of type `β`, bundled with its
round-trip companion printer. -/
structure Parser (β : Type) where
  run : List String → Option (β × List String)
  printer : Printer β

/-! ## Hole specifications -/

/-- Specification of one argument hole in a mixfix operator. -/
inductive HoleSpec (α : Type) : Type 1 where
  /-- A recursive hole: parse another expression of the operator's
  result type `α`. -/
  | recurse : HoleSpec α
  /-- A sub-hole: parse a value of carrier type `β` using the bundled
  parser/printer pair. -/
  | sub {β : Type} : Parser β → HoleSpec α

/-- The type that a hole's evaluated child must have. For `recurse`
holes that's the operator's own result type `α`; for `sub` holes it's
the sub-parser's carrier type. -/
abbrev HoleSpec.evalType {α : Type} : HoleSpec α → Type
  | .recurse            => α
  | @HoleSpec.sub _ β _ => β

/-! ## Build-function types

The build function of an operator with holes `[h₁, h₂, ..., hₙ]` is
curried over the eval-types of those holes:
`evalType h₁ → evalType h₂ → ... → evalType hₙ → α`. -/

/-- The type of a build function for an operator with the given list of
holes. -/
abbrev buildType (α : Type) : List (HoleSpec α) → Type
  | []      => α
  | h :: hs => h.evalType → buildType α hs

/-! ## Operators and grammars -/

/-- A mixfix operator producing values of type `α`.

`nameParts` lists the literal tokens; `fixity` says where the holes sit
relative to those tokens; `holes` gives the parsing/typing spec for
each hole; and `holes_match_arity` certifies that the count of holes
agrees with the arity implied by fixity and `nameParts.length`.

Examples (with the `holes_match_arity` proof omitted; typically `rfl`
or `by decide`):

* Closed `[_,_]`: `nameParts = ["[", ",", "]"]`,
  `holes = [.recurse, .recurse]`, `build : α → α → α`.
* Prefix `λ_._`: `nameParts = ["λ", "."]`,
  `holes = [.sub stringParser, .recurse]`,
  `build : String → α → α`.
* Infix `_+_`: `nameParts = ["+"]`, `fixity = .infix .left`,
  `holes = [.recurse, .recurse]`, `build : α → α → α`.
-/
structure Operator (α : Type) : Type 1 where
  fixity : Fixity
  nameParts : List String
  nameParts_ne_nil : nameParts ≠ []
  holes : List (HoleSpec α)
  holes_match_arity : holes.length = fixityArity fixity nameParts.length
  build : buildType α holes

/-- The number of argument holes of an operator. -/
def Operator.arity {α} (op : Operator α) : Nat := op.holes.length

/-- A grammar over result type `α`: a list of precedence levels, plus
a fall-through interpretation for bare identifier-like tokens, plus an
optional juxtaposition combiner for application-style adjacency. -/
structure Grammar (α : Type) : Type 1 where
  /-- Precedence levels, ordered from tightest- to loosest-binding. -/
  levels : List (List (Operator α))
  /-- Interpretation of a bare token (e.g. a variable name in λ-calculus). -/
  atomBuild : String → α
  /-- Optional juxtaposition: when `some f`, after a head is parsed the
  parser tries to parse another head and combine via `f`. When `none`,
  juxtaposition is disabled. -/
  juxtBuild : Option (α → α → α) := none

end LambdaLab.Parser.Mixfix
