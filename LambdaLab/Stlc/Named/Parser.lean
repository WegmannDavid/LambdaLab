import LambdaLab.Stlc.Named.Basic
import LambdaLab.Parser.Mixfix.Parser

/-!
# A parser for named STLC

Specializes the mixfix parser framework to produce
`LambdaLab.Stlc.Named.Term` values.

## Surface syntax

Types:
* `ι`        — base type.
* `τ → τ`    — function type (right-associative).
* `( τ )`    — grouping.

(Surface syntax `_` for "infer me" was removed alongside `Ty.inf`; it
will return once the parser threads a fresh-mvar counter through
`atomBuild`.)

Terms:
* identifier — variable.
* `λ x : τ . e` — lambda binder.
* `e₁ e₂`    — application (juxtaposition, left-associative).
* `( e )`    — grouping.

Tokens are whitespace-separated. The user is responsible for tokenizing
multi-character literals such as `→` to single tokens.
-/

namespace LambdaLab.Stlc.Named.Parser

open LambdaLab.Parser
open LambdaLab.Parser.Mixfix
open LambdaLab.Stlc.Named

/-! ## Type grammar -/

/-- Closed: `( τ )`. -/
def typeParens : Operator Unit Ty := {
  fixity := .closed
  nameParts := ["(", ")"]
  nameParts_ne_nil := by decide
  holes := [.recurse]
  holes_match_arity := by decide
  build := fun (a : Ty) => a
}

/-- Infix right-associative: `τ → τ`. -/
def arrowOp : Operator Unit Ty := {
  fixity := .infix .right
  nameParts := ["→"]
  nameParts_ne_nil := by decide
  holes := [.recurse, .recurse]
  holes_match_arity := by decide
  build := fun (a b : Ty) => .arrow a b
}

/-- Type grammar. The atom `_` is the surface "infer me" hole; every
other atom (including `ι`) is treated as `Ty.base` — a parser limitation
since `atomBuild` is total. -/
def typeGrammar : Grammar Unit Ty := {
  levels := [[typeParens, arrowOp]]
  atomBuild := fun _ => Ty.base
  juxtBuild := none
}

/-- Token-level rendering of a `Ty`. Doubles as the printer companion of
`typeParser`. -/
def Ty.toTokens : Ty → List String
  | .base      => ["ι"]
  | .arrow a b => "(" :: Ty.toTokens a ++ "→" :: Ty.toTokens b ++ [")"]
  | .mvar n    => [s!"?{n}"]

/-! ## Term grammar -/

/-- Sub-parser for types, using `typeGrammar`. -/
def typeParser : Parser Unit Ty where
  run := fun s input =>
    match parseTree typeGrammar s input with
    | none                 => none
    | some (s', t, rest)   => some (s', Tree.eval typeGrammar t, rest.val)
  printer := Ty.toTokens

/-- Closed: `( e )`. -/
def termParens : Operator Unit Term := {
  fixity := .closed
  nameParts := ["(", ")"]
  nameParts_ne_nil := by decide
  holes := [.recurse]
  holes_match_arity := by decide
  build := fun (e : Term) => e
}

/-- Prefix: `λ x : τ . body`. -/
def lamOp : Operator Unit Term := {
  fixity := .prefix
  nameParts := ["λ", ":", "."]
  nameParts_ne_nil := by decide
  holes := [.sub stringParser, .sub typeParser, .recurse]
  holes_match_arity := by decide
  build := fun (x : String) (τ : Ty) (body : Term) => .lam x τ body
}

/-- Term grammar. Variables are atoms; `λ` is prefix; application is
juxtaposition. -/
def termGrammar : Grammar Unit Term := {
  levels := [[termParens, lamOp]]
  atomBuild := fun s => Term.var s
  juxtBuild := some (fun a b => Term.app a b)
}

/-- Token-level rendering of a `Term`. Doubles as the printer companion
of `termParser`. -/
def Term.toTokens : Term → List String
  | .var x        => [x]
  | .lam x τ body =>
      "(" :: "λ" :: x :: ":" :: Ty.toTokens τ ++ "." :: Term.toTokens body ++ [")"]
  | .app a b      => "(" :: Term.toTokens a ++ Term.toTokens b ++ [")"]

/-- Sub-parser for terms, using `termGrammar`. Suitable for the
vernacular's body slot. -/
def termParser : Parser Unit Term where
  run := fun s input =>
    match parseTree termGrammar s input with
    | none                 => none
    | some (s', t, rest)   => some (s', Tree.eval termGrammar t, rest.val)
  printer := Term.toTokens

/-! ## Top-level entry points -/

/-- Tokenize a string by whitespace, dropping empty pieces. -/
def tokenize (s : String) : List String :=
  s.splitOn " " |>.filter (· != "")

/-- Parse a token list to a `Term`, requiring all tokens to be consumed. -/
def parseTokens (input : List String) : Option Term :=
  (parseAll termGrammar () input).map (·.snd)

/-- Parse a string to a `Term` via the whitespace tokenizer. -/
def parse (s : String) : Option Term :=
  parseTokens (tokenize s)

end LambdaLab.Stlc.Named.Parser
