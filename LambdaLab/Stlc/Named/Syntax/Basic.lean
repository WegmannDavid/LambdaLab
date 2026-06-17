import LambdaLab.Parser.Mixfix.Verified
import LambdaLab.Parser.Tokenizer

/-!
# Surface syntax of named STLC: the mixfix grammar + derived parser

This is the STLC-specific instance of the generic mixfix parser
(`LambdaLab/Parser/Mixfix/`). It pins a concrete `Grammar` — three operators
(parentheses, application by juxtaposition, lambda) plus variable leaves — and
derives the string → `Expr` front end by composing the tokenizer with the
generic `parse`.

The resulting `Expr stlc .loosest` is the *concrete syntax tree*; `Syntax.Truncate`
turns it into a `Term`.

## Precedence

Loosest → tightest: `lam → app → paren`. Application binds tighter than lambda
(`\lambda x . f x` is `\lambda x . (f x)`); parentheses/atoms are tightest.

**Limitation (inherited from the `prefx` encoding):** a `lam` body sits at
`.tighter lam` (strictly tighter), so a lambda body cannot itself be a bare
lambda — `\lambda x . \lambda y . e` must be written `\lambda x . (\lambda y . e)`.
Lifting this needs a loosest-body / right-associative prefix in the parser core.
-/

namespace LambdaLab.Stlc.Named.Syntax

open LambdaLab.Parser
open LambdaLab.Parser.Mixfix

/-- Surface operators of STLC. Variables are leaves (any non-reserved token),
not operators. -/
inductive Sym where
  | paren | app | lam
  deriving DecidableEq, Repr

/-- The operator name-part tokens; these cannot be used as variable names. -/
def reserved : List Token := ["(", ")", "\\lambda", "."]

/-- The binder sub-language: a grammar with **no operators**, so its parser
accepts exactly one variable. Parses the `x` in `\lambda x .`. -/
def varGrammar : Grammar.{0} where
  Op := Empty
  operator := fun e => e.elim
  loosest := []
  tighter := fun e => e.elim
  tighter_wf := ⟨fun e => e.elim⟩
  isVar := fun t => decide (t ∉ reserved)
  juxtUnique := fun e => e.elim

/-- Each operator's shape. `lam`'s binder hole is `varGrammar` (a different
language, embedded via `toVerifiedParser`); its body is the ordinary recursive
operand. -/
def symOp : Sym → Operator
  | .paren => .closed (.cons "(" .loosest (.last ")"))
  | .app   => .juxt
  | .lam   => .prefx (.cons "\\lambda" (.sub varGrammar.toVerifiedParser) (.last "."))

/-- Precedence DAG: `lam → app → paren`. -/
def symTighter : Sym → List Sym
  | .lam   => [.app]
  | .app   => [.paren]
  | .paren => []

/-- A rank witnessing acyclicity (higher = looser). -/
def symRank : Sym → Nat
  | .paren => 0 | .app => 1 | .lam => 2

theorem symTighter_wf : WellFounded (fun b a => b ∈ symTighter a) :=
  Subrelation.wf
    (r := fun x y => symRank x < symRank y)
    (fun {x y} (h : x ∈ symTighter y) => by
      cases x <;> cases y <;> simp_all [symTighter, symRank])
    (measure symRank).wf

/-- The STLC surface grammar. `@[reducible]` so `stlc.Op` unfolds to `Sym`. -/
@[reducible] def stlc : Grammar where
  Op := Sym
  operator := symOp
  loosest := [.lam]
  tighter := symTighter
  tighter_wf := symTighter_wf
  isVar := fun t => decide (t ∉ reserved)
  juxtUnique := fun o₁ o₂ h₁ h₂ => by cases o₁ <;> cases o₂ <;> simp_all [symOp]

/-! ## The derived front end: string → concrete syntax tree -/

/-- All parses of a token list as an STLC concrete syntax tree. -/
def parseTokens (tkns : List Token) : List (Expr stlc .loosest) :=
  Mixfix.parse (G := stlc) tkns

/-- All parses of a source string: tokenize, then parse. -/
def parse (s : String) : List (Expr stlc .loosest) :=
  parseTokens (Tokenizer.tokenize s)

/-- Round-trip view for the `#eval`s below: the flattening of each parse. -/
def run (s : String) : List (List Token) := (parse s).map Expr.flatten

-- NB the tokenizer is whitespace-separated (Agda-style), so every token —
-- including `(` and `)` — must be space-separated: write `( f x )`, not `(f x)`.
#eval run "x"                                  -- var
#eval run "f x y"                              -- app, left-associative
#eval run "\\lambda x . x"                     -- identity
#eval run "( \\lambda x . x ) y"               -- applied identity
#eval run "\\lambda f . ( \\lambda x . f x )"  -- nested lambda (parens required)

-- A parse exists and flattens back to the (space-canonical) input.
#guard (run "( \\lambda x . x ) y").any (· = ["(", "\\lambda", "x", ".", "x", ")", "y"])

end LambdaLab.Stlc.Named.Syntax
