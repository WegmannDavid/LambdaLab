import LambdaLab.CBiparser.Mixfix.Biparser
import LambdaLab.CBiparser.Mixfix.Example

/-!
# `mixfix_ok` is FALSE for the current parser — a machine-checked counterexample

**Do not try to prove `mixfix_ok` against `Parse.lean` as it stands. It is not true.**

The parser is **order-dependent**: its answer changes if you permute a grammar's `loosest`
list. Below, the *same* grammar and the *same* input `a + b` give

    loosest := [times, plus]  →  some (["a"], ["+", "b"])     -- partial parse!
    loosest := [plus, times]  →  some (["a", "+", "b"], [])   -- correct

## The mechanism

`parseInfixL` **must** fall through to a bare left operand when the infix token is absent —
`a` alone is a legitimate expression at `tighterEq plus`. But that means **every `infxl`
candidate "succeeds" trivially**, by parsing an operand and nothing more.

`parseExprList` then walks the candidate list with `orElse` and takes the **first success**. So
the first left-recursive operator in the list always wins — by falling through — and the
operator that actually matches the token stream is never tried.

`headsDistinct` does not save us: it makes dispatch deterministic on an operator's **leading**
token, but an infix operator's distinguishing token arrives **after** the left operand, and the
candidate loop has already committed by then.

## Why it appeared here and not in the other developments

Every *verified* mixfix parser in this repo (`Parser/Mixfix/Parse.lean`,
`ParserExperimental1/…`) returns **all parses** — `List (Expr × leftover)`, combined with `++`,
with completeness stated as membership (`t ∈ parse …`). Order cannot hurt you if you keep
everything.

The `Option`/`orElse` model here was chosen deliberately, for runtime. That choice is what
introduced this bug. `arith` never exposes it because it has exactly **one** loosest operator.

## The fix

Dispatch left-recursive operators by the token that follows the left operand (precedence
climbing / Pratt), rather than committing to a candidate before seeing it. Then `headsDistinct`
does the work it was meant to do, determinism is kept, and `mixfix_ok` becomes true as an
*equality* (not merely as membership).
-/

namespace LambdaLab.CBiparser.Mixfix

/-! ## A grammar with two incomparable infix operators at the loosest level -/

inductive Q | paren | app | plus | times
  deriving DecidableEq, Repr

def qTighter : Q → List Q
  | .plus => [.app] | .times => [.app] | .app => [.paren] | .paren => []

def qRank : Q → Nat
  | .paren => 0 | .app => 1 | .plus => 2 | .times => 2

theorem qWf : WellFounded (fun b a => b ∈ qTighter a) :=
  Subrelation.wf (r := fun x y => qRank x < qRank y)
    (fun {x y} (h : x ∈ qTighter y) => by cases x <;> cases y <;> simp_all [qTighter, qRank])
    (measure qRank).wf

def qOp : Q → Operator arithSep Unit
  | .paren => .closed (.cons (tk "(") () (.last (tk ")")))
  | .app   => .juxt
  | .plus  => .infxl (.last (tk "+"))
  | .times => .infxl (.last (tk "*"))

def qPreserved : List (Token arithSep) := [tk "(", tk ")", tk "+", tk "*"]

/-- `times` listed **before** `plus`. Both are `infxl`, both loosest, incomparable. -/
def qEntry : Entry arithSep Unit where
  Op := Q
  operator := qOp
  ops := [.paren, .app, .plus, .times]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.times, .plus]
  tighter := qTighter
  tighter_wf := qWf
  isVar := fun t => decide (t ∉ qPreserved)
  juxtUnique := fun a b h1 h2 => by cases a <;> cases b <;> simp_all [qOp]
  headsDistinct := by
    intro a b _ _; cases a <;> cases b <;>
      simp_all [qOp, Operator.headTok?, Operator.nameTokens, Notation.toTokens, tk]
  varDisjoint := by intro o; cases o <;> decide

def qG : Grammar := { arith with entry := fun _ => qEntry }

/-- The same grammar with the two operators listed the other way round. -/
def qG' : Grammar :=
  { arith with entry := fun _ => { qEntry with loosest := [.plus, .times] } }

/-! ## The refutation

`a + b` is a perfectly good tree of `qG`; its `flatten` is `["a","+","b"]`. Round-tripping it
requires `parse (flatten ++ []) = some (t, [])`, and `HeadIn (follow e) []` is *vacuously true*
— there is no side-condition to hide behind. Yet: -/

-- WRONG: the parser stops after `a`, leaving `+ b` unconsumed.
#eval ((biparser qG () .loosest).run [tk "a", tk "+", tk "b"]).map
        (fun r => (r.1.flatten.map (·.val), r.2.map (·.val)))
-- some (["a"], ["+", "b"])

-- CORRECT, and the ONLY thing that changed is the order of `loosest`.
#eval ((biparser qG' () .loosest).run [tk "a", tk "+", tk "b"]).map
        (fun r => (r.1.flatten.map (·.val), r.2.map (·.val)))
-- some (["a", "+", "b"], [])

end LambdaLab.CBiparser.Mixfix
