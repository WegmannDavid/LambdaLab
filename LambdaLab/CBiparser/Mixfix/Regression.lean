import LambdaLab.CBiparser.Mixfix.Biparser
import LambdaLab.CBiparser.Mixfix.Example

/-!
# Regression: the parser must be independent of operator ORDER

This file exists because the parser was once **wrong here**, and the bug was invisible in
`arith` (which has a single loosest operator). It is kept as a regression test.

## The bug (fixed by longest-match in `Parse.lean`)

`parseInfixL` **must** fall through to a bare left operand when its infix token is absent —
`a` alone is a legitimate expression at `tighterEq plus`. So **every left-recursive candidate
"succeeds" trivially**, by parsing an operand and nothing more.

The old `parseExprList` walked the candidate list with `orElse` and took the **first success**.
The first infix operator in the list therefore always won *by falling through*, and the operator
that actually matched the tokens was never tried. The parser's answer depended on the order you
happened to list your operators:

    loosest := [times, plus]  →  some (["a"], ["+", "b"])     -- partial parse!
    loosest := [plus, times]  →  some (["a", "+", "b"], [])   -- correct

`headsDistinct` does **not** rule this out: it makes dispatch deterministic on an operator's
*leading* token, but a left-recursive operator's distinguishing token arrives **after** the left
operand, by which time the candidate loop has already committed.

## The fix

`parseExprList` now takes the **longest match** — the candidate that consumes the most. A
candidate that genuinely uses its operator consumes strictly more than one that merely falls
through to a sub-expression, so the right operator wins whatever the order. Ties keep the earlier
candidate, so the parser stays deterministic.

## What this does *not* fix

Completeness-as-equality (`parse (t.flatten ++ rest) = some (t, rest)`) still requires `flatten`
to be **injective** — i.e. the grammar to be unambiguous. That holds for *any* deterministic
parser: if two distinct trees flatten alike, a deterministic parser returns one of them, and the
other cannot round-trip. `headsDistinct` does not supply unambiguity (this repo has a
machine-checked counterexample to that implication). So `mixfix_ok` will need an unambiguity
hypothesis on `Grammar` — independently of this bug.
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

/-! ## The regression test

`a + b` must parse fully **regardless of the order** `+` and `*` are listed in. Before the fix,
`qG` (which lists `times` first) returned a partial parse. -/

example : ((biparser qG () .loosest).run [tk "a", tk "+", tk "b"]).map
    (fun r => (r.1.flatten.map (·.val), r.2.map (·.val)))
      = some (["a", "+", "b"], []) := by native_decide

example : ((biparser qG' () .loosest).run [tk "a", tk "+", tk "b"]).map
    (fun r => (r.1.flatten.map (·.val), r.2.map (·.val)))
      = some (["a", "+", "b"], []) := by native_decide

/-- The *other* operator must work in both orders too — the fix must not merely swap the bias. -/
example : ((biparser qG () .loosest).run [tk "a", tk "*", tk "b"]).map
    (fun r => (r.1.flatten.map (·.val), r.2.map (·.val)))
      = some (["a", "*", "b"], []) := by native_decide

example : ((biparser qG' () .loosest).run [tk "a", tk "*", tk "b"]).map
    (fun r => (r.1.flatten.map (·.val), r.2.map (·.val)))
      = some (["a", "*", "b"], []) := by native_decide

end LambdaLab.CBiparser.Mixfix
