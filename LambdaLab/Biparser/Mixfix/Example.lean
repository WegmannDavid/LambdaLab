import LambdaLab.Biparser.Mixfix.Tree

/-!
# A concrete example grammar, and `flatten` as the canonical print

Phase 2 is essentially free: the token-level canonical print **is** `Expr.flatten`
(from `Tree.lean`) — it emits each name-part token and each operand's flattening in
body order, with no separators (separators belong to the later char↔token layer).
So the mixfix biparser's print will be `fun t => (t, t.flatten)`.

This file's real job is to *validate* the grammar/Tree machinery by building a real
`Grammar` (one entry: `( _ )`, application, left-assoc `+`) and a couple of `Expr`
trees, then showing `flatten`. It doubles as the test fixture for Phases 3–4.
-/

namespace LambdaLab.Biparser.Mixfix

/-- Space is the only separator. -/
def arithSep : Char → Bool := fun c => c == ' '

/-- A separator-free token literal; the proof is discharged by `decide`. -/
def tk (s : String) (h : (∀ c ∈ s.toList, arithSep c = false) ∧ s.toList ≠ [] := by decide) :
    Token arithSep := ⟨s, h⟩

/-- Operators of the single entry: parentheses, application (`juxt`), `_ + _`. -/
inductive PSym | paren | app | plus
  deriving DecidableEq, Repr

def preserved : List (Token arithSep) := [tk "(", tk ")", tk "+"]

def psymTighter : PSym → List PSym
  | .plus  => [.app]
  | .app   => [.paren]
  | .paren => []

def psymRank : PSym → Nat
  | .paren => 0 | .app => 1 | .plus => 2

theorem psymTighter_wf : WellFounded (fun b a => b ∈ psymTighter a) :=
  Subrelation.wf
    (r := fun x y => psymRank x < psymRank y)
    (fun {x y} (h : x ∈ psymTighter y) => by
      cases x <;> cases y <;> simp_all [psymTighter, psymRank])
    (measure psymRank).wf

def psymOp : PSym → Operator arithSep Unit
  | .paren => .closed (.cons (tk "(") () (.last (tk ")")))
  | .app   => .juxt
  | .plus  => .infxl (.last (tk "+"))

def pEntry : Entry arithSep Unit where
  Op := PSym
  operator := psymOp
  loosest := [.plus]
  tighter := psymTighter
  tighter_wf := psymTighter_wf
  isVar := fun t => decide (t ∉ preserved)
  juxtUnique := fun o₁ o₂ h₁ h₂ => by cases o₁ <;> cases o₂ <;> simp_all [psymOp]
  headsDistinct := by intro o₁ o₂ _ _; cases o₁ <;> cases o₂ <;> simp_all [psymOp, Operator.headTok?, Operator.nameTokens, Notation.toTokens, tk]
  varDisjoint := by intro o; cases o <;> decide

/-- The grammar: one entry, space is the only separator. -/
def arith : Grammar where
  Ent := Unit
  isSep := arithSep
  sepWitness := ⟨' ', by decide⟩
  entry := fun _ => pEntry

/-- A variable leaf `x` at the loosest level. -/
def exVar : Expr arith () .loosest := .var (tk "x") (by decide)

-- `flatten` IS the canonical token-level print (operator trees, which are painful
-- to hand-build, will be produced by the Phase 3 parser and flattened then):
#eval exVar.flatten.map (·.val)    -- ["x"]

end LambdaLab.Biparser.Mixfix
