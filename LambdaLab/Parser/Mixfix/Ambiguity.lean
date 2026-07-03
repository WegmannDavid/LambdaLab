import LambdaLab.Parser.Mixfix.Verified

/-!
# Distinct leading tokens do not give unambiguity

A machine-checked obstruction for discharging `Grammar.Unambiguous`: the
distinct-*leading*-tokens condition (a token resolves to at most one operator)
is **insufficient**.

The grammar `amb` below has three operators with pairwise-distinct leading
tokens —

* `num`  — closed `n`
* `wrap` — closed `( _ * _ )`   (leading token `(`)
* `mul`  — infix  `_ * _`        (leading name token `*`)

— yet `( n * n * n )` parses two ways: `wrap n (n * n)` and `wrap (n * n) n`,
because `wrap`'s middle name-part `*` collides with `mul`'s name token, and
`wrap`'s holes (at `loosest`) can absorb a `mul`.

The culprit is a *follow* condition, not a *leading* one: here the token `*`
immediately follows a hole of `wrap` while also naming an infix operator
reachable at that hole's level. Any sufficient unambiguity criterion must
exclude this — e.g.: **a name-part token immediately following a hole at level
`ℓ` must not be the name token of an infix operator reachable at `ℓ`** (for
`arith` this holds: `)` follows `paren`'s hole and names no infix).
-/

namespace LambdaLab.Parser.Mixfix

open LambdaLab.Parser

inductive AmbOp where
  | num | wrap | mul
deriving DecidableEq, Repr

def ambOperator : AmbOp → Operator Empty
  | .num  => .closed (.last "n")
  | .wrap => .closed (.cons "(" .loosest (.cons "*" .loosest (.last ")")))
  | .mul  => .infx (.last "*")

def ambTighter : AmbOp → List AmbOp
  | .num => [] | .wrap => [] | .mul => [.wrap, .num]

def ambRank : AmbOp → Nat
  | .num => 0 | .wrap => 0 | .mul => 1

theorem ambTighter_wf : WellFounded (fun b a => b ∈ ambTighter a) :=
  Subrelation.wf (r := fun x y => ambRank x < ambRank y)
    (fun {x y} h => by cases x <;> cases y <;> simp_all [ambTighter, ambRank])
    (measure ambRank).wf

/-- The counterexample grammar. Leading tokens `n`, `(`, `*` are pairwise
distinct (the distinct-leading-tokens condition), yet the grammar is ambiguous. -/
@[reducible] def amb : Grammar.{0} where
  Op := AmbOp
  Sub := Empty
  subParser := fun e => e.elim
  operator := ambOperator
  loosest := [.mul]
  tighter := ambTighter
  tighter_wf := ambTighter_wf
  isVar := fun _ => false
  juxtUnique := fun o₁ o₂ h₁ _ => by cases o₁ <;> simp [ambOperator] at h₁

/-- `n` as a loosest expression. -/
def nL : Expr amb .loosest :=
  .op .num ⟨.mul, by simp, .step (by simp [ambTighter]) .refl⟩
    (.namePart "n" .nil)

/-- `n` at level `tighter mul`. -/
def nT : Expr amb (.tighter .mul) :=
  .op .num (.base (by simp [ambTighter])) (.namePart "n" .nil)

/-- `n * n` as a loosest expression. -/
def nMulN : Expr amb .loosest :=
  .op .mul ⟨.mul, by simp, .refl⟩
    (.hole nT (.namePart "*" (.hole nT .nil)))

/-- `( x * y )` via the closed `wrap` operator. -/
def wrapped (x y : Expr amb .loosest) : Expr amb .loosest :=
  .op .wrap ⟨.mul, by simp, .step (by simp [ambTighter]) .refl⟩
    (.namePart "(" (.hole x (.namePart "*" (.hole y (.namePart ")" .nil)))))

theorem wrapped_left_flatten :
    (wrapped nL nMulN).flatten = ["(", "n", "*", "n", "*", "n", ")"] := rfl

theorem wrapped_right_flatten :
    (wrapped nMulN nL).flatten = ["(", "n", "*", "n", "*", "n", ")"] := rfl

theorem wrapped_ne : wrapped nL nMulN ≠ wrapped nMulN nL := by
  intro h
  unfold wrapped nL nMulN at h
  injection h with _ _ hp
  injection hp with _ _ hp2
  injection hp2 with _ _ he _
  injection he with _ ho _
  exact AmbOp.noConfusion ho

/-- **Distinct leading tokens are not enough**: `amb` is ambiguous. -/
theorem amb_not_unambiguous : ¬ amb.Unambiguous := fun h =>
  wrapped_ne (h _ _ (wrapped_left_flatten.trans wrapped_right_flatten.symm))

end LambdaLab.Parser.Mixfix
