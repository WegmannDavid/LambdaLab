import LambdaLab.Parser.Mixfix2.Basic

/-!
# Grammar-indexed parse trees (Mixfix2)

The goal of this variant is a **bijection between parse trees and token
streams**: every well-typed tree flattens to a distinct string, and
parsing inverts flattening. Disambiguation lives *in the type*.

The mechanism is precedence-by-depth. A grammar `G : List Operator` is
read loosest-first. `Tree G d` is an expression built using only the
operators at depth `≥ d`, i.e. the suffix `G.drop d`:

* `Tree.top  : Node G d     → Tree G d` — outermost operator is `G[d]`.
* `Tree.next : Tree G (d+1) → Tree G d` — defer to something tighter.

The level index is a *bare depth* — a bookmark into `G`, carrying no
grammar data of its own. The loosest level is `0` (all of `G`); the
tightest is `G.length` (no operators, hence uninhabited). For any string
the loosest operator present is forced, so `top` vs. `next` is forced —
that is the injectivity of flattening.

There are **no atom leaves**. The tightest entries in `G` must be
`closed` operators: a constant is a nullary `closed` op, and grouping is
a `closed` op like `( _ )` whose interior hole resets to level `0`. Hence
"to regroup, add a parenthesis operator and strip it later" is the only
regrouping available — by design.
-/

namespace LambdaLab.Parser.Mixfix2

/-- The depth of each recursive hole of `Op`, in token order, when `Op`
sits at level `d`. The list length is `Op.arity`.

* Interior holes (strictly between two name-parts) reset to level `0`:
  they are delimited on both sides.
* A leading/trailing hole sits at level `d` (same — permits chaining) or
  at `d + 1` (strictly tighter), per fixity/associativity:
  - `prefix`  trailing → same level   (`- - a`)
  - `postfix` leading  → same level   (`a ! !`)
  - `infix .left`      → left same, right tighter   (`(a - b) - c`)
  - `infix .right`     → left tighter, right same   (`a ⇒ (b ⇒ c)`)
  - `infix .nonAssoc`  → both tighter
-/
def Operator.childLevels (Op : Operator) (d : Nat) : List Nat :=
  let interior := List.replicate (Op.nameParts.length - 1) 0
  match Op.fixity with
  | .closed          => interior
  | .prefix          => interior ++ [d]
  | .postfix         => d :: interior
  | .infix .left     => d :: (interior ++ [d + 1])
  | .infix .right    => (d + 1) :: (interior ++ [d])
  | .infix .nonAssoc => (d + 1) :: (interior ++ [d + 1])

mutual

  /-- An expression at level `d` (built from `G`'s operators at depth
  `≥ d`). The index is a bare `Nat`; levels `d ≥ G.ops.size` are
  uninhabited (nothing is tighter than the tightest operator). -/
  inductive Tree (G : Grammar) : Nat → Type where
    | top  {d : Nat} : Node G d → Tree G d
    | next {d : Nat} : Tree G (d + 1) → Tree G d

  /-- A fully-applied instance of the operator at depth `d`: its recursive
  holes filled by trees at the levels `(G.ops[d]).childLevels d` prescribes.
  The bound `h : d < G.ops.size` witnesses that an operator exists at `d`
  (so `Node G d` is uninhabited past the end of `G`) and gives total access
  to it. A constant (`closed`, one name-part) has no children. -/
  inductive Node (G : Grammar) : Nat → Type where
    | mk {d : Nat} (h : d < G.ops.size) :
        Children G ((G.ops[d]'h).childLevels d) → Node G d

  /-- A heterogeneous list of child trees, one per hole, each at the
  depth demanded by its position. -/
  inductive Children (G : Grammar) : List Nat → Type where
    | nil  : Children G []
    | cons {L : Nat} {Ls : List Nat} :
        Tree G L → Children G Ls → Children G (L :: Ls)

end

/-- A complete expression: a tree at the loosest level `0`. -/
abbrev Expr (G : Grammar) : Type := Tree G 0

end LambdaLab.Parser.Mixfix2
