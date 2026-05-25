import LambdaLab.Parser.Mixfix2.Tree

/-!
Sanity checks for the grammar-indexed tree. Grammar (loosest-first):

    +        infix, left-associative   (depth 0)
    1        nullary constant          (depth 1)

A constant is reached by `next`-ing down to its depth; an infix node
places its left arg at the same level (chaining) and its right arg one
level tighter.
-/

namespace LambdaLab.Parser.Mixfix2.Example

def add : Operator where
  fixity := .infix .left
  nameParts := ["+"]
  nameParts_ne_nil := by simp

def one : Operator := .const "1"

abbrev G : Grammar := { ops := #[add, one], nameParts_nodup := by decide }

/-- The constant `1` reached directly at depth `1` (the tighter slot). -/
def one1 : Tree G 1 := .top (.mk (by decide) .nil)

/-- The constant `1`, as a complete expression: `next` past `+` (depth 0)
to reach `1` (depth 1). -/
def e1 : Expr G := .next one1

/-- `1 + 1`. `+`'s children sit at levels `[0, 1]`: left at the same
level, right one tighter. -/
def e1plus1 : Expr G :=
  .top (.mk (by decide) (.cons e1 (.cons one1 .nil)))

/-- `1 + 1 + 1` — left-associated: the left child is itself a `+` node
(well-typed only because the left hole sits at the same level `0`). -/
def e1plus1plus1 : Expr G :=
  .top (.mk (by decide) (.cons e1plus1 (.cons one1 .nil)))

end LambdaLab.Parser.Mixfix2.Example
