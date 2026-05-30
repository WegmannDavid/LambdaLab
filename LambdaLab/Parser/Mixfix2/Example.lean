import LambdaLab.Parser.Mixfix2.Bijection

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

/-! ## Parse round-trips for all four fixities

A richer grammar exercising prefix/postfix/infix parsing. Loosest-first:

    + (infix .left), - (prefix), ! (postfix), 1 (const)

`run` renders the parse result as `(parsed-tree-flatten, leftover)`; for a
complete parse the flatten equals the input and the leftover is empty —
i.e. the token stream round-trips through `parse`. -/

def neg : Operator where
  fixity := .prefix
  nameParts := ["-"]
  nameParts_ne_nil := by simp
def bang : Operator where
  fixity := .postfix
  nameParts := ["!"]
  nameParts_ne_nil := by simp

abbrev G2 : Grammar :=
  { ops := #[add, neg, bang, one], nameParts_nodup := by decide }

/-- Render `parse 0 s` as `(flatten, leftover)`. -/
def run (s : List String) : Option (List String × List String) :=
  match parse G2 0 s with
  | some (t, r) => some (t.flatten, r.val)
  | none        => none

-- closed constant
#eval run ["1"]                       -- some ([1], [])
-- left-associative infix chaining
#eval run ["1", "+", "1", "+", "1"]   -- some ([1,+,1,+,1], [])
-- prefix, chained
#eval run ["-", "-", "1"]             -- some ([-,-,1], [])
-- postfix, chained
#eval run ["1", "!", "!"]             -- some ([1,!,!], [])
-- mixed precedence
#eval run ["-", "1", "+", "1", "!"]   -- some ([-,1,+,1,!], [])
-- leftover handling
#eval run ["1", "+", "1", "extra"]    -- some ([1,+,1], [extra])

/-- Every example round-trips: `parse` returns the full input with no
leftover. (`native_decide`-checked since `run` is computable but built by
well-founded recursion, so it does not reduce by `rfl`.) -/
example : run ["1", "+", "1", "+", "1"] = some (["1", "+", "1", "+", "1"], []) := by native_decide
example : run ["-", "-", "1"] = some (["-", "-", "1"], []) := by native_decide
example : run ["1", "!", "!"] = some (["1", "!", "!"], []) := by native_decide
example : run ["-", "1", "+", "1", "!"] = some (["-", "1", "+", "1", "!"], []) := by native_decide

end LambdaLab.Parser.Mixfix2.Example
