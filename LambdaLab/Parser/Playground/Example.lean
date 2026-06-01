import LambdaLab.Parser.Playground.Parse

/-!
# A minimal concrete grammar for the Playground

Every operator here is *closed*: it begins and ends with a literal token,
with `arity` child holes strictly interior. We use a tiny arithmetic-ish
grammar — a constant, parentheses, and a bracketed `+` — and show that
`parse` inverts `Tree.flatten`.

For `lookup` to be unambiguous, the operators must have *distinct leading
tokens*. That is why `add` is written `[ _ + _ ]` rather than `( _ + _ )`:
otherwise it would collide with `paren`'s leading `(`.
-/

namespace LambdaLab.Parser.Playground

/-- Three operators. `num` is a nullary constant `n`; `paren` is `( _ )`;
`add` is the bracketed `[ _ + _ ]`. -/
inductive Sym where
  | num
  | paren
  | add
deriving DecidableEq, Repr

def arith : Grammar where
  Op := Sym
  arity
    | .num   => 0
    | .paren => 1
    | .add   => 2
  OpDescs
    | .num   => .last "n"                          -- shape:  n
    | .paren => .part "(" (.last ")")              -- shape:  ( _ )
    | .add   => .part "[" (.part "+" (.last "]"))  -- shape:  [ _ + _ ]
  lookup
    | "n" => some .num
    | "(" => some .paren
    | "[" => some .add
    | _   => none
  lookup_spec := by
    intro o tkn
    cases o <;>
      (simp only [beginsWith, decide_eq_true_eq]
       constructor
       · rintro rfl; rfl
       · intro h; split at h <;> simp_all)

/-- The constant `n`. -/
def num : Tree arith := .op .num .last

/-- `( e )`. -/
def paren (e : Tree arith) : Tree arith := .op .paren (.part e .last)

/-- `[ l + r ]`. -/
def add (l r : Tree arith) : Tree arith := .op .add (.part l (.part r .last))

/-- The tree `( [ n + n ] )`. -/
def example₁ : Tree arith := paren (add num num)

-- ( [ n + n ] )  ↝  ["(", "[", "n", "+", "n", "]", ")"]
#eval example₁.flatten

/-- `flatten` gives the bracketed rendering. -/
example : example₁.flatten = ["(", "[", "n", "+", "n", "]", ")"] := rfl

/-! ## Round-trip: `parse` inverts `flatten`

`Tree arith` has no `DecidableEq` (its `Op` is an arbitrary type), so we
witness the round-trip by re-flattening the parse result and comparing token
streams: `flatten ∘ parse ∘ flatten = flatten`.

(`parse` is defined by well-founded recursion, so it does not reduce by `rfl`;
we use `#guard`, which evaluates via the compiler and fails the build if the
check is false — a real, axiom-free, build-time check.) -/

/-- Full parser for `arith`: parse one tree and require every token consumed. -/
def parse : List Token → Option (Tree arith) := parseAll (parser arith)

-- some ["(", "[", "n", "+", "n", "]", ")"]
#eval (parse example₁.flatten).map (·.flatten)

#guard (parse example₁.flatten).map (·.flatten) == some example₁.flatten

-- Parsing a bare constant and a nested paren both succeed.
#guard (parse ["n"]).map (·.flatten) == some ["n"]
#guard (parse ["(", "(", "n", ")", ")"]).map (·.flatten)
        == some ["(", "(", "n", ")", ")"]

-- Malformed input is rejected.
#guard (parse ["(", "]"]).isNone            -- wrong closer
#guard (parse ["[", "n", "+", "n"]).isNone  -- missing trailing "]"
#guard (parse ["n", "n"]).isNone            -- trailing junk

end LambdaLab.Parser.Playground
