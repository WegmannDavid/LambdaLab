import LambdaLab.ParserExperimental1.Biparser.Combinators

/-!
# A generic, data-driven mixfix grammar — combinator weak-biparser

`Telescope.lean` verified *one* hardcoded grammar (parens + right-assoc `+`) from
combinators. This directory generalizes it to a **data-driven** grammar and grows toward
the full functionality of `Parser/Mixfix` (all fixities, notations, precedence), keeping
the weak target (`parse_complete` only) and the combinator style: every token/gap leaf is
a combinator, only the recursive skeleton is hand-rolled.

File layout:
* `Basic`    — the grammar data and the precedence-indexed `Tree`.
* `Leaves`   — the combinator leaves (`varTok`/`lpGap`/`gapRp`/`gapOpGap`, …).
* `Render`   — the telescope `render` (built from the leaves).
* `Parse`    — the char-level parser.
* `Complete` — `parse_complete` and the assembled `Biparser`.

This file: the grammar and the tree. Operators are a precedence-ordered table of
right-associative infix characters; brackets `(`/`)` and the space separator are built in.
The tree is **precedence-indexed** (`Tree G p` binds at least as tightly as level `p`), a
plain-`Nat` analogue of `Parser/Mixfix`'s `Level`-indexed `Expr G`, so `render` never has
to *decide* where to parenthesize.
-/

namespace LambdaLab.ParserExperimental1.Mixfix

open LambdaLab.ParserExperimental1

/-- A generic grammar: `ops[k]` is the right-associative infix operator character at
precedence level `k` (higher index = binds tighter); `isVar` recognizes variable
characters. Brackets `(`/`)` and the space separator are built in and assumed disjoint
from `ops` and `isVar`. -/
structure Grammar where
  ops : List Char
  isVar : Char → Bool

/-- A precedence-indexed parse tree: an inhabitant of `Tree G p` is an expression whose
top operator binds **at least as tightly as** level `p`. A `var`/`paren` is an atom
(tighter than everything, so valid at any `p`); an `op k` node has precedence `k` and is
valid at levels `p ≤ k`. Right-associative: the left operand is one level tighter
(`k+1`), the right operand chains at the same level (`k`). -/
inductive Tree (G : Grammar) : Nat → Type where
  | var   {p : Nat} (c : Char) : G.isVar c = true → Tree G p
  | paren {p : Nat} : Tree G 0 → Tree G p
  | op    {p : Nat} (k : Nat) (hk : k < G.ops.length) (hp : p ≤ k) :
            Tree G (k + 1) → Tree G k → Tree G p

/-! ### A sample grammar for `#eval` sanity checks. -/

/-- `+` (prec 0, loose) and `*` (prec 1, tight); lowercase letters are variables. -/
def sample : Grammar where
  ops := ['+', '*']
  isVar := fun c => 'a' ≤ c && c ≤ 'z'

/-- `a + b * c` as a tree: `+` at prec 0 with right operand `b * c` at prec 1. -/
def sampleTree : Tree sample 0 :=
  .op 0 (by decide) (by decide)
    (.var 'a' (by decide))
    (.op 1 (by decide) (by decide) (.var 'b' (by decide)) (.var 'c' (by decide)))

end LambdaLab.ParserExperimental1.Mixfix
