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

/-- The fixity of an operator. `infixr` is a right-associative binary infix `a ⊙ b`;
`prefix` is a unary leading operator `⊙ a`. (More fixities — infixl, postfix, non-assoc,
juxt — are added in later stages.) -/
inductive Fixity where
  | infixr
  | prefix
deriving DecidableEq

/-- A generic grammar: `ops[k] = (c, fx)` is the operator character `c` at precedence
level `k` (higher index = binds tighter) with fixity `fx`; `isVar` recognizes variable
characters. Brackets `(`/`)` and the space separator are built in and assumed disjoint
from `ops` and `isVar`. -/
structure Grammar where
  ops : List (Char × Fixity)
  isVar : Char → Bool

/-- The operator character at precedence `k`. -/
def Grammar.opChar (G : Grammar) (k : Nat) (hk : k < G.ops.length) : Char := (G.ops[k]'hk).1
/-- The fixity at precedence `k`. -/
def Grammar.opFixity (G : Grammar) (k : Nat) (hk : k < G.ops.length) : Fixity := (G.ops[k]'hk).2

/-- A precedence-indexed parse tree: an inhabitant of `Tree G p` is an expression whose
top operator binds **at least as tightly as** level `p`. A `var`/`paren` is an atom
(tighter than everything, so valid at any `p`); an operator node at precedence `k` is
valid at levels `p ≤ k` and carries a proof pinning it to its declared fixity.

* `op` — right-assoc infix: left operand one level tighter (`k+1`), right chains (`k`).
* `pre` — prefix: a single operand one level tighter (`k+1`). -/
inductive Tree (G : Grammar) : Nat → Type where
  | var   {p : Nat} (c : Char) : G.isVar c = true → Tree G p
  | paren {p : Nat} : Tree G 0 → Tree G p
  | op    {p : Nat} (k : Nat) (hk : k < G.ops.length) (hfix : G.opFixity k hk = .infixr)
            (hp : p ≤ k) : Tree G (k + 1) → Tree G k → Tree G p
  | pre   {p : Nat} (k : Nat) (hk : k < G.ops.length) (hfix : G.opFixity k hk = .prefix)
            (hp : p ≤ k) : Tree G (k + 1) → Tree G p

/-! ### A sample grammar for `#eval` sanity checks. -/

/-- `+` (prec 0, infix), `*` (prec 1, infix), `-` (prec 2, prefix); lowercase = variables. -/
def sample : Grammar where
  ops := [('+', .infixr), ('*', .infixr), ('-', .prefix)]
  isVar := fun c => 'a' ≤ c && c ≤ 'z'

/-- `a + b * c`. -/
def sampleTree : Tree sample 0 :=
  .op 0 (by decide) (by decide) (by decide)
    (.var 'a' (by decide))
    (.op 1 (by decide) (by decide) (by decide) (.var 'b' (by decide)) (.var 'c' (by decide)))

/-- `- a + b` (prefix `-` binds tighter than `+`): `(- a) + b`. -/
def sampleTree2 : Tree sample 0 :=
  .op 0 (by decide) (by decide) (by decide)
    (.pre 2 (by decide) (by decide) (by decide) (.var 'a' (by decide)))
    (.var 'b' (by decide))

end LambdaLab.ParserExperimental1.Mixfix
