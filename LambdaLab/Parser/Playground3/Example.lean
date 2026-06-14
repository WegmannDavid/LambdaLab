import LambdaLab.Parser.Playground3.Parse

/-!
# A concrete grammar exercising the `Part`/`Parts` parser

A tiny arithmetic grammar over the full (`closed` / `prefx` / `infx` /
`postfx`) operator model:

* `num`   — the constant `n`        (closed, tightest)
* `paren` — `( _ )`                  (closed)
* `add`   — `_ + _`                  (loosest)
* `mul`   — `_ * _`                  (tighter than `add`)
* `neg`   — `- _`                    (prefix, between `add` and `mul`)
* `fac`   — `_ !`                    (postfix, between `mul` and the atoms)

Precedence DAG (loosest → tightest): `add → {mul, neg}`, `neg → mul`,
`mul → fac`, `fac → {paren, num}`, so `n + n * n` groups as `n + (n * n)`,
`- n * n` as `- (n * n)`, and `n ! * n` as `(n !) * n`. The `#eval`s at the
bottom run the parser and re-flatten each parse — well-formed inputs
round-trip to themselves, malformed inputs yield no full parse.
-/

namespace LambdaLab.Parser.Playground3

open LambdaLab.Parser

/-- Operator names. `app` is juxtaposition (function application). -/
inductive Sym where
  | num | paren | add | mul | neg | fac | app
deriving DecidableEq, Repr

/-- Each operator's shape. -/
def symOp : Sym → Operator
  | .num   => .closed (.last "n")
  | .paren => .closed (.cons "(" (.last ")"))
  | .add   => .infx (.last "+")
  | .mul   => .infx (.last "*")
  | .neg   => .prefx (.last "-")
  | .fac   => .postfx (.last "!")
  | .app   => .juxt

/-- Immediately-tighter successors: `add → {mul, neg}`, `neg → mul`,
`mul → fac`, `fac → {paren, num}`. Unary minus binds looser than `*` (so
`- n * n` is `- (n * n)`); factorial binds tighter than `*` (so `n ! * n` is
`(n !) * n`). Both unary operators are non-assoc — the operand hole is
*strictly* tighter — so neither nests unparenthesized: `- - n` and `n ! !`
need parentheses. -/
def symTighter : Sym → List Sym
  | .num   => []
  | .paren => []
  | .add   => [.mul, .neg]
  | .neg   => [.mul]
  | .mul   => [.fac]
  | .fac   => [.app]
  | .app   => [.paren, .num]

/-- A rank witnessing acyclicity: higher = looser. Application sits just above the
atoms (`paren`/`num`) and below every named operator. -/
def symRank : Sym → Nat
  | .num => 0 | .paren => 0 | .app => 1 | .fac => 2 | .mul => 3 | .neg => 4 | .add => 5

/-- `tighter` is well-founded: each step strictly drops the rank. -/
theorem symTighter_wf : WellFounded (fun b a => b ∈ symTighter a) :=
  Subrelation.wf
    (r := fun x y => symRank x < symRank y)
    (fun {x y} (h : x ∈ symTighter y) => by
      cases x <;> cases y <;> simp_all [symTighter, symRank])
    (measure symRank).wf

/-- The arithmetic grammar. `@[reducible]` so `arith.Op` unfolds to `Sym`. -/
@[reducible] def arith : Grammar where
  Op := Sym
  operator := symOp
  loosest := [.add]
  tighter := symTighter
  tighter_wf := symTighter_wf
  -- Any token that is not one of `arith`'s reserved name parts is a variable.
  isVar := fun t => decide (t ∉ ["n", "(", ")", "+", "*", "-", "!"])
  juxtUnique := fun o₁ o₂ h₁ h₂ => by cases o₁ <;> cases o₂ <;> simp_all [symOp]

/-! ## Running the parser

`parse` returns every full parse as an `Expr`; we map `Expr.flatten` over the
results so the output is `Repr`-able and we can eyeball the round-trip. -/

/-- All full-parse flattenings of an input under `arith`. -/
def run (tkns : List Token) : List (List Token) :=
  (parse (G := arith) tkns).map Expr.flatten

-- NOTE on multiplicities: `add → {mul, neg} → mul` is a *diamond*, so the
-- parser reaches `mul`-and-below both directly and through `neg`, finding the
-- same tree several times. All copies are equal (`Expr` stores the level
-- condition as an irrelevant `Prop`) — `parse` is a multiset of parses, and
-- uniqueness (`parse_unique`) is "all members equal", not `length ≤ 1`.

-- `n` → one tree, twice (diamond).
#eval run ["n"]                          -- [["n"], ["n"]]
-- `n + n` → one tree, 2×2 copies (diamond per operand).
#eval run ["n", "+", "n"]                -- 4 × ["n", "+", "n"]
-- `n + n * n` → one tree (mul binds tighter).
#eval run ["n", "+", "n", "*", "n"]      -- 4 × ["n", "+", "n", "*", "n"]
-- `( n + n )` → one tree.
#eval run ["(", "n", "+", "n", ")"]      -- 8 × ["(", "n", "+", "n", ")"]
-- `( n + n ) * n` → one tree.
#eval run ["(", "n", "+", "n", ")", "*", "n"]
-- malformed: dangling `+` → no full parse.
#eval run ["n", "+"]                     -- []
-- malformed: unmatched `(` → no full parse.
#eval run ["(", "n"]                     -- []

/-! ### Prefix operator `- _` -/

-- `- n` → one parse.
#eval run ["-", "n"]                     -- [["-", "n"]]
-- `- n + n` → one tree, grouping `(- n) + n` (neg ∈ tighter add).
#eval run ["-", "n", "+", "n"]           -- 2 × ["-", "n", "+", "n"]
-- `n + - n` → one tree.
#eval run ["n", "+", "-", "n"]           -- 2 × ["n", "+", "-", "n"]
-- `- n * n` → one parse, grouping `- (n * n)` (mul ∈ tighter neg, and neg is
-- no valid operand of mul).
#eval run ["-", "n", "*", "n"]           -- [["-", "n", "*", "n"]]
-- `- - n` → no parse: the operand hole is *strictly* tighter, so the
-- non-assoc prefix doesn't nest…
#eval run ["-", "-", "n"]                -- []
-- …without parentheses: `- ( - n )` → one parse.
#eval run ["-", "(", "-", "n", ")"]      -- [["-", "(", "-", "n", ")"]]

/-! ### Postfix operator `_ !` -/

-- `n !` → one tree.
#eval run ["n", "!"]                     -- 2 × ["n", "!"]
-- `n ! * n` → one tree, grouping `(n !) * n` (fac ∈ tighter mul).
#eval run ["n", "!", "*", "n"]           -- 2 × ["n", "!", "*", "n"]
-- `- n !` → one tree, grouping `- (n !)`.
#eval run ["-", "n", "!"]                -- [["-", "n", "!"]]
-- `n ! !` → no parse: non-assoc postfix doesn't nest…
#eval run ["n", "!", "!"]                -- []
-- …without parentheses: `( n ! ) !` → one tree.
#eval run ["(", "n", "!", ")", "!"]      -- 4 × ["(", "n", "!", ")", "!"]

/-! ### Variables

Any token that is not a reserved name part (`isVar`) parses as a leaf variable, at
any level — so identifiers mix freely with operators and literals. (A variable is a
valid atom at *every* level, so the all-parses parser surfaces it once per level it
descends through: each result list below is many equal copies of the one tree.) -/

-- `x` → the variable leaf, as one tree.
#eval run ["x"]
-- `x + y` → variables as the operands of `+`.
#eval run ["x", "+", "y"]
-- `x + n * y` → a variable, the literal `n`, and operators together (x + (n * y)).
#eval run ["x", "+", "n", "*", "y"]
-- `- x` and `( x + y ) !` → variables under prefix / postfix / parens.
#eval run ["-", "x"]
#eval run ["(", "x", "+", "y", ")", "!"]

/-! ### Juxtaposition (application)

Application binds tightest and associates left, so `f x y = (f x) y`, `f x + y =
(f x) + y`, and `f (g x)` needs the parentheses. -/

-- `f x` → one application.
#eval run ["f", "x"]
-- `f x y` → left-associated `(f x) y` (the only reading; the argument is an atom).
#eval run ["f", "x", "y"]
-- `f x + y` → `(f x) + y` (application tighter than `+`).
#eval run ["f", "x", "+", "y"]
-- `f (g x)` → application nested via parentheses.
#eval run ["f", "(", "g", "x", ")"]
-- `n x` → the literal `n` applied to variable `x` (both are atoms).
#eval run ["n", "x"]

end LambdaLab.Parser.Playground3
