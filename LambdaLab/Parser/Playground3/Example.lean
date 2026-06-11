import LambdaLab.Parser.Playground3.Parse

/-!
# A concrete grammar exercising the `Part`/`Parts` parser

A tiny arithmetic grammar over the new (`closed` / `infx`) operator model:

* `num`   — the constant `n`        (closed, tightest)
* `paren` — `( _ )`                  (closed)
* `add`   — `_ + _`                  (loosest)
* `mul`   — `_ * _`                  (tighter than `add`)

Precedence chain (loosest → tightest): `add → mul → {paren, num}`, so
`n + n * n` groups as `n + (n * n)`. The `#eval`s at the bottom run the
`partial` parser and re-flatten each parse — well-formed inputs round-trip to
themselves, malformed inputs yield no full parse.
-/

namespace LambdaLab.Parser.Playground3

open LambdaLab.Parser

/-- Operator names. -/
inductive Sym where
  | num | paren | add | mul
deriving DecidableEq, Repr

/-- Each operator's shape. -/
def symOp : Sym → Operator
  | .num   => .closed (.last "n")
  | .paren => .closed (.cons "(" (.last ")"))
  | .add   => .infx (.last "+")
  | .mul   => .infx (.last "*")

/-- Immediately-tighter successors: `add → mul → {paren, num}`. -/
def symTighter : Sym → List Sym
  | .num   => []
  | .paren => []
  | .add   => [.mul]
  | .mul   => [.paren, .num]

/-- A rank witnessing acyclicity: higher = looser. -/
def symRank : Sym → Nat
  | .num => 0 | .paren => 0 | .mul => 1 | .add => 2

/-- `tighter` is well-founded: each step strictly drops the rank. -/
theorem symTighter_wf : WellFounded (fun b a => b ∈ symTighter a) :=
  Subrelation.wf
    (r := fun x y => symRank x < symRank y)
    (fun {x y} (h : x ∈ symTighter y) => by
      cases x <;> cases y <;> simp_all [symTighter, symRank])
    (measure symRank).wf

/-- Resolve a leading token to its operator (unused by the parser, which keys on
name-parts directly; provided to populate the `Grammar`). -/
def symLookup : Token → Option Sym
  | "n" => some .num
  | "(" => some .paren
  | "+" => some .add
  | "*" => some .mul
  | _   => none

/-- The arithmetic grammar. `@[reducible]` so `arith.Op` unfolds to `Sym`. -/
@[reducible] def arith : Grammar where
  Op := Sym
  operator := symOp
  loosest := [.add]
  tighter := symTighter
  tighter_wf := symTighter_wf
  lookup := symLookup

/-! ## Running the parser

`parse` returns every full parse as an `Expr`; we map `Expr.flatten` over the
results so the output is `Repr`-able and we can eyeball the round-trip. -/

/-- All full-parse flattenings of an input under `arith`. -/
def run (tkns : List Token) : List (List Token) :=
  (parse (G := arith) tkns).map Expr.flatten

-- `n` → one parse, round-trips.
#eval run ["n"]                          -- [["n"]]
-- `n + n` → one parse.
#eval run ["n", "+", "n"]                -- [["n", "+", "n"]]
-- `n + n * n` → one parse (mul binds tighter).
#eval run ["n", "+", "n", "*", "n"]      -- [["n", "+", "n", "*", "n"]]
-- `( n + n )` → one parse.
#eval run ["(", "n", "+", "n", ")"]      -- [["(", "n", "+", "n", ")"]]
-- `( n + n ) * n` → one parse.
#eval run ["(", "n", "+", "n", ")", "*", "n"]
-- malformed: dangling `+` → no full parse.
#eval run ["n", "+"]                     -- []
-- malformed: unmatched `(` → no full parse.
#eval run ["(", "n"]                     -- []

end LambdaLab.Parser.Playground3
