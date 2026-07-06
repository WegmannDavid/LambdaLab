import LambdaLab.ParserOld.Mixfix.Parse

/-!
# A concrete grammar exercising the multi-entry parser

A tiny arithmetic grammar as a two-`Entry` family: a `term` entry with the full
operator model (`closed`/`prefx`/`infx`/`postfx`/`infxl`/`infxr`/`juxt`), and a
`var` entry (no operators) used as the binder language of `lam` — referenced as
an ordinary cross-entry hole `\lambda ‹var› . _`.

Precedence (in `term`): `add → {mul, neg}`, `neg → mul`, `mul → pow`, `pow → fac`,
`fac → app`, `app → {paren, num}`; `lam` is loosest. The `#eval`s run the parser
at the `term` entry and re-flatten each parse.
-/

namespace LambdaLab.ParserOld.Mixfix

open LambdaLab.ParserOld

/-- The two classes of expressions: ordinary terms, and the binder sub-language. -/
inductive Ent where | term | var
  deriving DecidableEq, Repr

/-- Operator names of the `term` entry. -/
inductive Sym where
  | num | paren | add | mul | pow | neg | fac | app | lam
  deriving DecidableEq, Repr

def reserved : List Token := ["n", "(", ")", "+", "*", "-", "!", "^", "\\lambda", "."]

/-- Immediately-tighter successors within `term`. -/
def symTighter : Sym → List Sym
  | .num   => []
  | .paren => []
  | .add   => [.mul, .neg]
  | .neg   => [.mul]
  | .mul   => [.pow]
  | .pow   => [.fac]
  | .fac   => [.app]
  | .app   => [.paren, .num]
  | .lam   => [.add]

def symRank : Sym → Nat
  | .num => 0 | .paren => 0 | .app => 1 | .fac => 2 | .pow => 3
  | .mul => 4 | .neg => 5 | .add => 6 | .lam => 7

theorem symTighter_wf : WellFounded (fun b a => b ∈ symTighter a) :=
  Subrelation.wf
    (r := fun x y => symRank x < symRank y)
    (fun {x y} (h : x ∈ symTighter y) => by
      cases x <;> cases y <;> simp_all [symTighter, symRank])
    (measure symRank).wf

/-- Each `term` operator's shape. `paren`'s interior hole recurses into `term`;
`lam`'s binder hole references the `var` entry. -/
def symOp : Sym → Operator Ent
  | .num   => .closed (.last "n")
  | .paren => .closed (.cons "(" .term (.last ")"))
  | .add   => .infxl (.last "+")
  | .mul   => .infx (.last "*")
  | .pow   => .infxr (.last "^")
  | .neg   => .prefx (.last "-")
  | .fac   => .postfx (.last "!")
  | .app   => .juxt
  | .lam   => .prefx (.cons "\\lambda" .var (.last "."))

/-- The `term` entry. -/
def termEntry : Entry Ent where
  Op := Sym
  operator := symOp
  loosest := [.add, .lam]
  tighter := symTighter
  tighter_wf := symTighter_wf
  isVar := fun t => decide (t ∉ reserved)
  juxtUnique := fun o₁ o₂ h₁ h₂ => by cases o₁ <;> cases o₂ <;> simp_all [symOp]

/-- The `var` entry: no operators, only identifiers. -/
def varEntry : Entry Ent where
  Op := Empty
  operator := fun e => e.elim
  loosest := []
  tighter := fun e => e.elim
  tighter_wf := ⟨fun e => e.elim⟩
  isVar := fun t => decide (t ∉ reserved)
  juxtUnique := fun e => e.elim

/-- The arithmetic grammar, as a family of the two entries. -/
def arith : Grammar where
  Ent := Ent
  entry := fun | .term => termEntry | .var => varEntry

/-! ## Running the parser -/

/-- All full-parse flattenings of an input, parsed at the `term` entry. -/
def run (tkns : List Token) : List (List Token) :=
  (parse (G := arith) .term tkns).map Expr.flatten

#eval run ["n"]                          -- 2 × ["n"]
#eval run ["n", "+", "n"]                -- ["n", "+", "n"]
#eval run ["n", "+", "n", "*", "n"]
#eval run ["(", "n", "+", "n", ")"]
#eval run ["n", "+"]                     -- []
#eval run ["-", "n"]
#eval run ["-", "n", "*", "n"]           -- - (n * n)
#eval run ["n", "!"]
#eval run ["n", "!", "*", "n"]           -- (n !) * n
#eval run ["x"]                          -- a variable leaf
#eval run ["f", "x", "y"]                -- application f x y
#eval run ["\\lambda", "x", ".", "x"]    -- binder parsed by the `var` entry
#eval run ["(", "\\lambda", "x", ".", "x", ")", "y"]

end LambdaLab.ParserOld.Mixfix
