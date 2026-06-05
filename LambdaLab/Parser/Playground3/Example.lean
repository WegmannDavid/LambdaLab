import LambdaLab.Parser.Playground3.Uniqueness

/-!
# A concrete precedence grammar for the Playground

A tiny arithmetic grammar exercising the new fixities and precedence DAG:

* `num`   — a nullary constant `n`           (closed, tightest)
* `paren` — `( _ )`                           (closed)
* `add`   — `_ + _`, left-associative        (loosest)
* `mul`   — `_ * _`, left-associative         (tighter than `add`)

Precedence chain (loosest → tightest): `add → mul → {paren, num}`. So
`a + b * c` groups as `a + (b * c)` and `a - b - c`-style chains nest left.

This file *type-checks* the design — constructing the `Grammar` (discharging
`tighter_wf` and `lookup_spec`) and building a few precedence-indexed trees —
and then exercises the parser: the `#eval` round-trips at the bottom confirm
well-formed inputs parse and re-flatten to themselves, and malformed inputs are
rejected.
-/

namespace LambdaLab.Parser.Playground3

open LambdaLab.Parser

/-- Operator names. -/
inductive Sym where
  | num | paren | add | mul
deriving DecidableEq, Repr

/-- Each operator's shape (fixity + name-parts). -/
def symOp : Sym → Operator
  | .num   => .const "n"
  | .paren => { fixity := .closed,      nameParts := ["(", ")"], nameParts_ne := by simp }
  | .add   => { fixity := .infix .left, nameParts := ["+"],      nameParts_ne := by simp }
  | .mul   => { fixity := .infix .left, nameParts := ["*"],      nameParts_ne := by simp }

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

/-- Resolve a leading token to its operator. -/
def symLookup : Token → Option Sym
  | "n" => some .num
  | "(" => some .paren
  | "+" => some .add
  | "*" => some .mul
  | _   => none

/-- The arithmetic grammar. Marked `@[reducible]` so `arith.Op` unfolds to
`Sym` during unification and instance search — without it, `.op`/`.mk` can't
infer `G` and `decide` can't find `DecidableEq arith.Op`. -/
@[reducible] def arith : Grammar where
  Op := Sym
  operator := symOp
  loosest := [.add]
  tighter := symTighter
  tighter_wf := symTighter_wf
  lookup := symLookup
  lookup_spec := by
    intro o tkn
    cases o <;>
      (simp only [symOp, Operator.head, Operator.const, List.head_cons]
       constructor
       · rintro rfl; rfl
       · intro h; simp only [symLookup] at h; split at h <;> simp_all)

/-! ## Example trees

Because operands at a loose node embed tighter ones by explicit `next` steps,
atoms must be "lifted" up the precedence chain. A few helpers make that bearable. -/

/-- The bare constant `n`, at its own (tight) node. (We pin `G := arith` on
`.op`: its children argument's type mentions `(G.operator a).fixity`, which
stays stuck while `G` is a metavar, so the expected type alone doesn't fix it.) -/
def tNum : Tree arith Sym.num := Tree.op (G := arith) Sym.num (.closed (.last "n"))

/-- `n` lifted to the `mul` level. -/
def tNumMul : Tree arith Sym.mul := .next (.mk Sym.num (by decide) tNum)

/-- `n` lifted to the `add` level. -/
def tNumAdd : Tree arith Sym.add := .next (.mk Sym.mul (by decide) tNumMul)

/-- `n` as something strictly tighter than `add`. -/
def bNumAdd : TreeBelow arith Sym.add := .mk Sym.mul (by decide) tNumMul

/-- `n + n` — head operand strictly tighter, then one `(+ , operand)` spine step. -/
def tAdd : Tree arith Sym.add :=
  Tree.op (G := arith) Sym.add (.infixL bNumAdd (.last (.last "+") bNumAdd))

/-- `( n )` — the interior hole is a top-level expression (here, `n` at `add`). -/
def tParen : Tree arith Sym.paren :=
  Tree.op (G := arith) Sym.paren (.closed (.cons "(" (.mk Sym.add (by decide) tNumAdd) (.last ")")))

#guard tNum.flatten == ["n"]
#guard tAdd.flatten == ["n", "+", "n"]
#guard tParen.flatten == ["(", "n", ")"]

/-! ## Parsing

`parse` returns the list of full parses; each is mapped through `flatten`. Since
`arith` is unambiguous (total-order DAG), every accepted input prints as a
singleton `[<the input tokens>]`, and rejected input prints `[]`. -/

-- [["n"]]
#eval (parse (G := arith) ["n"]).map (·.flatten)
-- [["n", "+", "n"]]
#eval (parse (G := arith) ["n", "+", "n"]).map (·.flatten)
-- [["(", "n", ")"]]
#eval (parse (G := arith) ["(", "n", ")"]).map (·.flatten)
-- [["n", "+", "n", "*", "n"]]   (mul binds tighter)
#eval (parse (G := arith) ["n", "+", "n", "*", "n"]).map (·.flatten)
-- [["n", "*", "n", "+", "n"]]
#eval (parse (G := arith) ["n", "*", "n", "+", "n"]).map (·.flatten)
-- [["n", "+", "n", "+", "n"]]   (left-assoc chain)
#eval (parse (G := arith) ["n", "+", "n", "+", "n"]).map (·.flatten)
-- [["(", "n", "+", "n", ")", "*", "n"]]
#eval (parse (G := arith) ["(", "n", "+", "n", ")", "*", "n"]).map (·.flatten)
-- []   (malformed: missing closing paren)
#eval (parse (G := arith) ["(", "n"]).map (·.flatten)
-- []   (trailing junk)
#eval (parse (G := arith) ["n", "n"]).map (·.flatten)

/-! ## A grammar exercising prefix / postfix / infixR / infixN

A linear precedence chain (loosest → tightest): `= → ^ → - → ! → x`, with one
operator of each remaining fixity. Round-trips below confirm the parser handles
all four; the non-associative `=` correctly *rejects* `x = x = x`. -/

inductive MSym where
  | atom | fact | neg | pow | eq
deriving DecidableEq, Repr

def mixOp : MSym → Operator
  | .atom => .const "x"
  | .fact => { fixity := .postfix,         nameParts := ["!"], nameParts_ne := by simp }
  | .neg  => { fixity := .prefix,          nameParts := ["-"], nameParts_ne := by simp }
  | .pow  => { fixity := .infix .right,    nameParts := ["^"], nameParts_ne := by simp }
  | .eq   => { fixity := .infix .nonAssoc, nameParts := ["="], nameParts_ne := by simp }

/-- `= → ^ → - → ! → x` (loosest → tightest). -/
def mixTighter : MSym → List MSym
  | .atom => []
  | .fact => [.atom]
  | .neg  => [.fact]
  | .pow  => [.neg]
  | .eq   => [.pow]

def mixRank : MSym → Nat
  | .atom => 0 | .fact => 1 | .neg => 2 | .pow => 3 | .eq => 4

theorem mixTighter_wf : WellFounded (fun b a => b ∈ mixTighter a) :=
  Subrelation.wf
    (r := fun x y => mixRank x < mixRank y)
    (fun {x y} (h : x ∈ mixTighter y) => by
      cases x <;> cases y <;> simp_all [mixTighter, mixRank])
    (measure mixRank).wf

def mixLookup : Token → Option MSym
  | "x" => some .atom
  | "!" => some .fact
  | "-" => some .neg
  | "^" => some .pow
  | "=" => some .eq
  | _   => none

@[reducible] def mix : Grammar where
  Op := MSym
  operator := mixOp
  loosest := [.eq]
  tighter := mixTighter
  tighter_wf := mixTighter_wf
  lookup := mixLookup
  lookup_spec := by
    intro o tkn
    cases o <;>
      (simp only [mixOp, Operator.head, Operator.const, List.head_cons]
       constructor
       · rintro rfl; rfl
       · intro h; simp only [mixLookup] at h; split at h <;> simp_all)

-- [["-", "x"]]                 (prefix)
#eval (parse (G := mix) ["-", "x"]).map (·.flatten)
-- [["-", "-", "x"]]            (prefix stacks)
#eval (parse (G := mix) ["-", "-", "x"]).map (·.flatten)
-- [["x", "!"]]                 (postfix)
#eval (parse (G := mix) ["x", "!"]).map (·.flatten)
-- [["x", "!", "!"]]            (postfix stacks)
#eval (parse (G := mix) ["x", "!", "!"]).map (·.flatten)
-- [["x", "^", "x", "^", "x"]]  (right-assoc; type forces `x ^ (x ^ x)`)
#eval (parse (G := mix) ["x", "^", "x", "^", "x"]).map (·.flatten)
-- [["x", "=", "x"]]            (non-assoc, single use OK)
#eval (parse (G := mix) ["x", "=", "x"]).map (·.flatten)
-- []                            (non-assoc rejects chaining `x = x = x`)
#eval (parse (G := mix) ["x", "=", "x", "=", "x"]).map (·.flatten)
-- [["-", "x", "!"]]            (`-(x!)`: `!` binds tighter than `-`)
#eval (parse (G := mix) ["-", "x", "!"]).map (·.flatten)

/-! ## Unambiguity of the concrete grammars

Both grammars satisfy the syntactic criterion `Unambiguous`, hence (modulo the
open `unambiguous_flatten_injective`) `flatten` is injective and `parse` is
subsingleton on them. -/

theorem arith_unambiguous : Unambiguous arith where
  nameParts_nodup := by intro a; cases a <;> decide
  nameParts_disjoint := by
    intro a b hne tk htk
    cases a <;> cases b <;>
      simp_all [arith, symOp, Operator.const] <;>
      rcases htk with rfl | rfl <;> simp_all
  tighter_disjoint := by
    intro a b₁ b₂ h₁ h₂ hne c hc₁ hc₂
    cases a <;> simp_all [arith, symTighter]
    -- only `mul` survives: tighter mul = [paren, num]
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
      subst h₁ <;> subst h₂ <;>
      first
        | exact absurd rfl hne
        | · have e₁ := TighterEq.eq_of_sink (G := arith) rfl hc₁
            have e₂ := TighterEq.eq_of_sink (G := arith) rfl hc₂
            simp_all
  loosest_disjoint := by
    intro r₁ r₂ h₁ h₂ hne c hc₁ hc₂
    simp_all [arith]

theorem mix_unambiguous : Unambiguous mix where
  nameParts_nodup := by intro a; cases a <;> decide
  nameParts_disjoint := by
    intro a b hne tk htk
    cases a <;> cases b <;> simp_all [mix, mixOp, Operator.const]
  tighter_disjoint := by
    intro a b₁ b₂ h₁ h₂ hne c hc₁ hc₂
    cases a <;> simp_all [mix, mixTighter]
  loosest_disjoint := by
    intro r₁ r₂ h₁ h₂ hne c hc₁ hc₂
    simp_all [mix]

/-- `arith`'s `flatten` is injective (modulo the open criterion). -/
theorem arith_flatten_injective : FlattenInjective arith :=
  unambiguous_flatten_injective arith_unambiguous

/-- `mix`'s `flatten` is injective (modulo the open criterion). -/
theorem mix_flatten_injective : FlattenInjective mix :=
  unambiguous_flatten_injective mix_unambiguous

/-- `parse` on `arith` returns at most one result. -/
theorem arith_parse_unique {tkns : List Token} {e₁ e₂ : Expr arith}
    (h₁ : e₁ ∈ parse (G := arith) tkns) (h₂ : e₂ ∈ parse (G := arith) tkns) : e₁ = e₂ :=
  parse_unique arith_flatten_injective h₁ h₂

/-- `parse` on `mix` returns at most one result. -/
theorem mix_parse_unique {tkns : List Token} {e₁ e₂ : Expr mix}
    (h₁ : e₁ ∈ parse (G := mix) tkns) (h₂ : e₂ ∈ parse (G := mix) tkns) : e₁ = e₂ :=
  parse_unique mix_flatten_injective h₁ h₂

end LambdaLab.Parser.Playground3
