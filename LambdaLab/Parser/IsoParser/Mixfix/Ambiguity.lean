import LambdaLab.Parser.IsoParser.Mixfix.Sound

/-!
# Why the round-trip law needs an unambiguity hypothesis — a machine-checked counterexample

The `Grammar` of `Basic.lean` is deliberately lightweight: operators, an explicit precedence
`rank`, and a variable recognizer. Nothing in it forbids **two operators with the same
notation**. This file exhibits such a grammar and proves that the round-trip law

    parse (t.flatten ++ rest) = some (t, rest)

**fails** for it — so the law is not merely unproved without an unambiguity hypothesis, it is
*false*, and no proof effort can remove that hypothesis.

The argument is the general one, and applies to **any** deterministic parser: if `t₁ ≠ t₂` have
`t₁.flatten = t₂.flatten`, a deterministic parser returns one of them, and the other cannot
round-trip. Here `ambigA` and `ambigB` are two distinct trees for `a + b` (they differ in which
operator sits on top), the parser returns the `A` one, and so the law fails at `ambigB`.

This is why `Complete.lean` takes `Unambiguous G` as a hypothesis, and why `mixfix` does too.
Whether `Unambiguous` is *derivable* from finitely-checkable lexical conditions is a separate
question (empirically yes; see the project notes on `UniqueNameParts` / Danielsson–Norell §4).

Nothing here depends on the open `parseExpr_exact`: this file imports only `Sound.lean`, so its
theorems are sorry-free.
-/

namespace LambdaLab.Parser.IsoParser.Mixfix.Ambiguity

open LambdaLab.Parser.IsoParser.Mixfix

/-- Two operator *names* with identical notation. -/
inductive Sym | A | B
  deriving DecidableEq, Repr

/-- One entry, whose two operators are both `_ + _`, left-associative, both loosest. -/
def ambigEntry : Entry String Unit where
  Op := Sym
  operator | .A => .infxl (.last "+") | .B => .infxl (.last "+")
  ops := [.A, .B]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.A, .B]
  tighter | .A => [] | .B => []
  rank | .A => 0 | .B => 0
  topRank := 1
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := fun t => t == "a" || t == "b"

def ambigG : Grammar String where
  Ent := Unit
  entry := fun _ => ambigEntry

instance : DecidableEq (ambigG.entry ()).Op := inferInstanceAs (DecidableEq Sym)
instance : Repr (ambigG.entry ()).Op := inferInstanceAs (Repr Sym)

/-- `a + b` with `A` on top. -/
def ambigA : Expr ambigG () .loosest :=
  .op Sym.A ⟨Sym.A, List.Mem.head _, .refl⟩
    (.hole (.var "a" (by decide)) (.namePart "+" (.hole (.var "b" (by decide)) .nil)))

/-- `a + b` with `B` on top — a *different* tree. -/
def ambigB : Expr ambigG () .loosest :=
  .op Sym.B ⟨Sym.B, List.Mem.tail _ (List.Mem.head _), .refl⟩
    (.hole (.var "a" (by decide)) (.namePart "+" (.hole (.var "b" (by decide)) .nil)))

/-- The grammar is ambiguous: two distinct trees, one flattening. -/
theorem flatten_eq : ambigA.flatten = ambigB.flatten := rfl

/-- The top operator of a tree — enough to tell `ambigA` and `ambigB` apart. -/
def topOp : Expr ambigG () .loosest → Option Sym
  | .op o _ _ => some o
  | .var _ _  => none

theorem topOp_A : topOp ambigA = some Sym.A := rfl
theorem topOp_B : topOp ambigB = some Sym.B := rfl

/-- **The round-trip law is false for this grammar.**

No evaluation of the parser is needed: if the law held at *both* trees, then — since they have
the *same* flattening — the parser's single answer would have to equal both, forcing
`ambigA = ambigB`, which their top operators refute. This is the general argument that no
deterministic parser can escape. -/
theorem law_not_universal :
    ¬ (∀ (t : Expr ambigG () .loosest) (rest : List String),
        (parseExpr (G := ambigG) () .loosest (t.flatten ++ rest)).map (fun z => (z.1, z.2.list))
          = some (t, rest)) := by
  intro h
  have hA := h ambigA []
  have hB := h ambigB []
  rw [flatten_eq, hB] at hA
  simp only [Option.some.injEq, Prod.mk.injEq] at hA
  have htop : topOp ambigA = topOp ambigB := by rw [hA.1]
  rw [topOp_A, topOp_B] at htop
  exact absurd htop (by decide)

/-- For the record, which of the two the parser actually returns (ties keep the earlier
candidate, so: `A`). Not used in the proof above. -/
example : True := trivial
-- #eval (parseExpr (G := ambigG) () .loosest ["a", "+", "b"]).map (fun z => topOp z.1)

end LambdaLab.Parser.IsoParser.Mixfix.Ambiguity
