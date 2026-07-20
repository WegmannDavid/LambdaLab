import LambdaLab.IsoParser.Mixfix.Sound
import LambdaLab.IsoParser.Basic

/-!
# The general mixfix `IsoParser`

Packages the self-contained mixfix parser as an `IsoParser` over the abstract token alphabet —
the independent counterpart of `IsoParser/Mixfix.lean` (which reuses `CBiparser`). **Aligned**:
source = value = the tree, `print` is `flatten`.

* **FIRST = ⊤** (`firstOk` vacuous).
* **FOLLOW** carries the content: the computed `follow` — tokens at which the greedy parser
  provably stops (neither an operand-starter nor an expression-continuer).
* **`ok`** (the round-trip) is the greedy left-associative reconstruction — the genuinely hard
  direction (the analogue of `CBiparser`'s open `parseExpr_exact`), left as a `sorry` here.
* The **exactness** direction is *proved* (`parseExpr_sound`, sorry-free) but has no field in the
  split model; it remains available standalone in `Sound.lean`.
-/

namespace LambdaLab.IsoParser.Mixfix

open LambdaLab.IsoParser

variable {Tok : Type} [DecidableEq Tok] {G : Grammar Tok}

/-! ## FOLLOW — the tokens at which the parser provably stops -/

/-- Can this token **start an operand** of entry `e`? A variable can, as can the leading token of
an operator that does not begin with a hole (`closed`/`prefx`). -/
def startsOperand (e : G.Ent) (t : Tok) : Bool :=
  (G.entry e).isVar t ||
    (G.entry e).ops.any (fun o =>
      let op := (G.entry e).operator o
      !op.startsWithHole &&
        (match op.headTok? with
         | some h => decide (h = t)
         | none   => false))

/-- Can this token **continue** an expression of entry `e`? Exactly the leading token of an
operator that begins with a hole (`infx`/`infxl`/`infxr`/`postfx`). -/
def continuesExpr (e : G.Ent) (t : Tok) : Bool :=
  (G.entry e).ops.any (fun o =>
    let op := (G.entry e).operator o
    op.startsWithHole &&
      (match op.headTok? with
       | some h => decide (h = t)
       | none   => false))

/-- **FOLLOW**: a token stops the parser iff it can neither start an operand nor continue one. -/
def follow (e : G.Ent) : Tok → Bool :=
  fun t => !startsOperand e t && !continuesExpr e t

/-! ## The `IsoParser` -/

/-- **The general mixfix parser as an `IsoParser`.** Aligned; `print = flatten`. -/
def mixfix (e : G.Ent) (l : Level (G.entry e)) :
    IsoParser Tok (fun _ => True) (fun t => follow e t = true)
      (Expr G e l) (Expr G e l) where
  parse input := (parseExpr e l input).map (fun z => (z.1, ⟨z.2.list, z.2.lt⟩))
  print t := (t, t.flatten)
  firstOk c rest hc := absurd trivial hc
  ok := by
    -- The greedy left-associative reconstruction — CBiparser's open `parseExpr_exact` analogue.
    sorry

end LambdaLab.IsoParser.Mixfix
