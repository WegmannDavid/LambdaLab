import LambdaLab.IsoParser.Mixfix.Sound

/-!
# The general mixfix `IsoParser`

Packages the self-contained mixfix parser as an `IsoParser` over the abstract token alphabet — the
independent counterpart of `IsoParser/Mixfix.lean` (which reuses `CBiparser`).

* **FIRST = ⊤** (`anyTok`). `firstOk` is a purely negative claim, so the weakest FIRST makes it
  vacuous.
* **FOLLOW** carries the content: the tokens at which the greedy parser provably stops — neither an
  operand-starter nor an expression-continuer.
* **`print`** is `flatten`; **`print_parse`** (exactness) lands on `parseExpr_sound`.
* **`parse_print`** (the round-trip) is the greedy left-associative reconstruction — the genuinely
  hard direction (the analogue of `CBiparser`'s open `parseExpr_exact`), left as a `sorry` here.
-/

namespace LambdaLab.IsoParser.Mixfix

open LambdaLab.IsoParser

variable {Tok : Type} [DecidableEq Tok] {G : Grammar Tok}

/-! ## FIRST — vacuous, hence free -/

/-- The weakest FIRST: everything. -/
abbrev anyTok : Tok → Bool := fun _ => true

/-! ## FOLLOW — the tokens at which the parser provably stops -/

/-- Can this token **start an operand** of entry `e`? A variable can, as can the leading token of an
operator that does not begin with a hole (`closed`/`prefx`) — `(` starts a parenthesised operand. -/
def startsOperand (e : G.Ent) (t : Tok) : Bool :=
  (G.entry e).isVar t ||
    (G.entry e).ops.any (fun o =>
      let op := (G.entry e).operator o
      !op.startsWithHole &&
        (match op.headTok? with
         | some h => decide (h = t)
         | none   => false))

/-- Can this token **continue** an expression of entry `e`? Exactly the leading token of an operator
that begins with a hole (`infx`/`infxl`/`infxr`/`postfx`) — it arrives after the left operand. -/
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

/-- **The general mixfix parser as an `IsoParser`.** Trivial annotation (the tree pins its token
string); `print = flatten`; exactness from `parseExpr_sound`. -/
def mixfix (e : G.Ent) (l : Level (G.entry e)) :
    IsoParser Tok anyTok (follow e) (Expr G e l) (fun _ => PUnit) where
  parse input := (parseExpr e l input).map (fun z => (⟨z.1, PUnit.unit⟩, ⟨z.2.list, z.2.lt⟩))
  print t _ := t.flatten
  firstOk c rest h := by simp [anyTok] at h
  print_parse input xa r h := by
    rcases hpe : parseExpr e l input with _ | ⟨t, s⟩
    · rw [hpe] at h; simp at h
    · rw [hpe] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hr⟩ := h
      have hrv : r.val = s.list := congrArg Subtype.val hr.symm
      show t.flatten ++ r.val = input
      rw [hrv]
      exact parseExpr_sound e l input t s hpe
  parse_print := by
    -- The greedy left-associative reconstruction — CBiparser's open `parseExpr_exact` analogue.
    sorry

end LambdaLab.IsoParser.Mixfix
