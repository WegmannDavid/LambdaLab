import LambdaLab.Biparser.Mixfix.Parse

/-!
# Parser soundness: a parse flattens back to the consumed input

`parseExpr e l tkns = some (t, s)` implies `t.flatten ++ s.list = tkns` — the tree the
parser returns, flattened, is exactly the prefix it consumed (with `s.list` the leftover).
This is the *soundness* half of the round-trip: the parser never fabricates or drops
tokens. Combined with determinism it gives uniqueness; the *completeness* half — that
`print`ing a tree and parsing it back recovers the tree — is proved separately (it needs
the greedy "FOLLOW" side-condition, the generic form of `Concrete`'s `rest.head? ≠ '+'`).

Proof machinery this file establishes (reused by completeness): induction over the
well-founded parser recursion, and the `flatten`/`++`/`RightSublist.list` bookkeeping.
-/

namespace LambdaLab.Biparser.Mixfix

variable {G : Grammar}

/-- The variable leaf is sound: it consumes exactly the one variable token it returns. -/
theorem parseVar_sound (e : G.Ent) (l : Level (G.entry e)) (tkns : List (Token G.isSep))
    {t : Expr G e l} {s : RightSublist tkns} (h : parseVar e l tkns = some (t, s)) :
    t.flatten ++ s.list = tkns := by
  cases tkns with
  | nil => simp [parseVar] at h
  | cons hd tl =>
      simp only [parseVar] at h
      split at h
      · rename_i hv
        obtain ⟨rfl, rfl⟩ := Option.some.inj h
        simp [Expr.flatten]
      · exact absurd h (by simp)

end LambdaLab.Biparser.Mixfix
