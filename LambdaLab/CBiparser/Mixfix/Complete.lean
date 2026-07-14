import LambdaLab.CBiparser.Mixfix.Sound
import LambdaLab.CBiparser.Mixfix.Biparser

/-!
# Parser completeness: printing a tree and parsing it back recovers the tree

This is the second half of the round-trip, and the hard one:

    parseExpr e l (t.flatten ++ rest) = some (t, rest)      when  HeadIn (follow e) rest

Note the induction is on the **tree**, not on the parser — the opposite direction from
`Sound.lean`. Soundness says *whatever the parser returns flattens back*; completeness says
*the parser returns the tree you printed*. Neither implies the other. (Soundness plus injective
`flatten` would give it, but `flatten` is injective only for an *unambiguous* grammar, and we
deliberately require only lexical `headsDistinct`, not full DAG-unambiguity. So the tree must be
recovered *directly*, by showing the parser's dispatch is forced at every node.)

Three things force it:

* **`headsDistinct`** — a leading token selects at most one operator, so operator dispatch is
  forced by the token stream.
* **`varDisjoint`** — no operator name-part is a variable token, so a leaf can't be mistaken for
  (part of) an operator.
* **the FOLLOW condition** — this is what stops the *greedy* folds (`parseJuxt`,
  `parseInfixL`) exactly where the printed tree ended, rather than eating into `rest`.
-/

namespace LambdaLab.CBiparser.Mixfix

open LambdaLab.CBiparser

variable {G : Grammar}

/-- The parser at the erased level — no `RightSublist` in any statement. -/
def runExpr (e : G.Ent) (l : Level (G.entry e)) (input : List (Token G.isSep)) :
    Option (Expr G e l × List (Token G.isSep)) :=
  (parseExpr e l input).map (fun x => (x.1, x.2.list))

def runParts (shape : List (Part G)) (input : List (Token G.isSep)) :
    Option (Parts G shape × List (Token G.isSep)) :=
  (parseParts shape input).map (fun x => (x.1, x.2.list))

/-! ## A printed tree is never empty

Needed everywhere: the leftover after parsing `t.flatten ++ rest` must be a *strict* suffix, so
`t.flatten` has to be non-empty. It is, and the reason is structural — a variable prints one
token, and every operator body contains either a name part or a hole (which prints non-empty by
induction). -/

/-- A notation always has at least one name token. -/
theorem Notation.toParts_ne_nil (n : Notation G.isSep G.Ent) :
    Notation.toParts n ≠ [] := by
  cases n <;> simp [Notation.toParts]

/-- Every operator body has at least one part — a name token, or a hole. -/
theorem Operator.body_ne_nil {e : G.Ent} (o : (G.entry e).Op) :
    Operator.body e o ≠ [] := by
  unfold Operator.body
  cases (G.entry e).operator o <;>
    simp [Notation.toParts_ne_nil]

mutual
  theorem Expr.flatten_ne_nil {e : G.Ent} {l : Level (G.entry e)} :
      ∀ (t : Expr G e l), t.flatten ≠ []
    | .var _ _ => by simp [Expr.flatten]
    | .op o _ ps => by
        simp only [Expr.flatten]
        exact Parts.flatten_ne_nil ps (Operator.body_ne_nil o)

  theorem Parts.flatten_ne_nil {shape : List (Part G)} :
      ∀ (ps : Parts G shape), shape ≠ [] → ps.flatten ≠ []
    | .nil, h => absurd rfl h
    | .namePart _ _, _ => by simp [Parts.flatten]
    | .hole ex _, _ => by
        simp only [Parts.flatten]
        intro hcon
        exact Expr.flatten_ne_nil ex (List.append_eq_nil_iff.mp hcon).1
end

/-! ## The main theorem — the shape of the induction

`Expr` and `Parts` are mutually inductive, so completeness is a mutual theorem. The `Parts`
statement carries its own FOLLOW obligation (what may follow the *rest* of the body).

**Where the difficulty concentrates**: the two greedy folds. For a left-nested juxtaposition
`(f x) y`, `flatten = f.flatten ++ x.flatten ++ y.flatten`, and `parseJuxt` must consume all
three and then *stop* — which is precisely what `HeadIn (follow e) rest` buys. Proving the fold
stops in the right place needs an auxiliary induction on the *spine* of the tree, not just its
subterms. -/

theorem parseExpr_complete {e : G.Ent} {l : Level (G.entry e)} (t : Expr G e l)
    (rest : List (Token G.isSep)) (hF : HeadIn (follow e) rest) :
    runExpr e l (t.flatten ++ rest) = some (t, rest) := by
  sorry

/-- **The round-trip law** for the mixfix biparser. -/
theorem mixfix_ok' (e : G.Ent) (l : Level (G.entry e)) :
    RoundTrips (biparser G e l) (HeadIn (follow e)) := by
  intro t rest hF
  have h := parseExpr_complete t rest hF
  simp only [runExpr] at h
  simpa [biparser, CBiparser.run, parseCB, Option.map_map] using h

end LambdaLab.CBiparser.Mixfix
