import LambdaLab.CBiparser.Mixfix.Sound
import LambdaLab.CBiparser.Mixfix.Biparser
import LambdaLab.CBiparser.Mixfix.Unambiguity

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

/-! ## Unambiguity — and why it is unavoidable

Completeness-as-equality requires `flatten` to be **injective**, and this is forced for *any*
deterministic parser, not just ours: if `t₁ ≠ t₂` flatten alike, a deterministic parser returns
one of them, and the other cannot possibly round-trip. `headsDistinct` does **not** supply it
(this repo has a machine-checked counterexample to that implication). So it is a hypothesis. -/

/-- Distinct trees at a level print distinctly. -/

/-! ## The decomposition

Everything hard is concentrated in **one** lemma, and — importantly — that lemma does **not**
mention unambiguity:

    parseExpr_exact :  the parser succeeds on `t.flatten ++ rest` and consumes EXACTLY
                       `t.flatten`, i.e. its leftover is exactly `rest`.

Given that, completeness is three lines: soundness turns "leftover = rest" into
`t'.flatten = t.flatten`, and unambiguity turns that into `t' = t`.

`parseExpr_exact` is where the FOLLOW condition earns its keep — it is what stops the greedy
folds from eating into `rest` — and where longest-match earns its keep: the candidate that
really uses its operator consumes more than one that falls through, so the parser cannot stop
short. -/

/-! ### Roadmap for `parseExpr_exact` — two things it needs that we do not yet have

Both were found by probing the actual parser, and both change the *shape* of the proof.

**(1) FOLLOW must be per-LEVEL, not per-entry.**

In `f x` (juxtaposition), the left hole is followed directly by the right hole, whose flatten
begins with `x` — a *variable*, i.e. an operand-starter, i.e. **not** in `follow e`:

    #eval follow (G := arith) () (tk "x")   -- false

So the left operand of a juxt can *never* satisfy `HeadIn (follow e)` on its continuation. Yet
`f x y` parses perfectly. Why? Because the operands sit at **tighter levels**, where
juxtaposition is not applicable — nothing can extend them there, so a variable *is* a legal
follower **at that level**.

Hence the induction needs `follow e l` — the tokens that cannot extend an expression **at level
`l`**: the left-recursive operators valid at `l` (`Level.condition l o`), plus juxt if it is
valid at `l`. The current `follow e` is precisely the **loosest-level** instance, which is what
`Language1`'s interface wants — so the `IBip` index is right; it is the *induction* that needs
the refinement.

**(2) A grammar condition that `Entry` does not currently force.**

Inside an operator body, a hole is followed by a name token (`)` in `( _ )`, `then` in
`if _ then _ else _`). For that hole to parse *exactly* — stopping where the printed
sub-expression ended, rather than running on — that token must be in FOLLOW at the hole's level.

`follow t = true` iff `t` is not a variable **and** `t` heads no operator. `varDisjoint` already
gives the first half. The second is **missing**: a grammar with an operator *headed by* `)`
would make `follow ")" = false`, and `( e )` could not round-trip. This is the classic LL(1)
condition, and it is the analogue of `headsDistinct` for **interior** tokens.

    #eval follow (G := arith) () (tk ")")   -- true  -- interior; heads nothing
    #eval follow (G := arith) () (tk "(")   -- false -- HEADS the paren operator

So `Entry` needs one more field (or `Unambiguous` needs to imply it).
-/

/-- **The one open lemma.** The parser consumes exactly what was printed.

Stated with the **per-level** FOLLOW -- with `follow e` it would be *false* (a juxt's left
operand is followed by a variable, which is never in the loosest-level FOLLOW).

It does **not** need unambiguity: it is purely a statement about how *much* the parser consumes.
That is where FOLLOW earns its keep (stopping the greedy folds from eating into `rest`) and
where longest-match earns its keep (a candidate that really uses its operator consumes more than
one that falls through, so the parser cannot stop short).

Both prerequisites are now in place:
* the **per-level** FOLLOW below (a juxt's left operand lives at a tighter level, where
  juxtaposition is not applicable, so the variable that follows it does *not* continue it);
* **`follow_of_interior`** (`Biparser.lean`), from the `interiorTerminates` grammar condition —
  the `)` of `( _ )` stops the parser, so an operator's inner expression is parsed exactly.

What remains is the induction itself: mutual, over the tree, mirroring `parseExpr.induct`'s
7 motives, with the same **shifted** statements on the two accumulator folds that `Sound.lean`
needed (`acc.flatten ++ tkns`, not `tkns`). The `longer` combinator is what makes the fold cases
go through: a candidate that really uses its operator consumes strictly more than one that falls
through to a bare operand, so longest-match cannot stop short. -/
theorem parseExpr_exact {e : G.Ent} {l : Level (G.entry e)} (t : Expr G e l)
    (rest : List (Token G.isSep)) (hF : FollowAt e l rest) :
    ∃ t', runExpr e l (t.flatten ++ rest) = some (t', rest) := by
  sorry

/-! ## Completeness, and the round-trip law -- both DERIVED -/

/-- **Completeness**: printing a tree and parsing it back recovers *that* tree. -/
theorem parseExpr_complete (hU : Unambiguous G) {e : G.Ent} {l : Level (G.entry e)}
    (t : Expr G e l) (rest : List (Token G.isSep)) (hF : HeadIn (follow e) rest) :
    runExpr e l (t.flatten ++ rest) = some (t, rest) := by
  obtain ⟨t', ht'⟩ := parseExpr_exact t rest (followAt_of_follow hF)
  -- soundness: what the parser returned flattens to what it consumed
  have hsound : t'.flatten ++ rest = t.flatten ++ rest := by
    simp only [runExpr, Option.map_eq_some_iff] at ht'
    obtain ⟨x, hx, hxe⟩ := ht'
    have hs := parseExpr_sound e l (t.flatten ++ rest) x.1 x.2 hx
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨rfl, hrest⟩ := hxe
    rw [hrest] at hs
    exact hs
  -- hence the two trees print alike, hence (unambiguity) they are equal
  have ht : t' = t := hU e l t' t (by simpa using hsound)
  subst ht
  exact ht'

/-- **The round-trip law** for the mixfix biparser. -/
theorem mixfix_ok' (hU : Unambiguous G) (e : G.Ent) (l : Level (G.entry e)) :
    RoundTrips (biparser G e l) (HeadIn (follow e)) := by
  intro t rest hF
  have h := parseExpr_complete hU t rest hF
  simp only [runExpr] at h
  simpa [biparser, CBiparser.run, parseCB, Option.map_map] using h

/-- **The mixfix `IBip`** — a plug-in-ready biparser for an unambiguous grammar.

FIRST is `anyTok`: `firstOk` is a purely negative claim, so the weakest FIRST makes it vacuous —
and `anyTok` is exactly what `Language1`'s interface asks for. FOLLOW is derived from the
grammar. The round-trip law rides along. -/
def ibiparser (hU : Unambiguous G) (e : G.Ent) (l : Level (G.entry e)) :
    IBip (anyTok (G := G)) (follow e) (Expr G e l) (Expr G e l) where
  toCBiparser := biparser G e l
  firstOk := firstOk_any e l
  ok := mixfix_ok' hU e l

end LambdaLab.CBiparser.Mixfix
