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

/-! ## Unambiguity — and why it is unavoidable

Completeness-as-equality requires `flatten` to be **injective**, and this is forced for *any*
deterministic parser, not just ours: if `t₁ ≠ t₂` flatten alike, a deterministic parser returns
one of them, and the other cannot possibly round-trip. `headsDistinct` does **not** supply it
(this repo has a machine-checked counterexample to that implication). So it is a hypothesis. -/

/-- Distinct trees at a level print distinctly. -/
def Unambiguous (G : Grammar) : Prop :=
  ∀ (e : G.Ent) (l : Level (G.entry e)) (t₁ t₂ : Expr G e l), t₁.flatten = t₂.flatten → t₁ = t₂

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

/-- **The one open lemma.** The parser consumes exactly what was printed.

*Not yet proved.* Needs induction on the tree, with FOLLOW stopping the greedy folds
(`parseJuxt`/`parseInfixL`) precisely where `t.flatten` ends. -/
theorem parseExpr_exact {e : G.Ent} {l : Level (G.entry e)} (t : Expr G e l)
    (rest : List (Token G.isSep)) (hF : HeadIn (follow e) rest) :
    ∃ t', runExpr e l (t.flatten ++ rest) = some (t', rest) := by
  sorry

/-! ## Completeness, and the round-trip law -- both DERIVED -/

/-- **Completeness**: printing a tree and parsing it back recovers *that* tree. -/
theorem parseExpr_complete (hU : Unambiguous G) {e : G.Ent} {l : Level (G.entry e)}
    (t : Expr G e l) (rest : List (Token G.isSep)) (hF : HeadIn (follow e) rest) :
    runExpr e l (t.flatten ++ rest) = some (t, rest) := by
  obtain ⟨t', ht'⟩ := parseExpr_exact t rest hF
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
