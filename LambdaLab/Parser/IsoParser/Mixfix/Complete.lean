import LambdaLab.Parser.IsoParser.Mixfix.Sound
import LambdaLab.Parser.IsoParser.Basic

/-!
# FOLLOW, the grammar's lexical conditions, and the round-trip law — decomposed

The round-trip law (print a tree, parse it back, recover *that* tree) splits into three parts,
only one of which is open:

```
  parseExpr_exact   (OPEN)  -- the parser consumes EXACTLY the printed tokens
+ parseExpr_sound   (proved, Sound.lean)
+ Unambiguous G     (hypothesis)
⇒ parseExpr_complete       ⇒  mixfix's `ok`
```

Two hypotheses are genuinely necessary, not artifacts of the proof:

* **`Unambiguous G`.** `Ambiguity.lean` exhibits a grammar with two operators sharing a notation
  and *proves* the law false for it (`law_not_universal`). Any deterministic parser returns one
  tree for one token list, so the other cannot round-trip. No proof effort removes this.
* **`Lawful G`.** The three lexical conditions the lightweight `Grammar` deliberately omits.
  `interiorTerminates` is the load-bearing one: in `( _ )` the only thing that can stop the
  hole's parser is the following `)`, so `)` must lie in the **hole entry's** FOLLOW. Without it
  the greedy parser runs past the `)` and a printed tree does not parse back. It lives here
  rather than on `Entry` because a hole's entry is in general a *different* entry from the
  operator's host, and an `Entry` cannot see its siblings.

Both are decidable for a concrete grammar (finite operator and seam lists), so an instance
discharges them by `decide`.

## Why FOLLOW must be per-level

With the entry-level `follow e`, `parseExpr_exact` would be **false**: a juxtaposition's left
operand is followed by its right operand, which begins with a *variable* — an operand-starter,
hence never in `follow e`. Yet `f x y` parses fine, because the operands sit at *tighter* levels
where juxtaposition is not applicable, so nothing can extend them there. `ContinuesAt`/`FollowAt`
below are the per-level refinement; `followAt_of_follow` bridges from the computable `follow`
(which excludes *every* operator, so it is the strongest FOLLOW and implies the per-level one).
-/

namespace LambdaLab.Parser.IsoParser.Mixfix

open LambdaLab.Parser.IsoParser

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

/-- **Continuation at a level**: `t` can extend an expression at level `l` — either it heads a
left-recursive operator valid at `l`, or juxtaposition is valid at `l` and `t` starts an operand
(juxt continues via an operand, having no token of its own). -/
def ContinuesAt (e : G.Ent) (l : Level (G.entry e)) (t : Tok) : Prop :=
  (∃ o, Level.condition l o ∧ ((G.entry e).operator o).startsWithHole = true ∧
        ((G.entry e).operator o).headTok? = some t)
  ∨ (∃ j, Level.condition l j ∧ (G.entry e).operator j = Operator.juxt ∧
          startsOperand e t = true)

/-- **FOLLOW at a level**: the tokens that cannot extend an expression at `l`. -/
def FollowAt (e : G.Ent) (l : Level (G.entry e)) (rest : List Tok) : Prop :=
  ∀ t, rest.head? = some t → ¬ ContinuesAt e l t

/-- The computable `follow` is the **strongest** FOLLOW: it excludes *every* operator, not just
those valid at a level. So it implies `FollowAt` at every level — which is what lets the
loosest-level parser index feed the level-indexed induction. -/
theorem followAt_of_follow {e : G.Ent} {l : Level (G.entry e)} {rest : List Tok}
    (h : HeadIn (fun t => follow e t = true) rest) : FollowAt e l rest := by
  intro t ht hcon
  have hf : follow e t = true := h t ht
  simp only [follow, Bool.and_eq_true, Bool.not_eq_true'] at hf
  obtain ⟨hstart, hcont⟩ := hf
  rcases hcon with ⟨o, _, hhole, hhead⟩ | ⟨j, _, hjuxt, hstart'⟩
  · have : continuesExpr e t = true := by
      simp only [continuesExpr, List.any_eq_true]
      exact ⟨o, (G.entry e).ops_complete o, by simp [hhole, hhead]⟩
    rw [this] at hcont; exact absurd hcont (by simp)
  · rw [hstart'] at hstart; exact absurd hstart (by simp)

/-! ## The grammar's lexical conditions -/

/-- The three lexical conditions the lightweight `Grammar` omits, bundled as a `Prop` so existing
grammars need not change shape. Every clause ranges over finite lists, so a concrete grammar
discharges the bundle by `decide`.

Together they say: **every token has exactly one lexical role at every seam it can reach.** -/
structure Lawful (G : Grammar Tok) : Prop where
  /-- Distinct operators have distinct leading tokens (when they have one at all). -/
  headsDistinct : ∀ (e : G.Ent) (o₁ o₂ : (G.entry e).Op),
    ((G.entry e).operator o₁).headTok?.isSome = true →
    ((G.entry e).operator o₁).headTok? = ((G.entry e).operator o₂).headTok? → o₁ = o₂
  /-- No operator name part is a variable token. -/
  varDisjoint : ∀ (e : G.Ent) (o : (G.entry e).Op) (t : Tok),
    t ∈ ((G.entry e).operator o).nameTokens → (G.entry e).isVar t = false
  /-- **Interior seams terminate**: the token after a hole lies in the *hole entry's* FOLLOW. -/
  interiorTerminates : ∀ (e : G.Ent) (o : (G.entry e).Op) (e' : G.Ent) (t : Tok),
    (e', t) ∈ ((G.entry e).operator o).holeFollowers →
      (G.entry e').isVar t = false ∧
        ∀ o' : (G.entry e').Op, ((G.entry e').operator o').headTok? ≠ some t

/-- The payoff: an interior seam token stops the hole's parser. -/
theorem follow_of_interior (hL : Lawful G) {e : G.Ent} {o : (G.entry e).Op} {e' : G.Ent} {t : Tok}
    (h : (e', t) ∈ ((G.entry e).operator o).holeFollowers) : follow e' t = true := by
  obtain ⟨hvar, hheads⟩ := hL.interiorTerminates e o e' t h
  simp only [follow, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · simp only [startsOperand, Bool.or_eq_false_iff, hvar, true_and]
    simp only [List.any_eq_false]
    intro o' _
    cases hh : ((G.entry e').operator o').headTok? with
    | none => simp
    | some h' =>
        have hne : h' ≠ t := fun heq => hheads o' (by rw [hh, heq])
        simp [hne]
  · simp only [continuesExpr, List.any_eq_false]
    intro o' _
    cases hh : ((G.entry e').operator o').headTok? with
    | none => simp
    | some h' =>
        have hne : h' ≠ t := fun heq => hheads o' (by rw [hh, heq])
        simp [hne]

/-! A concrete grammar discharges `Lawful` by casing on its (finite) entries and operators and
deciding the resulting closed token facts — see `Arith.aLawful` for the ~15-line script, which
transfers verbatim to any grammar (only the three definition names in the `simp` sets change). -/

/-! ## Unambiguity -/

/-- **Unambiguity**: `flatten` is injective on each level. Required by *any* deterministic
parser — see `Ambiguity.law_not_universal` for the machine-checked proof that dropping it makes
the round-trip law false. -/
def Unambiguous (G : Grammar Tok) : Prop :=
  ∀ (e : G.Ent) (l : Level (G.entry e)) (t₁ t₂ : Expr G e l), t₁.flatten = t₂.flatten → t₁ = t₂

/-! ## The decomposition -/

/-- The parser with the progress witness erased. -/
def runExpr (e : G.Ent) (l : Level (G.entry e)) (input : List Tok) :
    Option (Expr G e l × List Tok) :=
  (parseExpr e l input).map (fun x => (x.1, x.2.list))

/-- **The one open lemma.** The parser succeeds on a printed tree followed by an admissible
continuation, and consumes *exactly* the printed part.

It does **not** mention unambiguity: it is purely a statement about how *much* is consumed. This
is where the per-level FOLLOW earns its keep (stopping the greedy folds from eating into `rest`),
where `interiorTerminates` earns its keep (the `)` of `( _ )` stops the hole's parser), and where
longest-match earns its keep (a candidate that really uses its operator consumes strictly more
than one that falls through to a bare operand, so the parser cannot stop short).

What remains is the induction: mutual, over the tree, mirroring `parseExpr.induct`'s seven
motives, with the **shifted** statements on the two accumulator folds that `Sound.lean` needed
(`acc.flatten ++ tkns`, not `tkns`). -/
theorem parseExpr_exact (hL : Lawful G) {e : G.Ent} {l : Level (G.entry e)} (t : Expr G e l)
    (rest : List Tok) (hF : FollowAt e l rest) :
    ∃ t', runExpr e l (t.flatten ++ rest) = some (t', rest) := by
  sorry

/-- **Completeness**: printing a tree and parsing it back recovers *that* tree. Three lines from
the decomposition — soundness turns "leftover = rest" into "the trees print alike", and
unambiguity turns that into "the trees are equal". -/
theorem parseExpr_complete (hL : Lawful G) (hU : Unambiguous G) {e : G.Ent}
    {l : Level (G.entry e)} (t : Expr G e l) (rest : List Tok)
    (hF : HeadIn (fun t => follow e t = true) rest) :
    runExpr e l (t.flatten ++ rest) = some (t, rest) := by
  obtain ⟨t', ht'⟩ := parseExpr_exact hL t rest (followAt_of_follow hF)
  have hsound : t'.flatten ++ rest = t.flatten ++ rest := by
    simp only [runExpr, Option.map_eq_some_iff] at ht'
    obtain ⟨x, hx, hxe⟩ := ht'
    have hs := parseExpr_sound e l (t.flatten ++ rest) x.1 x.2 hx
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨rfl, hrest⟩ := hxe
    rw [hrest] at hs
    exact hs
  have ht : t' = t := hU e l t' t (by simpa using hsound)
  subst ht
  exact ht'

end LambdaLab.Parser.IsoParser.Mixfix
