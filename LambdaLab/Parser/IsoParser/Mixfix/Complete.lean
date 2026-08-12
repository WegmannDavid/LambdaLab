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
The grammar's three **lexical** conditions (`headsDistinct`, `varDisjoint` on `Entry`;
`interiorTerminates` on `Grammar`) are *fields*, not hypotheses: they would otherwise thread
through all seven motives of `parseExpr_exact` and through the whole unambiguity development.
Being fields, they also make a malformed grammar unrepresentable. Each is decidable for a
concrete grammar, so an instance discharges it by `decide`.

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

/-! ## Interior seams stop the hole's parser -/

/-- The payoff of `Grammar.interiorTerminates`: the token after a hole lies in the FOLLOW of the
**hole's** entry, so the greedy sub-parser stops exactly there. -/
theorem follow_of_interior {e : G.Ent} {o : (G.entry e).Op} {e' : G.Ent} {t : Tok}
    (h : (e', t) ∈ ((G.entry e).operator o).holeFollowers) : follow e' t = true := by
  obtain ⟨hvar, hheads⟩ := G.interiorTerminates e o e' t h
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

/-! ## Per-level seams: an operator's own head cannot continue its own operand

`follow_of_interior` covers the seams *inside* a notation — the `)` of `( _ )`. It does not cover
an operator's own leading operand hole, and it cannot: in `a + b` that hole is followed by `+`,
and `follow e "+" = false` because `+` continues an expression. That seam is carried by the
*per-level* condition instead, and the lemma below is why it holds. It is the second half of what
`parseExpr_exact` needs from the grammar's lexical fields. -/

omit [DecidableEq Tok] in
/-- `Tighter` is irreflexive — it strictly decreases `rank`. -/
theorem Tighter.irrefl {e : G.Ent} {o : (G.entry e).Op}
    (h : Tighter (G.entry e).tighter o o) : False :=
  Nat.lt_irrefl _ ((G.entry e).rank_lt_of_tighter h)

omit [DecidableEq Tok] in
/-- A head token is one of its operator's name tokens — the bridge to `varDisjoint`. -/
theorem mem_nameTokens_of_headTok? {e : G.Ent} {o : (G.entry e).Op} {t : Tok}
    (h : ((G.entry e).operator o).headTok? = some t) :
    t ∈ ((G.entry e).operator o).nameTokens := by
  simp only [Operator.headTok?] at h
  cases hn : ((G.entry e).operator o).nameTokens with
  | nil => rw [hn] at h; simp at h
  | cons a as => rw [hn] at h; simp at h; subst h; simp

/-- **An operator's own head token cannot continue its own operand.**

The left operand of `a + b` is parsed at `Level.tighter (+)` and is followed by `+` itself, so this
is exactly the seam that per-level FOLLOW exists to carry. Both disjuncts of `ContinuesAt` die by
`headsDistinct`, which forces the continuing operator to *be* `o`:

* a left-recursive continuation would need `Tighter o o`, impossible since `rank` strictly drops;
* juxtaposition continues through an *operand*, so `t` would have to start one — but `t` is a name
  token of `o`, so `varDisjoint` rules out the variable case, and the only operator heading `t` is
  `o`, which begins with a hole and therefore starts no operand.

Note the hypothesis: `o` must begin with a hole. That is precisely the case in which a leading
operand hole exists to be followed. -/
theorem not_continuesAt_tighter_head {e : G.Ent} {o : (G.entry e).Op} {t : Tok}
    (hhole : ((G.entry e).operator o).startsWithHole = true)
    (hhead : ((G.entry e).operator o).headTok? = some t) :
    ¬ ContinuesAt e (Level.tighter o) t := by
  rintro (⟨o', hcond, _, hhead'⟩ | ⟨j, hcond, _, hstart⟩)
  · have : o = o' := (G.entry e).headsDistinct o o' (by rw [hhead]; rfl) (by rw [hhead, hhead'])
    subst this
    exact Tighter.irrefl (show Tighter (G.entry e).tighter o o from hcond)
  · simp only [startsOperand, Bool.or_eq_true, List.any_eq_true] at hstart
    rcases hstart with hvar | ⟨o'', _, ho''⟩
    · exact absurd hvar (by
        rw [(G.entry e).varDisjoint o t (mem_nameTokens_of_headTok? hhead)]; simp)
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at ho''
      obtain ⟨hnh, hh⟩ := ho''
      have hhead'' : ((G.entry e).operator o'').headTok? = some t := by
        revert hh; cases hx : ((G.entry e).operator o'').headTok? <;> simp_all
      have : o = o'' := (G.entry e).headsDistinct o o'' (by rw [hhead]; rfl) (by rw [hhead, hhead''])
      subst this
      rw [hhole] at hnh; exact absurd hnh (by simp)

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

## Roadmap

The induction is mutual over `parseExpr.induct`'s **seven** motives, exactly as `Sound.lean`'s.
For each parse function, the statement to prove on `t.flatten ++ rest`:

| function            | statement                                                              |
|---------------------|------------------------------------------------------------------------|
| `parseExpr`         | succeeds, leftover `= rest`                                             |
| `parseExprList`     | ditto, *given* the printed tree's top operator is among the candidates  |
| `parseParts`        | ditto for a body shape, operand by operand                              |
| `parseJuxt`         | ditto for a whole application chain                                     |
| `parseJuxtExtend`   | **shifted**: from `acc`, consumes the remaining chain (`acc.flatten ++ …`) |
| `parseInfixL`       | ditto for a left-associative chain                                      |
| `parseInfixLExtend` | **shifted**, as `parseJuxtExtend`                                       |

The two accumulator folds need the *shifted* form (`acc.flatten ++ tkns`, not `tkns`) — stated
unshifted the induction does not go through; `Sound.lean` hit the same wall and its `motive4`/
`motive6` show the shape.

Three places carry the real content, and each is where one hypothesis earns its keep:

1. **Nothing stops short.** `longer` takes the longest match, and a candidate that genuinely uses
   its operator consumes strictly more than one that falls through to a bare operand — so the
   fold cannot stop early. Needs: the printed tree's own operator is a candidate at this level
   (`Level.condition`), and its parse consumes everything it printed (the IH).
2. **Nothing runs long.** The greedy folds must not eat into `rest`. This is `FollowAt`: at the
   operand's level nothing in `rest` can continue the expression. Note the level-sensitivity —
   at `loosest` a variable *does* continue (juxtaposition), at a tighter level it does not.
3. **Seams stop the hole**, and there are **two kinds**, needing different lemmas — worth knowing
   before starting, since assuming one kind covers both is the obvious wrong turn:
   * *Interior* seams, inside a notation: the `)` of `( _ )`. Full `follow` holds there, via
     `follow_of_interior` from `interiorTerminates` — and it must be read at the *hole's* entry,
     not the host's.
   * The operator's *own operand* seam: the leading hole of `a + b` is followed by `+`. Full
     `follow` is **false** here (`+` continues an expression), and `interiorTerminates` says
     nothing about it, because `holeFollowers` covers only a notation's interior. What carries it
     is the per-level condition, via `not_continuesAt_tighter_head` above.

   So the side condition threaded through `motive2` cannot be "every hole is followed by a token in
   `follow`". It has to be the per-level `¬ ContinuesAt e l t` at each hole's own level, which the
   first bullet implies and the second bullet supplies directly.

Useful existing machinery: `longer_eq_some` and `orElse_eq_some` (a bare `split` generalises both
alternatives into opaque variables and severs the IHs), the cast lemmas
`Parts.flatten_cast`/`Expr.reindex_flatten`/`juxtApp_flatten`/`infxlApp_flatten`, and
`zetaDelta := true` for the `let`-bound left operand. `parseExpr.induct` already splits the
nested matches — re-splitting them is what breaks the IHs. -/
theorem parseExpr_exact {e : G.Ent} {l : Level (G.entry e)} (t : Expr G e l)
    (rest : List Tok) (hF : FollowAt e l rest) :
    ∃ t', runExpr e l (t.flatten ++ rest) = some (t', rest) := by
  sorry

/-- **Completeness**: printing a tree and parsing it back recovers *that* tree. Three lines from
the decomposition — soundness turns "leftover = rest" into "the trees print alike", and
unambiguity turns that into "the trees are equal". -/
theorem parseExpr_complete (hU : Unambiguous G) {e : G.Ent}
    {l : Level (G.entry e)} (t : Expr G e l) (rest : List Tok)
    (hF : HeadIn (fun t => follow e t = true) rest) :
    runExpr e l (t.flatten ++ rest) = some (t, rest) := by
  obtain ⟨t', ht'⟩ := parseExpr_exact t rest (followAt_of_follow hF)
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
