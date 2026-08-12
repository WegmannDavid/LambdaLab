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

/-! ## The shape of a parts sequence, and its two side conditions

`parseExpr_exact`'s `motive2` has to say what a *body* needs in order to parse back exactly. Two
separate things, and separating them is the point:

* **`Seamed ps`** — internal: every hole with parts after it is stopped by the next name token, at
  **that hole's own level**. Not `follow`: see `not_continuesAt_tighter_head` above for why the
  operator's own operand seam cannot use it.
* **`PartsFollow ps rest`** — external: what the tokens *after* the body must satisfy. Only a
  trailing hole constrains them at all.

`seamed_body` below is the payoff and the design check: every non-left-recursive operator body is
`Seamed`, with the two seam kinds discharged by their two different lemmas. These are the
prerequisites for the open theorem, not yet its proof.
-/

/-- Every hole with parts after it is stopped by the next name token, at the hole's own level. -/
def Seamed : List (Part G) → Prop
  | []      => True
  | [_]     => True
  | Part.hole e l :: y :: r =>
      (match y with
       | Part.namePart t => ¬ ContinuesAt e l t
       | Part.hole _ _   => False) ∧ Seamed (y :: r)
  | Part.namePart _ :: y :: r => Seamed (y :: r)

/-- What must hold of the tokens *after* a parts sequence: only a trailing hole constrains them. -/
def PartsFollow : List (Part G) → List Tok → Prop
  | []                 , _    => True
  | [Part.namePart _]  , _    => True
  | [Part.hole e l]    , rest => FollowAt e l rest
  | _ :: y :: r        , rest => PartsFollow (y :: r) rest

omit [DecidableEq Tok] in
theorem toParts_head (n : Notation Tok G.Ent) :
    ∃ ps, Notation.toParts (G := G) n = Part.namePart n.firstTok :: ps := by
  cases n with
  | last t => exact ⟨[], rfl⟩
  | cons t e' rest => exact ⟨Part.hole e' Level.loosest :: rest.toParts, rfl⟩

/-- A notation's parts, followed by anything seamed, are seamed. -/
theorem seamed_toParts_append (n : Notation Tok G.Ent) (suffix : List (Part G))
    (hs : ∀ e' t, (e', t) ∈ n.holeFollowers → ¬ ContinuesAt e' Level.loosest t)
    (hsuf : Seamed suffix) :
    Seamed (Notation.toParts (G := G) n ++ suffix) := by
  induction n with
  | last t =>
      cases suffix with
      | nil => exact trivial
      | cons y r => exact hsuf
  | cons t e' rest ih =>
      have hrest : Seamed (Notation.toParts (G := G) rest ++ suffix) :=
        ih (fun e'' t'' hm => hs e'' t'' (List.mem_cons_of_mem _ hm))
      have hseam : ¬ ContinuesAt e' Level.loosest rest.firstTok :=
        hs e' rest.firstTok List.mem_cons_self
      obtain ⟨ps, hps⟩ := toParts_head (G := G) rest
      show Seamed (Part.namePart t :: Part.hole e' Level.loosest ::
        (Notation.toParts (G := G) rest ++ suffix))
      rw [hps] at hrest ⊢
      exact ⟨hseam, hrest⟩

/-- `follow_of_interior`, in the pointwise per-level form `Seamed` wants. -/
theorem not_continuesAt_of_interior {e : G.Ent} {o : (G.entry e).Op} {e' : G.Ent} {t : Tok}
    {l : Level (G.entry e')}
    (h : (e', t) ∈ ((G.entry e).operator o).holeFollowers) : ¬ ContinuesAt e' l t :=
  followAt_of_follow (l := l) (rest := [t])
    (fun c hc => by simp at hc; subst hc; exact follow_of_interior h) t rfl

omit [DecidableEq Tok] in
/-- A notation's first token is its operator's head token. -/
theorem headTok?_toTokens (n : Notation Tok G.Ent) : n.toTokens.head? = some n.firstTok := by
  cases n <;> rfl

/-- **Operator bodies are seamed** — the two seam kinds, discharged by their two lemmas. -/
theorem seamed_body {e : G.Ent} (a : (G.entry e).Op)
    (hnl : ((G.entry e).operator a).leftRec = false) : Seamed (Operator.body e a) := by
  have hint : ∀ (n : Notation Tok G.Ent), ((G.entry e).operator a).holeFollowers = n.holeFollowers →
      ∀ e' t, (e', t) ∈ n.holeFollowers → ¬ ContinuesAt e' Level.loosest t := by
    intro n hn e' t hm; exact not_continuesAt_of_interior (o := a) (by rw [hn]; exact hm)
  have hown : ∀ (n : Notation Tok G.Ent), ((G.entry e).operator a).nameTokens = n.toTokens →
      ((G.entry e).operator a).startsWithHole = true →
      ¬ ContinuesAt e (Level.tighter a) n.firstTok := by
    intro n hn hh
    exact not_continuesAt_tighter_head hh
      (by simp only [Operator.headTok?, hn]; exact headTok?_toTokens n)
  -- the three hole-leading fixities share a shape: `hole :: (toParts n ++ tail)`
  have lead : ∀ (n : Notation Tok G.Ent) (tail : List (Part G)),
      ((G.entry e).operator a).nameTokens = n.toTokens →
      ((G.entry e).operator a).startsWithHole = true →
      ((G.entry e).operator a).holeFollowers = n.holeFollowers →
      Seamed tail →
      Seamed (Part.hole e (Level.tighter a) :: (Notation.toParts (G := G) n ++ tail)) := by
    intro n tail hnt hh hhf htail
    obtain ⟨ps, hps⟩ := toParts_head (G := G) n
    have hbody : Seamed (Notation.toParts (G := G) n ++ tail) :=
      seamed_toParts_append (G := G) n tail (hint n hhf) htail
    rw [hps] at hbody ⊢
    exact ⟨hown n hnt hh, hbody⟩
  cases hop : (G.entry e).operator a with
  | closed n =>
      have hb : Operator.body e a = Notation.toParts (G := G) n := by
        unfold Operator.body; rw [hop]
      rw [hb]
      have := seamed_toParts_append (G := G) n [] (hint n (by rw [hop]; rfl)) trivial
      simpa using this
  | prefx n =>
      have hb : Operator.body e a
          = Notation.toParts (G := G) n ++ [Part.hole e (Level.tighter a)] := by
        unfold Operator.body; rw [hop]
      rw [hb]
      exact seamed_toParts_append (G := G) n _ (hint n (by rw [hop]; rfl)) trivial
  | infx n =>
      have hb : Operator.body e a = Part.hole e (Level.tighter a)
          :: (Notation.toParts (G := G) n ++ [Part.hole e (Level.tighter a)]) := by
        unfold Operator.body; rw [hop]; simp
      rw [hb]
      exact lead n _ (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) trivial
  | infxr n =>
      have hb : Operator.body e a = Part.hole e (Level.tighter a)
          :: (Notation.toParts (G := G) n ++ [Part.hole e (Level.tighterEq a)]) := by
        unfold Operator.body; rw [hop]; simp
      rw [hb]
      exact lead n _ (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) trivial
  | postfx n =>
      have hb : Operator.body e a
          = Part.hole e (Level.tighter a) :: (Notation.toParts (G := G) n ++ []) := by
        unfold Operator.body; rw [hop]; simp
      rw [hb]
      exact lead n _ (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) trivial
  | infxl n => rw [hop, Operator.leftRec] at hnl; exact absurd hnl (by simp)
  | juxt    => rw [hop, Operator.leftRec] at hnl; exact absurd hnl (by simp)

/-- The tail a left-associative fold parses repeatedly is seamed too. Its leading hole was
consumed by the accumulator, so only the notation's interior seams remain. -/
theorem seamed_body_tail {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) : Seamed (Operator.body e o).tail := by
  cases hop : (G.entry e).operator o with
  | infxl n =>
      have hb : (Operator.body e o).tail
          = Notation.toParts (G := G) n ++ [Part.hole e (Level.tighter o)] := by
        unfold Operator.body; rw [hop]; simp
      rw [hb]
      refine seamed_toParts_append (G := G) n _ ?_ trivial
      intro e' t hm
      exact not_continuesAt_of_interior (o := o) (by rw [hop]; exact hm)
  | _ => rw [hop] at hl; simp [Operator.isInfxl] at hl

/-! ## Decomposing the two left-recursive chains

`motive4` and `motive6` are about `parseJuxtExtend`/`parseInfixLExtend`, which fold arguments onto
an accumulator. To state them over a *tree* the tree must first be taken apart the same way: a
chain at level `tighterEq j` is a base operand at `tighter j` plus a **list** of further pieces,
left-nested. That is what `juxt_decomp` and `infxl_decomp` supply, and until they existed the two
fold motives could not even be written down.

Both go by strong induction on `Expr.size`, and both split on whether the node's operator *is* the
chaining one: if it is, the node is one application and its left component is a shorter chain; if
it is not, `TighterEq` minus reflexivity is `Tighter`, so the whole tree is a lone operand
(`tighter_of_tighterEq_ne`).

The fiddly part is the shape index. `Operator.body e j` is only *propositionally* equal to the
two-hole list, so the operand extraction goes through a cast, and `rw` cannot reach under it —
the transport is done explicitly with `congrArg` plus `Parts.cast_symm_cast`.
-/

/-- Invert a two-hole body: the parts of a `juxt` node are exactly its two operands. -/
def Parts.twoHoles {e : G.Ent} {l₁ l₂ : Level (G.entry e)}
    (p : Parts G [Part.hole e l₁, Part.hole e l₂]) : Expr G e l₁ × Expr G e l₂ :=
  match p with
  | .hole f (.hole x .nil) => (f, x)

omit [DecidableEq Tok] in
theorem Parts.twoHoles_flatten {e : G.Ent} {l₁ l₂ : Level (G.entry e)}
    (p : Parts G [Part.hole e l₁, Part.hole e l₂]) :
    p.flatten = (p.twoHoles).1.flatten ++ (p.twoHoles).2.flatten := by
  match p with
  | .hole f (.hole x .nil) => simp [Parts.twoHoles, Parts.flatten]

omit [DecidableEq Tok] in
theorem Parts.twoHoles_eta {e : G.Ent} {l₁ l₂ : Level (G.entry e)}
    (p : Parts G [Part.hole e l₁, Part.hole e l₂]) :
    p = Parts.hole p.twoHoles.1 (Parts.hole p.twoHoles.2 Parts.nil) := by
  match p with
  | .hole f (.hole x .nil) => rfl

/-- Left-fold a chain of juxtaposed arguments onto an accumulator. -/
def juxtFold {e : G.Ent} {j : (G.entry e).Op} (hj : (G.entry e).operator j = Operator.juxt)
    (base : Expr G e (Level.tighterEq j)) :
    List (Expr G e (Level.tighter j)) → Expr G e (Level.tighterEq j)
  | []      => base
  | x :: xs => juxtFold hj (Expr.juxtApp hj base x) xs

omit [DecidableEq Tok] in
@[simp] theorem juxtFold_nil {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt) (base : Expr G e (Level.tighterEq j)) :
    juxtFold hj base [] = base := rfl

omit [DecidableEq Tok] in
/-- Appending one more argument at the end is one more application on the outside. -/
theorem juxtFold_snoc {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt) (base : Expr G e (Level.tighterEq j))
    (xs : List (Expr G e (Level.tighter j))) (x : Expr G e (Level.tighter j)) :
    juxtFold hj base (xs ++ [x]) = Expr.juxtApp hj (juxtFold hj base xs) x := by
  induction xs generalizing base with
  | nil => rfl
  | cons y ys ih => simpa [juxtFold] using ih (Expr.juxtApp hj base y)

omit [DecidableEq Tok] in
/-- The flattening of a fold is the concatenation of its pieces. -/
theorem juxtFold_flatten {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt) (base : Expr G e (Level.tighterEq j))
    (xs : List (Expr G e (Level.tighter j))) :
    (juxtFold hj base xs).flatten = base.flatten ++ (xs.map Expr.flatten).flatten := by
  induction xs generalizing base with
  | nil => simp [juxtFold]
  | cons y ys ih => simp [juxtFold, ih (Expr.juxtApp hj base y), List.append_assoc]

/-- Weakening a strictly-tighter operand to the chaining level. -/
def Expr.toEq {e : G.Ent} {j : (G.entry e).Op} (x : Expr G e (Level.tighter j)) :
    Expr G e (Level.tighterEq j) :=
  x.reindex (l := Level.tighter j) (l' := Level.tighterEq j)
    (fun _o hh => Tighter.toTighterEq (show Tighter (G.entry e).tighter j _o from hh))

omit [DecidableEq Tok] in
@[simp] theorem Expr.toEq_flatten {e : G.Ent} {j : (G.entry e).Op}
    (x : Expr G e (Level.tighter j)) : x.toEq.flatten = x.flatten := by
  simp [Expr.toEq]

omit [DecidableEq Tok] in
theorem Parts.size_cast {s s' : List (Part G)} (h : s = s') (ps : Parts G s) :
    (h ▸ ps).size = ps.size := by subst h; rfl

omit [DecidableEq Tok] in
theorem Parts.cast_symm_cast {s s' : List (Part G)} (h : s = s') (ps : Parts G s) :
    h.symm ▸ (h ▸ ps) = ps := by subst h; rfl

omit [DecidableEq Tok] in
/-- `TighterEq j o` with `o ≠ j` is `Tighter j o`. -/
theorem tighter_of_tighterEq_ne {e : G.Ent} {j o : (G.entry e).Op}
    (h : TighterEq (G.entry e).tighter j o) (hne : ¬ o = j) : Tighter (G.entry e).tighter j o := by
  cases h with
  | refl => exact absurd rfl hne
  | step hmem hrest => exact Tighter.ofMemTighterEq hmem hrest

omit [DecidableEq Tok] in
/-- **A juxtaposition chain is a base operand plus a list of arguments.**

The decomposition the two accumulator folds are stated over. Every tree at the chaining level
`tighterEq j` is either an operand one level tighter, or an application whose left component is
itself such a chain — so unrolling gives a base and a left-nested list. -/
theorem juxt_decomp {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt) :
    ∀ (n : Nat) (t : Expr G e (Level.tighterEq j)), t.size ≤ n →
      ∃ (x₀ : Expr G e (Level.tighter j)) (xs : List (Expr G e (Level.tighter j))),
        t = juxtFold hj x₀.toEq xs := by
  intro n
  induction n with
  | zero =>
      intro t ht
      cases t <;> simp [Expr.size] at ht
  | succ m ih =>
      intro t ht
      match t with
      | .var tok hv => exact ⟨Expr.var tok hv, [], rfl⟩
      | .op o hc parts =>
          by_cases hoj : o = j
          · subst hoj
            have hparts :
                ((Operator.body_juxt hj).symm ▸
                  (Parts.hole ((Operator.body_juxt hj ▸ parts).twoHoles).1
                    (Parts.hole ((Operator.body_juxt hj ▸ parts).twoHoles).2 Parts.nil))
                  : Parts G (Operator.body e o)) = parts :=
              (congrArg (fun q => (Operator.body_juxt hj).symm ▸ q)
                  (Parts.twoHoles_eta (Operator.body_juxt hj ▸ parts))).symm.trans
                (Parts.cast_symm_cast (Operator.body_juxt hj) parts)
            have hnode : Expr.op (l := Level.tighterEq o) o hc parts
                = Expr.juxtApp hj ((Operator.body_juxt hj ▸ parts).twoHoles).1
                    ((Operator.body_juxt hj ▸ parts).twoHoles).2 := by
              unfold Expr.juxtApp
              rw [hparts]
            have hsz : ((Operator.body_juxt hj ▸ parts).twoHoles).1.size ≤ m := by
              have hpe := Parts.twoHoles_eta (Operator.body_juxt hj ▸ parts)
              have hc2 : (Operator.body_juxt hj ▸ parts).size = parts.size :=
                Parts.size_cast (Operator.body_juxt hj) parts
              rw [hpe] at hc2
              simp only [Parts.size, Expr.size] at hc2 ht ⊢
              omega
            obtain ⟨x₀, xs, hx₀⟩ := ih _ hsz
            exact ⟨x₀, xs ++ [((Operator.body_juxt hj ▸ parts).twoHoles).2],
              by rw [hnode, juxtFold_snoc, ← hx₀]⟩
          · exact ⟨Expr.op (l := Level.tighter j) o (tighter_of_tighterEq_ne hc hoj) parts, [], rfl⟩

omit [DecidableEq Tok] in
/-- `juxt_decomp` with the size bound discharged. -/
theorem juxt_decomp' {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt) (t : Expr G e (Level.tighterEq j)) :
    ∃ (x₀ : Expr G e (Level.tighter j)) (xs : List (Expr G e (Level.tighter j))),
      t = juxtFold hj x₀.toEq xs :=
  juxt_decomp hj t.size t (Nat.le_refl _)

/-! ### The same for a left-associative chain

`infxl` folds whole body *tails* rather than single operands, so the list is of `Parts`. -/

/-- Invert a body whose first part is a hole. -/
def Parts.headHole {e : G.Ent} {l : Level (G.entry e)} {ps : List (Part G)}
    (p : Parts G (Part.hole e l :: ps)) : Expr G e l × Parts G ps :=
  match p with
  | .hole x rest => (x, rest)

omit [DecidableEq Tok] in
theorem Parts.headHole_eta {e : G.Ent} {l : Level (G.entry e)} {ps : List (Part G)}
    (p : Parts G (Part.hole e l :: ps)) :
    p = Parts.hole p.headHole.1 p.headHole.2 := by
  match p with
  | .hole x rest => rfl

def infxlFold {e : G.Ent} {o : (G.entry e).Op} (hl : ((G.entry e).operator o).isInfxl = true)
    (base : Expr G e (Level.tighterEq o)) :
    List (Parts G (Operator.body e o).tail) → Expr G e (Level.tighterEq o)
  | []      => base
  | p :: ps => infxlFold hl (Expr.infxlApp hl base p) ps

omit [DecidableEq Tok] in
@[simp] theorem infxlFold_nil {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) (base : Expr G e (Level.tighterEq o)) :
    infxlFold hl base [] = base := rfl

omit [DecidableEq Tok] in
theorem infxlFold_snoc {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) (base : Expr G e (Level.tighterEq o))
    (ps : List (Parts G (Operator.body e o).tail)) (p : Parts G (Operator.body e o).tail) :
    infxlFold hl base (ps ++ [p]) = Expr.infxlApp hl (infxlFold hl base ps) p := by
  induction ps generalizing base with
  | nil => rfl
  | cons q qs ih => simpa [infxlFold] using ih (Expr.infxlApp hl base q)

omit [DecidableEq Tok] in
theorem infxlFold_flatten {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) (base : Expr G e (Level.tighterEq o))
    (ps : List (Parts G (Operator.body e o).tail)) :
    (infxlFold hl base ps).flatten = base.flatten ++ (ps.map Parts.flatten).flatten := by
  induction ps generalizing base with
  | nil => simp [infxlFold]
  | cons q qs ih => simp [infxlFold, ih (Expr.infxlApp hl base q), List.append_assoc]

omit [DecidableEq Tok] in
/-- **A left-associative chain is a base operand plus a list of body tails.** -/
theorem infxl_decomp {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) :
    ∀ (n : Nat) (t : Expr G e (Level.tighterEq o)), t.size ≤ n →
      ∃ (x₀ : Expr G e (Level.tighter o)) (ps : List (Parts G (Operator.body e o).tail)),
        t = infxlFold hl x₀.toEq ps := by
  intro n
  induction n with
  | zero => intro t ht; cases t <;> simp [Expr.size] at ht
  | succ m ih =>
      intro t ht
      match t with
      | .var tok hv => exact ⟨Expr.var tok hv, [], rfl⟩
      | .op b hc parts =>
          by_cases hbo : b = o
          · subst hbo
            have hparts :
                ((Operator.body_infxl_cons hl).symm ▸
                  (Parts.hole ((Operator.body_infxl_cons hl ▸ parts).headHole).1
                    ((Operator.body_infxl_cons hl ▸ parts).headHole).2)
                  : Parts G (Operator.body e b)) = parts :=
              (congrArg (fun q => (Operator.body_infxl_cons hl).symm ▸ q)
                  (Parts.headHole_eta (Operator.body_infxl_cons hl ▸ parts))).symm.trans
                (Parts.cast_symm_cast (Operator.body_infxl_cons hl) parts)
            have hnode : Expr.op (l := Level.tighterEq b) b hc parts
                = Expr.infxlApp hl ((Operator.body_infxl_cons hl ▸ parts).headHole).1
                    ((Operator.body_infxl_cons hl ▸ parts).headHole).2 := by
              unfold Expr.infxlApp
              rw [hparts]
            have hsz : ((Operator.body_infxl_cons hl ▸ parts).headHole).1.size ≤ m := by
              have hpe := Parts.headHole_eta (Operator.body_infxl_cons hl ▸ parts)
              have hc2 : (Operator.body_infxl_cons hl ▸ parts).size = parts.size :=
                Parts.size_cast (Operator.body_infxl_cons hl) parts
              rw [hpe] at hc2
              simp only [Parts.size, Expr.size] at hc2 ht ⊢
              omega
            obtain ⟨x₀, ps, hx₀⟩ := ih _ hsz
            exact ⟨x₀, ps ++ [((Operator.body_infxl_cons hl ▸ parts).headHole).2],
              by rw [hnode, infxlFold_snoc, ← hx₀]⟩
          · exact ⟨Expr.op (l := Level.tighter o) b (tighter_of_tighterEq_ne hc hbo) parts, [], rfl⟩

omit [DecidableEq Tok] in
/-- `infxl_decomp` with the size bound discharged. -/
theorem infxl_decomp' {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) (t : Expr G e (Level.tighterEq o)) :
    ∃ (x₀ : Expr G e (Level.tighter o)) (ps : List (Parts G (Operator.body e o).tail)),
      t = infxlFold hl x₀.toEq ps :=
  infxl_decomp hl t.size t (Nat.le_refl _)

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

`motive1`'s direction, which type-checks and is what the others follow:

```lean
motive1 e l tkns := ∀ (t : Expr G e l) (rest : List Tok),
  tkns = t.flatten ++ rest → FollowAt e l rest →
  ∃ t' s, parseExpr e l tkns = some (t', s) ∧ s.list = rest
```

and `motive2` carries `Seamed ps` and `PartsFollow ps rest` besides — both defined above, with
`seamed_body` already discharging the first for every body the parser hands to `parseParts`.

The decompositions the two fold motives are stated over — `juxt_decomp'` and `infxl_decomp'` —
now exist above, together with the folds themselves (`juxtFold`, `infxlFold`) and their `snoc` and
`flatten` laws. So all seven motives can now be written down.

**What is left is the induction itself**: instantiating `parseExpr.induct` with the seven motives
and discharging the cases. The three places carrying real content are as listed above; everything
they need from the grammar (`seamed_body`, `not_continuesAt_tighter_head`, `follow_of_interior`)
and from the tree shape (the two decompositions) is proved.

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
