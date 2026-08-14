import LambdaLab.Parser.IsoParser.Mixfix.Unambiguity

/-!
# Exactness: the parser consumes exactly the printed tokens

`parseExpr_exact` — print a tree, append an admissible continuation, and the parser succeeds,
returns *that* tree, and stops exactly at the seam. With `parseExpr_sound` it gives the round-trip
law `parseExpr_complete`, which is what `mixfix`'s `ok` field is.

## Why this file sits above `Unambiguity.lean`

The obligation splits cleanly in two:

* **Nothing runs long** — the parser must not eat into the continuation. That half is *not* about
  the parser at all: it says that two trees at one level cannot have one's flattening properly
  extend the other's unless the extra token continues the level. That is exactly the unique
  decomposition already proved in `Unambiguity.lean` (`udExpr`), so here it is three lines
  (`continuesAt_of_prefix`) and one packaging lemma (`exact_of_le`).
* **Nothing stops short** — the parser must not return a shorter parse when a longer one exists.
  That half *is* about the parser, and it is what the induction below establishes: at every choice
  point the printed tree is among the alternatives, and `longer` keeps the longest.

Splitting it this way is what makes the induction tractable: every case ends the same way — exhibit
one alternative that reaches the seam, then let `exact_of_le` cap the result from above.
-/

namespace LambdaLab.Parser.IsoParser.Mixfix

variable {Tok : Type} [inst : DecidableEq Tok] {G : Grammar Tok}

/-! ## Splitting an append -/

/-- Two appends that agree, with the right-hand tail no longer than the left-hand one, differ by a
middle segment. The workhorse for comparing what two parses consumed. -/
theorem append_split {α : Type} : ∀ (a b c d : List α), a ++ b = c ++ d → d.length ≤ b.length →
    ∃ mid, c = a ++ mid ∧ b = mid ++ d := by
  intro a
  induction a with
  | nil => intro b c d h _; exact ⟨c, rfl, by simpa using h⟩
  | cons x a' ih =>
      intro b c d h hlen
      cases c with
      | nil =>
          exfalso
          have := congrArg List.length h
          simp only [List.cons_append, List.length_cons, List.length_append,
            List.nil_append] at this
          omega
      | cons y c' =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h'⟩ := h
          obtain ⟨mid, hc, hb⟩ := ih b c' d h' hlen
          exact ⟨mid, by rw [hc]; rfl, hb⟩

/-! ## Nothing runs long — imported wholesale from unique decomposition -/

/-- **A proper prefix is continued.** If one tree's flattening properly extends another's *at the
same level*, the first token of the excess continues an expression at that level.

Immediately from `udExpr`: were that token not a continuation, both `[]` and the excess would stop
the level, and unique decomposition would force the two leftovers equal — but one is empty and the
other is not. -/
theorem continuesAt_of_prefix {e : G.Ent} {l : Level (G.entry e)} (t₁ t₂ : Expr G e l)
    {c : Tok} {more : List Tok} (h : t₂.flatten = t₁.flatten ++ c :: more) :
    ContinuesAt e l c := by
  by_cases hn : ContinuesAt e l c
  · exact hn
  · exfalso
    have h₁ : FollowAt e l (c :: more) := by
      intro x hx
      simp only [List.head?_cons, Option.some.injEq] at hx
      exact hx ▸ hn
    have h₂ : FollowAt e l ([] : List Tok) := by intro x hx; simp at hx
    have hs := (udExpr e l t₁ t₂ (c :: more) [] (by simp [h]) h₁ h₂).2
    exact absurd hs (by simp)

/-- **The cap.** A parse that consumed *at least* the printed tree consumed *exactly* it: any
excess would have to be continued, and the continuation stops the level. Unambiguity then names the
tree as well, so the parser's answer is the printed tree itself.

This is where the whole of the "nothing runs long" half of exactness lives. Every case of the
induction below discharges its FOLLOW obligation by calling this. -/
theorem exact_of_le {e : G.Ent} {l : Level (G.entry e)} {t t' : Expr G e l}
    {rest s : List Tok} (hF : FollowAt e l rest)
    (heq : t'.flatten ++ s = t.flatten ++ rest) (hlen : s.length ≤ rest.length) :
    t' = t ∧ s = rest := by
  obtain ⟨mid, hmid, hrest⟩ := append_split t.flatten rest t'.flatten s heq.symm hlen
  cases mid with
  | nil =>
      refine ⟨unambiguous G e l t' t (by simpa using hmid), ?_⟩
      simpa using hrest.symm
  | cons c more =>
      exact absurd (continuesAt_of_prefix t t' hmid) (hF c (by rw [hrest]; rfl))

/-- The `Parts` analogue, over one shape. Same argument, with `udParts`'s side conditions in place
of an ambient `FollowAt`. -/
theorem exact_of_le_parts {shape : List (Part G)} {p p' : Parts G shape}
    {rest s : List Tok} (hseam : Seamed shape)
    (hpf : PartsFollow shape rest) (hpf' : PartsFollow shape s)
    (heq : p'.flatten ++ s = p.flatten ++ rest) : p' = p ∧ s = rest :=
  udPartsN _ p' p s rest (Nat.le_refl _) hseam hpf' hpf heq

/-! ## Nothing stops short — what `longer` guarantees -/

omit [DecidableEq Tok] in
/-- **The longest match exists and is no shorter than the left alternative.** The bound is carried
as a parameter rather than read off the alternative, so that the alternative itself can stay a
metavariable until the goal fixes it. -/
theorem longer_left_le {α : Type} {tkns : List Tok} {a b : Option (α × RightSublist tkns)}
    {y : α × RightSublist tkns} {n : Nat} (ha : a = some y) (hy : y.2.list.length ≤ n) :
    ∃ x : α × RightSublist tkns, longer a b = some x ∧ x.2.list.length ≤ n := by
  subst ha
  cases b with
  | none => exact ⟨y, rfl, hy⟩
  | some z =>
      simp only [longer]
      split
      · rename_i hlt; exact ⟨z, rfl, by omega⟩
      · exact ⟨y, rfl, hy⟩

omit [DecidableEq Tok] in
/-- The same for the right alternative. -/
theorem longer_right_le {α : Type} {tkns : List Tok} {a b : Option (α × RightSublist tkns)}
    {y : α × RightSublist tkns} {n : Nat} (hb : b = some y) (hy : y.2.list.length ≤ n) :
    ∃ x : α × RightSublist tkns, longer a b = some x ∧ x.2.list.length ≤ n := by
  subst hb
  cases a with
  | none => exact ⟨y, rfl, hy⟩
  | some z =>
      simp only [longer]
      split
      · exact ⟨y, rfl, hy⟩
      · rename_i hlt; exact ⟨z, rfl, by omega⟩

/-! ## Small parser facts -/

omit [DecidableEq Tok] in
/-- `orElse` succeeds when either alternative does. -/
theorem orElse_ne_none {α : Type _} {A : Option α} {f : Unit → Option α}
    (h : A ≠ none ∨ f () ≠ none) : A.orElse f ≠ none := by
  cases A with
  | none => simpa [Option.orElse] using h
  | some _ => simp [Option.orElse]

omit [DecidableEq Tok] in
theorem Operator.leftRec_of_isInfxl {Ent : Type} {op : Operator Tok Ent}
    (h : op.isInfxl = true) : op.leftRec = true := by
  cases op <;> simp_all [Operator.isInfxl, Operator.leftRec]

omit [DecidableEq Tok] in
theorem Operator.leftRec_of_juxt {Ent : Type} {op : Operator Tok Ent}
    (h : op = Operator.juxt) : op.leftRec = true := by
  subst h; rfl

omit [DecidableEq Tok] in
/-- A left-recursive body is a leading hole followed by something non-empty: the fold has a shape
to parse. -/
theorem body_tail_ne_nil {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) : (Operator.body e o).tail ≠ [] := by
  cases hop : (G.entry e).operator o with
  | infxl n =>
      have hb : (Operator.body e o).tail
          = Notation.toParts (G := G) n ++ [Part.hole e (Level.tighter o)] := by
        unfold Operator.body; rw [hop]; simp
      rw [hb]; simp
  | juxt =>
      have hb : (Operator.body e o).tail = [Part.hole e (Level.tighter o)] := by
        unfold Operator.body; rw [hop]; rfl
      rw [hb]; simp
  | closed n => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | prefx n  => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | infx n   => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | infxr n  => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | postfx n => rw [hop] at hlr; simp [Operator.leftRec] at hlr

/-- **A juxtaposition chain's operands stop the base's level** — the `juxt` analogue of
`tails_followAt_tighter`, whose tails are `Parts` rather than operands. Either another operand
follows, and its first token starts an operand (so `not_continuesAt_tighter_juxt` applies), or the
final leftover does, and stopping `.tighterEq j` stops `.tighter j`. -/
theorem operands_followAt_tighter {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt)
    (xs : List (Expr G e (Level.tighter j))) {s : List Tok}
    (hs : FollowAt e (Level.tighterEq j) s) :
    FollowAt e (Level.tighter j) ((xs.map Expr.flatten).flatten ++ s) := by
  cases xs with
  | nil => simpa using FollowAt.tighter_of_tighterEq hs
  | cons x ys =>
      obtain ⟨c, ts, hct, hstart⟩ := Expr.flatten_startsOperand' x
      intro t ht
      simp only [List.map_cons, List.flatten_cons, hct, List.cons_append, List.head?_cons,
        Option.some.injEq] at ht
      subst ht
      exact not_continuesAt_tighter_juxt hj hstart

/-- **A juxtaposition fold stops at the seam.** No operand can be parsed where the continuation
begins, so `parseJuxtExtend`'s first step fails — which is how the greedy fold knows to stop. -/
theorem parseExpr_none_of_followAt_juxt {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt) {rest : List Tok}
    (hF : FollowAt e (Level.tighterEq j) rest) :
    parseExpr e (Level.tighter j) rest = none := by
  cases h : parseExpr e (Level.tighter j) rest with
  | none => rfl
  | some p =>
      obtain ⟨x, s⟩ := p
      exact absurd (parseExpr_sound e (Level.tighter j) rest x s h).symm
        (no_tree_at_followAt_juxt hj hF x s.list)

/-- **A left-associative fold stops at the seam.** The same for `parseInfixLExtend`: a body tail
begins with a token that continues at `.tighterEq o`, and the continuation does not. -/
theorem parseParts_tail_none_of_followAt {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) {rest : List Tok}
    (hF : FollowAt e (Level.tighterEq o) rest) :
    parseParts (Operator.body e o).tail rest = none := by
  cases h : parseParts (Operator.body e o).tail rest with
  | none => rfl
  | some p =>
      obtain ⟨tp, s⟩ := p
      obtain ⟨x, r, hx, -, hcont⟩ := leftRec_tail_head hlr tp
      have hs := parseParts_sound (Operator.body e o).tail rest tp s h
      exact absurd hcont (hF x (by rw [← hs, hx]; rfl))

omit [DecidableEq Tok] in
/-- A parse that starts where a *variable leaf* was printed cannot have consumed less: every tree
prints at least one token. -/
theorem leftover_le_of_var {e : G.Ent} {l : Level (G.entry e)} {t' : Expr G e l} {tok : Tok}
    {s rest : List Tok} (hsound : t'.flatten ++ s = tok :: rest) : s.length ≤ rest.length := by
  have h1 := Expr.flatten_ne_nil t'
  have h2 := congrArg List.length hsound
  cases hfl : t'.flatten with
  | nil => exact absurd hfl h1
  | cons b bs =>
      rw [hfl] at h2
      simp only [List.length_append, List.length_cons] at h2
      omega

/-! ## The induction -/

/-- **Exactness.** The parser succeeds on a printed tree followed by an admissible continuation,
returns *that* tree, and stops exactly at the seam.

The seven motives are the ones the roadmap in `Complete.lean` records, with one simplification the
roadmap could not make: because `exact_of_le` caps a parse from above, each motive asks for the
printed tree *itself* rather than for some tree with the same flattening. -/
theorem parseExpr_exact_aux (e : G.Ent) (l : Level (G.entry e)) (tkns : List Tok) :
    ∀ (t : Expr G e l) (rest : List Tok), tkns = t.flatten ++ rest → FollowAt e l rest →
      ∃ s, parseExpr e l tkns = some (t, s) ∧ s.list = rest := by
  induction e, l, tkns using parseExpr.induct
    (motive2 := fun ps tkns =>
      ∀ (p : Parts G ps) (rest : List Tok), ps ≠ [] → Seamed ps → PartsFollow ps rest →
        tkns = p.flatten ++ rest →
        ∃ s, @parseParts Tok inst G ps tkns = some (p, s) ∧ s.list = rest)
    (motive3 := fun e o hl tkns =>
      ∀ (t : Expr G e (Level.tighterEq o)) (rest : List Tok), tkns = t.flatten ++ rest →
        FollowAt e (Level.tighterEq o) rest →
        ∃ s, @parseInfixL Tok inst G e o hl tkns = some (t, s) ∧ s.list = rest)
    (motive4 := fun e o hl acc tkns =>
      ∀ (ps : List (Parts G (Operator.body e o).tail)) (rest : List Tok),
        tkns = (ps.map Parts.flatten).flatten ++ rest → FollowAt e (Level.tighterEq o) rest →
        (ps = [] → @parseInfixLExtend Tok inst G e o hl acc tkns = none) ∧
        (ps ≠ [] → ∃ s, @parseInfixLExtend Tok inst G e o hl acc tkns
          = some (infxlFold hl acc ps, s) ∧ s.list = rest))
    (motive5 := fun e j hj tkns =>
      ∀ (t : Expr G e (Level.tighterEq j)) (rest : List Tok), tkns = t.flatten ++ rest →
        FollowAt e (Level.tighterEq j) rest →
        ∃ s, @parseJuxt Tok inst G e j hj tkns = some (t, s) ∧ s.list = rest)
    (motive6 := fun e j hj acc tkns =>
      ∀ (xs : List (Expr G e (Level.tighter j))) (rest : List Tok),
        tkns = (xs.map Expr.flatten).flatten ++ rest → FollowAt e (Level.tighterEq j) rest →
        (xs = [] → @parseJuxtExtend Tok inst G e j hj acc tkns = none) ∧
        (xs ≠ [] → ∃ s, @parseJuxtExtend Tok inst G e j hj acc tkns
          = some (juxtFold hj acc xs, s) ∧ s.list = rest))
    (motive7 := fun e l cs h hrank tkns =>
      ∀ (c : (G.entry e).Op), c ∈ cs → ∀ (u : Expr G e (Level.tighterEq c)) (rest : List Tok),
        tkns = u.flatten ++ rest → FollowAt e l rest →
        ∃ t' s, @parseExprList Tok inst G e l cs h hrank tkns = some (t', s) ∧
          t'.flatten = u.flatten ∧ s.list = rest)
  -- `parseExpr.induct` introduces each motive's binders itself, so every case names what it needs
  -- with `rename_i`, counting from the end of the context.
  --
  -- ## Dispatch: the two left-recursive fixities delegate wholesale
  case case3 =>
    rename_i hjb ih5
    intro t rest heq hF
    rw [parseExpr, dif_pos hjb]
    exact ih5 t rest heq hF
  case case4 =>
    rename_i hnj hlb ih3
    intro t rest heq hF
    rw [parseExpr, dif_neg hnj, dif_pos hlb]
    exact ih3 t rest heq hF
  -- ## Bodies, part by part
  case case6 =>
    rename_i _ _ hne _ _ _
    exact absurd rfl hne
  case case7 =>
    rename_i t rest p rest' _ _ _ heq
    cases p with
    | namePart _ q =>
        cases q
        simp only [Parts.flatten, List.cons_append, List.nil_append, List.cons.injEq,
          true_and] at heq
        refine ⟨RightSublist.consTail t rest, ?_, heq⟩
        rw [parseParts]
        simp
  case case8 =>
    rename_i tk t rest hne p rest' _ _ _ heq
    cases p with
    | namePart _ q =>
        cases q
        simp only [Parts.flatten, List.cons_append, List.nil_append, List.cons.injEq] at heq
        exact absurd heq.1 hne
  case case9 =>
    rename_i tk p rest' _ _ _ heq
    cases p with
    | namePart _ q => cases q; simp [Parts.flatten] at heq
  case case10 =>
    rename_i ih1 p rest _ _ hpf heq
    cases p with
    | hole x q =>
        cases q
        simp only [Parts.flatten, List.append_nil] at heq
        obtain ⟨s, hp, hs⟩ := ih1 x rest heq hpf
        exact ⟨s, by rw [parseParts, hp]; rfl, hs⟩
  case case11 =>
    rename_i t rest ih2 p rest2 _ hseam hpf heq
    cases p with
    | namePart _ q =>
        simp only [Parts.flatten, List.cons_append, List.cons.injEq, true_and] at heq
        obtain ⟨s, hp, hs⟩ := ih2 q rest2 (by simp) hseam hpf heq
        refine ⟨(RightSublist.consTail t rest).trans s, ?_, hs⟩
        rw [parseParts]
        simp [hp]
  case case12 =>
    rename_i hne p rest2 _ _ _ heq
    cases p with
    | namePart _ q =>
        simp only [Parts.flatten, List.cons_append, List.cons.injEq] at heq
        exact absurd heq.1 hne
  case case13 =>
    rename_i p rest2 _ _ _ heq
    cases p with
    | namePart _ q => simp [Parts.flatten] at heq
  case case14 =>
    rename_i ih1 ih2 p rest2 _ hseam hpf heq
    cases p with
    | hole sub q =>
        cases q with
        | hole sub' q' => exact hseam.1.elim
        | namePart tk q' =>
            -- the seam: the name part after this hole stops the hole's own level
            obtain ⟨s₁, hp₁, hs₁⟩ :=
              ih1 sub ((Parts.namePart tk q').flatten ++ rest2)
                (by simpa only [Parts.flatten, List.cons_append, List.append_assoc] using heq)
                (by intro x hx
                    simp only [Parts.flatten, List.cons_append, List.head?_cons,
                      Option.some.injEq] at hx
                    exact hx ▸ hseam.1)
            obtain ⟨s₂, hp₂, hs₂⟩ :=
              ih2 (sub, s₁) (Parts.namePart tk q') rest2 (by simp) hseam.2 hpf hs₁
            exact ⟨s₁.trans s₂, by rw [parseParts, hp₁]; simp [hp₂], by simpa using hs₂⟩
  -- ## No candidate operators left
  case case27 =>
    rename_i hc _ _ _ _
    simp at hc
  -- ## An expression at a level: the candidate list, then the variable leaf
  case case1 =>
    rename_i ent tk0 ih7
    intro t rest heq hF
    cases t with
    | op o hc parts =>
        have hc' := hc
        obtain ⟨c, hcmem, htq⟩ := hc'
        obtain ⟨t', s, hp, hfl, hs⟩ :=
          ih7 c hcmem (Expr.op (l := Level.tighterEq c) o htq parts) rest
            (by simpa only [Expr.flatten] using heq) hF
        refine ⟨s, ?_, hs⟩
        rw [parseExpr, hp,
          unambiguous G ent Level.loosest t' (Expr.op o hc parts)
            (by simpa only [Expr.flatten] using hfl)]
        rfl
    | var tok hv =>
        have heq' : tk0 = tok :: rest := by simpa only [Expr.flatten] using heq
        subst heq'
        have hvar : parseVar ent Level.loosest (tok :: rest)
            = some (Expr.var tok hv, RightSublist.consTail tok rest) := by
          rw [parseVar]; simp [hv]
        have hne : parseExpr ent Level.loosest (tok :: rest) ≠ none := by
          rw [parseExpr]
          exact orElse_ne_none (Or.inr (by rw [hvar]; simp))
        cases hx : parseExpr ent Level.loosest (tok :: rest) with
        | none => exact absurd hx hne
        | some p =>
            obtain ⟨t', s'⟩ := p
            have hsound := parseExpr_sound ent Level.loosest (tok :: rest) t' s' hx
            obtain ⟨rfl, hs⟩ :=
              exact_of_le hF (hsound.trans heq) (leftover_le_of_var hsound)
            exact ⟨s', rfl, hs⟩
  case case2 =>
    rename_i ent tk0 a ih7
    intro t rest heq hF
    cases t with
    | op o hc parts =>
        have hc' := hc
        obtain ⟨c, hcmem, htq⟩ := tighter_iff.mp hc'
        obtain ⟨t', s, hp, hfl, hs⟩ :=
          ih7 c hcmem (Expr.op (l := Level.tighterEq c) o htq parts) rest
            (by simpa only [Expr.flatten] using heq) hF
        refine ⟨s, ?_, hs⟩
        rw [parseExpr, hp,
          unambiguous G ent (Level.tighter a) t' (Expr.op o hc parts)
            (by simpa only [Expr.flatten] using hfl)]
        rfl
    | var tok hv =>
        have heq' : tk0 = tok :: rest := by simpa only [Expr.flatten] using heq
        subst heq'
        have hvar : parseVar ent (Level.tighter a) (tok :: rest)
            = some (Expr.var tok hv, RightSublist.consTail tok rest) := by
          rw [parseVar]; simp [hv]
        have hne : parseExpr ent (Level.tighter a) (tok :: rest) ≠ none := by
          rw [parseExpr]
          exact orElse_ne_none (Or.inr (by rw [hvar]; simp))
        cases hx : parseExpr ent (Level.tighter a) (tok :: rest) with
        | none => exact absurd hx hne
        | some p =>
            obtain ⟨t', s'⟩ := p
            have hsound := parseExpr_sound ent (Level.tighter a) (tok :: rest) t' s' hx
            obtain ⟨rfl, hs⟩ :=
              exact_of_le hF (hsound.trans heq) (leftover_le_of_var hsound)
            exact ⟨s', rfl, hs⟩
  -- ## A body of its own operator, or a strictly tighter tree — whichever consumed more
  case case5 =>
    rename_i ent tk0 a hnj hnl ihExpr ihParts
    intro t rest heq hF
    have hnlr : ((G.entry ent).operator a).leftRec = false := Operator.leftRec_eq_false hnj hnl
    have key : ∃ x : Expr G ent (Level.tighterEq a) × RightSublist tk0,
        parseExpr ent (Level.tighterEq a) tk0 = some x ∧ x.2.list.length ≤ rest.length := by
      rw [parseExpr, dif_neg hnj, dif_neg hnl]
      dsimp only
      cases t with
      | op b hc parts =>
          rcases TighterEq.toTighterOrEq hc with rfl | hstrict
          · obtain ⟨s₀, hp, hs₀⟩ :=
              ihParts parts rest (Operator.body_ne_nil a) (seamed_body a hnlr)
                (partsFollow_body hc hnlr hF) (by simpa only [Expr.flatten] using heq)
            exact longer_left_le (by rw [hp]; rfl) (Nat.le_of_eq (congrArg List.length hs₀))
          · obtain ⟨s₀, hp, hs₀⟩ :=
              ihExpr (Expr.op (l := Level.tighter a) b hstrict parts) rest
                (by simpa only [Expr.flatten] using heq) (FollowAt.tighter_of_tighterEq hF)
            exact longer_right_le (by rw [hp]; rfl) (Nat.le_of_eq (congrArg List.length hs₀))
      | var tok hv =>
          obtain ⟨s₀, hp, hs₀⟩ :=
            ihExpr (Expr.var (l := Level.tighter a) tok hv) rest
              (by simpa only [Expr.flatten] using heq) (FollowAt.tighter_of_tighterEq hF)
          exact longer_right_le (by rw [hp]; rfl) (Nat.le_of_eq (congrArg List.length hs₀))
    obtain ⟨⟨t', s'⟩, hx, hlen⟩ := key
    have hsound := parseExpr_sound ent (Level.tighterEq a) tk0 t' s' hx
    obtain ⟨rfl, hs⟩ := exact_of_le hF (hsound.trans heq) hlen
    exact ⟨s', hx, hs⟩
  -- ## One candidate operator, then the rest of the list
  case case28 =>
    rename_i ent lvl tk0 c cs hcond hrk _ _ ih1 ih7 c₀ hc₀ u rest2 heq hF
    have key : ∃ x : Expr G ent lvl × RightSublist tk0,
        parseExprList ent lvl (c :: cs) hcond hrk tk0 = some x ∧
          x.2.list.length ≤ rest2.length := by
      rw [parseExprList]
      rcases List.mem_cons.mp hc₀ with rfl | hmem
      · obtain ⟨s₀, hp, hs₀⟩ :=
          ih1 u rest2 heq (FollowAt.tighten (hcond c₀ hc₀) hF)
        exact longer_left_le (by rw [hp]; rfl) (Nat.le_of_eq (congrArg List.length hs₀))
      · obtain ⟨t₀, s₀, hp, -, hs₀⟩ := ih7 c₀ hmem u rest2 heq hF
        exact longer_right_le (by rw [hp]) (Nat.le_of_eq (congrArg List.length hs₀))
    obtain ⟨⟨t', s'⟩, hx, hlen⟩ := key
    have hsound := parseExprList_sound ent lvl (c :: cs) hcond hrk tk0 t' s' hx
    obtain ⟨rfl, hs⟩ :=
      exact_of_le (t := Expr.reindex (hcond c₀ hc₀) u) hF
        (by simpa only [Expr.reindex_flatten] using hsound.trans heq) hlen
    exact ⟨_, s', hx, Expr.reindex_flatten _ u, hs⟩
  -- ## A left-associative chain: base operand, then a fold of body tails
  case case15 =>
    rename_i hl tkns hnone ih1 t rest heq hF
    exfalso
    obtain ⟨x₀, ps, rfl⟩ := infxl_decomp' hl t
    obtain ⟨s, hp, -⟩ :=
      ih1 x₀ ((ps.map Parts.flatten).flatten ++ rest)
        (by rw [heq, infxlFold_flatten, Expr.toEq_flatten, List.append_assoc])
        (tails_followAt_tighter (Operator.leftRec_of_isInfxl hl) ps hF)
    rw [hp] at hnone
    simp at hnone
  case case16 =>
    rename_i hl tkns x s1 hsome lone hnone2 ih1 ih4 t rest heq hF
    obtain ⟨x₀, ps, rfl⟩ := infxl_decomp' hl t
    obtain ⟨s₀, hp, hs₀⟩ :=
      ih1 x₀ ((ps.map Parts.flatten).flatten ++ rest)
        (by rw [heq, infxlFold_flatten, Expr.toEq_flatten, List.append_assoc])
        (tails_followAt_tighter (Operator.leftRec_of_isInfxl hl) ps hF)
    have hxx : (x₀, s₀) = (x, s1) := Option.some.inj (hp.symm.trans hsome)
    simp only [Prod.mk.injEq] at hxx
    obtain ⟨rfl, rfl⟩ := hxx
    obtain ⟨hemp, hnem⟩ := ih4 ps rest hs₀ hF
    cases ps with
    | cons p ps' => exact absurd (hnem (by simp)) (by rw [hnone2]; simp)
    | nil =>
        refine ⟨s₀, ?_, by simpa using hs₀⟩
        rw [parseInfixL, hp]
        dsimp only
        rw [hnone2]
        rfl
  case case17 =>
    rename_i hl tkns x s1 hsome lone final s2 hextsome ih1 ih4 t rest heq hF
    obtain ⟨x₀, ps, rfl⟩ := infxl_decomp' hl t
    obtain ⟨s₀, hp, hs₀⟩ :=
      ih1 x₀ ((ps.map Parts.flatten).flatten ++ rest)
        (by rw [heq, infxlFold_flatten, Expr.toEq_flatten, List.append_assoc])
        (tails_followAt_tighter (Operator.leftRec_of_isInfxl hl) ps hF)
    have hxx : (x₀, s₀) = (x, s1) := Option.some.inj (hp.symm.trans hsome)
    simp only [Prod.mk.injEq] at hxx
    obtain ⟨rfl, rfl⟩ := hxx
    obtain ⟨hemp, hnem⟩ := ih4 ps rest hs₀ hF
    cases ps with
    | nil => exact absurd (hemp rfl) (by rw [hextsome]; simp)
    | cons p ps' =>
        obtain ⟨s₃, hp₃, hs₃⟩ := hnem (by simp)
        have hff : (infxlFold (G := G) hl x₀.toEq (p :: ps'), s₃) = (final, s2) :=
          Option.some.inj (hp₃.symm.trans hextsome)
        simp only [Prod.mk.injEq] at hff
        obtain ⟨rfl, rfl⟩ := hff
        refine ⟨s₀.trans s₃, ?_, by simpa using hs₃⟩
        rw [parseInfixL, hp]
        dsimp only
        rw [hp₃]
        rfl
  case case18 =>
    rename_i hl acc tkns hnone ih2 ps rest heq hF
    have hlr := Operator.leftRec_of_isInfxl hl
    refine ⟨fun _ => by rw [parseInfixLExtend, hnone], fun hnenil => ?_⟩
    exfalso
    cases ps with
    | nil => exact hnenil rfl
    | cons p ps' =>
        obtain ⟨s₀, hp, -⟩ :=
          ih2 p ((ps'.map Parts.flatten).flatten ++ rest) (body_tail_ne_nil hlr)
            (seamed_body_tail_leftRec hlr)
            (partsFollow_body_tail hlr (tails_followAt_tighter hlr ps' hF))
            (by rw [heq]; simp [List.append_assoc])
        rw [hp] at hnone
        simp at hnone
  case case19 =>
    rename_i hl acc tkns tp s hsome acc2 hnone2 ih2 ih4 ps rest heq hF
    have hlr := Operator.leftRec_of_isInfxl hl
    cases ps with
    | nil =>
        exfalso
        simp only [List.map_nil, List.flatten_nil, List.nil_append] at heq
        subst heq
        rw [parseParts_tail_none_of_followAt hlr hF] at hsome
        simp at hsome
    | cons p ps' =>
        obtain ⟨s₀, hp, hs₀⟩ :=
          ih2 p ((ps'.map Parts.flatten).flatten ++ rest) (body_tail_ne_nil hlr)
            (seamed_body_tail_leftRec hlr)
            (partsFollow_body_tail hlr (tails_followAt_tighter hlr ps' hF))
            (by rw [heq]; simp [List.append_assoc])
        have hxx : (p, s₀) = (tp, s) := Option.some.inj (hp.symm.trans hsome)
        simp only [Prod.mk.injEq] at hxx
        obtain ⟨rfl, rfl⟩ := hxx
        obtain ⟨hemp', hnem'⟩ := ih4 ps' rest hs₀ hF
        refine ⟨fun hnil => absurd hnil (by simp), fun _ => ?_⟩
        cases ps' with
        | cons p2 ps2 => exact absurd (hnem' (by simp)) (by rw [hnone2]; simp)
        | nil =>
            refine ⟨s₀, ?_, by simpa using hs₀⟩
            rw [parseInfixLExtend, hp]
            dsimp only
            rw [hnone2]
            rfl
  case case20 =>
    rename_i hl acc tkns tp s hsome acc2 final s2 hextsome ih2 ih4 ps rest heq hF
    have hlr := Operator.leftRec_of_isInfxl hl
    cases ps with
    | nil =>
        exfalso
        simp only [List.map_nil, List.flatten_nil, List.nil_append] at heq
        subst heq
        rw [parseParts_tail_none_of_followAt hlr hF] at hsome
        simp at hsome
    | cons p ps' =>
        obtain ⟨s₀, hp, hs₀⟩ :=
          ih2 p ((ps'.map Parts.flatten).flatten ++ rest) (body_tail_ne_nil hlr)
            (seamed_body_tail_leftRec hlr)
            (partsFollow_body_tail hlr (tails_followAt_tighter hlr ps' hF))
            (by rw [heq]; simp [List.append_assoc])
        have hxx : (p, s₀) = (tp, s) := Option.some.inj (hp.symm.trans hsome)
        simp only [Prod.mk.injEq] at hxx
        obtain ⟨rfl, rfl⟩ := hxx
        obtain ⟨hemp', hnem'⟩ := ih4 ps' rest hs₀ hF
        refine ⟨fun hnil => absurd hnil (by simp), fun _ => ?_⟩
        cases ps' with
        | nil => exact absurd (hemp' rfl) (by rw [hextsome]; simp)
        | cons p2 ps2 =>
            obtain ⟨s₃, hp₃, hs₃⟩ := hnem' (by simp)
            have hff : (infxlFold (G := G) hl (Expr.infxlApp hl acc p) (p2 :: ps2), s₃)
                = (final, s2) := Option.some.inj (hp₃.symm.trans hextsome)
            simp only [Prod.mk.injEq] at hff
            obtain ⟨rfl, rfl⟩ := hff
            refine ⟨s₀.trans s₃, ?_, by simpa using hs₃⟩
            rw [parseInfixLExtend, hp]
            dsimp only
            rw [hp₃]
            rfl
  -- ## An application chain: base operand, then a fold of arguments
  case case21 =>
    rename_i hj tkns hnone ih1 t rest heq hF
    exfalso
    obtain ⟨x₀, xs, rfl⟩ := juxt_decomp' hj t
    obtain ⟨s, hp, -⟩ :=
      ih1 x₀ ((xs.map Expr.flatten).flatten ++ rest)
        (by rw [heq, juxtFold_flatten, Expr.toEq_flatten, List.append_assoc])
        (operands_followAt_tighter hj xs hF)
    rw [hp] at hnone
    simp at hnone
  case case22 =>
    rename_i hj tkns x s1 hsome lone hnone2 ih1 ih6 t rest heq hF
    obtain ⟨x₀, xs, rfl⟩ := juxt_decomp' hj t
    obtain ⟨s₀, hp, hs₀⟩ :=
      ih1 x₀ ((xs.map Expr.flatten).flatten ++ rest)
        (by rw [heq, juxtFold_flatten, Expr.toEq_flatten, List.append_assoc])
        (operands_followAt_tighter hj xs hF)
    have hxx : (x₀, s₀) = (x, s1) := Option.some.inj (hp.symm.trans hsome)
    simp only [Prod.mk.injEq] at hxx
    obtain ⟨rfl, rfl⟩ := hxx
    obtain ⟨hemp, hnem⟩ := ih6 xs rest hs₀ hF
    cases xs with
    | cons y ys => exact absurd (hnem (by simp)) (by rw [hnone2]; simp)
    | nil =>
        refine ⟨s₀, ?_, by simpa using hs₀⟩
        rw [parseJuxt, hp]
        dsimp only
        rw [hnone2]
        rfl
  case case23 =>
    rename_i hj tkns x s1 hsome lone final s2 hextsome ih1 ih6 t rest heq hF
    obtain ⟨x₀, xs, rfl⟩ := juxt_decomp' hj t
    obtain ⟨s₀, hp, hs₀⟩ :=
      ih1 x₀ ((xs.map Expr.flatten).flatten ++ rest)
        (by rw [heq, juxtFold_flatten, Expr.toEq_flatten, List.append_assoc])
        (operands_followAt_tighter hj xs hF)
    have hxx : (x₀, s₀) = (x, s1) := Option.some.inj (hp.symm.trans hsome)
    simp only [Prod.mk.injEq] at hxx
    obtain ⟨rfl, rfl⟩ := hxx
    obtain ⟨hemp, hnem⟩ := ih6 xs rest hs₀ hF
    cases xs with
    | nil => exact absurd (hemp rfl) (by rw [hextsome]; simp)
    | cons y ys =>
        obtain ⟨s₃, hp₃, hs₃⟩ := hnem (by simp)
        have hff : (juxtFold (G := G) hj x₀.toEq (y :: ys), s₃) = (final, s2) :=
          Option.some.inj (hp₃.symm.trans hextsome)
        simp only [Prod.mk.injEq] at hff
        obtain ⟨rfl, rfl⟩ := hff
        refine ⟨s₀.trans s₃, ?_, by simpa using hs₃⟩
        rw [parseJuxt, hp]
        dsimp only
        rw [hp₃]
        rfl
  case case24 =>
    rename_i hj acc tkns hnone ih1 xs rest heq hF
    refine ⟨fun _ => by rw [parseJuxtExtend, hnone], fun hnenil => ?_⟩
    exfalso
    cases xs with
    | nil => exact hnenil rfl
    | cons y ys =>
        obtain ⟨s₀, hp, -⟩ :=
          ih1 y ((ys.map Expr.flatten).flatten ++ rest)
            (by rw [heq]; simp [List.append_assoc])
            (operands_followAt_tighter hj ys hF)
        rw [hp] at hnone
        simp at hnone
  case case25 =>
    rename_i hj acc tkns x s1 hsome acc2 hnone2 ih1 ih6 xs rest heq hF
    cases xs with
    | nil =>
        exfalso
        simp only [List.map_nil, List.flatten_nil, List.nil_append] at heq
        subst heq
        rw [parseExpr_none_of_followAt_juxt hj hF] at hsome
        simp at hsome
    | cons y ys =>
        obtain ⟨s₀, hp, hs₀⟩ :=
          ih1 y ((ys.map Expr.flatten).flatten ++ rest)
            (by rw [heq]; simp [List.append_assoc])
            (operands_followAt_tighter hj ys hF)
        have hxx : (y, s₀) = (x, s1) := Option.some.inj (hp.symm.trans hsome)
        simp only [Prod.mk.injEq] at hxx
        obtain ⟨rfl, rfl⟩ := hxx
        obtain ⟨hemp', hnem'⟩ := ih6 ys rest hs₀ hF
        refine ⟨fun hnil => absurd hnil (by simp), fun _ => ?_⟩
        cases ys with
        | cons z zs => exact absurd (hnem' (by simp)) (by rw [hnone2]; simp)
        | nil =>
            refine ⟨s₀, ?_, by simpa using hs₀⟩
            rw [parseJuxtExtend, hp]
            dsimp only
            rw [hnone2]
            rfl
  case case26 =>
    rename_i hj acc tkns x s1 hsome acc2 final s2 hextsome ih1 ih6 xs rest heq hF
    cases xs with
    | nil =>
        exfalso
        simp only [List.map_nil, List.flatten_nil, List.nil_append] at heq
        subst heq
        rw [parseExpr_none_of_followAt_juxt hj hF] at hsome
        simp at hsome
    | cons y ys =>
        obtain ⟨s₀, hp, hs₀⟩ :=
          ih1 y ((ys.map Expr.flatten).flatten ++ rest)
            (by rw [heq]; simp [List.append_assoc])
            (operands_followAt_tighter hj ys hF)
        have hxx : (y, s₀) = (x, s1) := Option.some.inj (hp.symm.trans hsome)
        simp only [Prod.mk.injEq] at hxx
        obtain ⟨rfl, rfl⟩ := hxx
        obtain ⟨hemp', hnem'⟩ := ih6 ys rest hs₀ hF
        refine ⟨fun hnil => absurd hnil (by simp), fun _ => ?_⟩
        cases ys with
        | nil => exact absurd (hemp' rfl) (by rw [hextsome]; simp)
        | cons z zs =>
            obtain ⟨s₃, hp₃, hs₃⟩ := hnem' (by simp)
            have hff : (juxtFold (G := G) hj (Expr.juxtApp hj acc y) (z :: zs), s₃)
                = (final, s2) := Option.some.inj (hp₃.symm.trans hextsome)
            simp only [Prod.mk.injEq] at hff
            obtain ⟨rfl, rfl⟩ := hff
            refine ⟨s₀.trans s₃, ?_, by simpa using hs₃⟩
            rw [parseJuxtExtend, hp]
            dsimp only
            rw [hp₃]
            rfl

/-! ## The two statements the rest of the development asks for -/

/-- **Exactness**, in the leftover-erased form the round-trip law uses: parsing a printed tree
followed by an admissible continuation returns that tree, with the continuation untouched. -/
theorem parseExpr_exact {e : G.Ent} {l : Level (G.entry e)} (t : Expr G e l)
    (rest : List Tok) (hF : FollowAt e l rest) :
    runExpr e l (t.flatten ++ rest) = some (t, rest) := by
  obtain ⟨s, hp, hs⟩ := parseExpr_exact_aux e l (t.flatten ++ rest) t rest rfl hF
  rw [runExpr, hp]
  simp [hs]

/-- **The round-trip law**: printing a tree and parsing it back recovers *that* tree.

Now a direct corollary — `followAt_of_follow` weakens the computable FOLLOW to the per-level one,
and exactness does the rest. The `Unambiguous G` hypothesis this used to carry is gone: it is a
theorem (`unambiguous`), and `exact_of_le` applies it where it is needed. -/
theorem parseExpr_complete {e : G.Ent} {l : Level (G.entry e)} (t : Expr G e l) (rest : List Tok)
    (hF : HeadIn (fun t => follow e t = true) rest) :
    runExpr e l (t.flatten ++ rest) = some (t, rest) :=
  parseExpr_exact t rest (followAt_of_follow hF)

end LambdaLab.Parser.IsoParser.Mixfix
