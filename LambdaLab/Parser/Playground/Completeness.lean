import LambdaLab.Parser.Playground.Soundness

/-!
# Completeness (membership) of the list-returning parser

Because the parser returns **all** parses, completeness is a *membership* fact:
every tree's flattening is among the parses of its flattening. Crucially this
holds for an **arbitrary trailing `rest`** — the greedy maximal-munch problem
that made the single-`Option` round-trip false disappears, because "stop exactly
at `t`" is one of the alternatives the tail loops emit.

The headline is then a clean characterization that needs **no** grammar
well-formedness and **no** unambiguity (it is membership, not uniqueness):

  `mem_parse_iff : e ∈ parse tkns ↔ e.flatten = tkns`

with `⟹` from `parse_sound` and `⟸` from the core completeness lemma
`mem_parseExpr` (proved by mutual induction on the tree; the crux is the
tail-loop extension for `infix-left`/`postfix`).
-/

namespace LambdaLab.Parser.Playground

open LambdaLab.Parser

variable {G : Grammar}

/-! ## Computing `parseTree` under a known fixity

`parseTree a tkns` matches on `hf : (G.operator a).fixity`. When we are building a
membership proof for a tree `Tree.op a children`, `cases children` refines the
fixity to a concrete constructor; these lemmas then state what `parseTree a tkns`
*is* under that concrete fixity, so we can land in the right branch. They are the
membership-side analogues of the `flatten_cast_*` lemmas in `Soundness.lean`. -/

theorem parseTree_eq_closed {a : G.Op} (hf : (G.operator a).fixity = .closed)
    (tkns : List Token) :
    parseTree a tkns =
      (parseWoven (G.operator a).nameParts tkns).map
          (fun x => (Tree.op a (hf ▸ Children.closed x.1), x.2))
      ++ (parseBelow a tkns).map (fun x => (Tree.next x.1, x.2)) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_prefix {a : G.Op} (hf : (G.operator a).fixity = .prefix)
    (tkns : List Token) :
    parseTree a tkns =
      (parseWoven (G.operator a).nameParts tkns).flatMap (fun x =>
        (parseTree a x.2.list).map (fun y =>
          (Tree.op a (hf ▸ Children.prefix x.1 y.1), x.2.trans y.2)))
      ++ (parseBelow a tkns).map (fun x => (Tree.next x.1, x.2)) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_postfix {a : G.Op} (hf : (G.operator a).fixity = .postfix)
    (tkns : List Token) :
    parseTree a tkns =
      (parseBelow a tkns).flatMap (fun x => parsePostfixTail a hf (Tree.next x.1) tkns x.2) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_infixL {a : G.Op} (hf : (G.operator a).fixity = .infix .left)
    (tkns : List Token) :
    parseTree a tkns =
      (parseBelow a tkns).flatMap (fun x => parseInfixLTail a hf (Tree.next x.1) tkns x.2) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_infixR {a : G.Op} (hf : (G.operator a).fixity = .infix .right)
    (tkns : List Token) :
    parseTree a tkns =
      (parseBelow a tkns).flatMap (fun x =>
        (Tree.next x.1, x.2) ::
        (parseWoven (G.operator a).nameParts x.2.list).flatMap (fun y =>
          (parseTree a y.2.list).map (fun z =>
            (Tree.op a (hf ▸ Children.infixR x.1 y.1 z.1), x.2.trans (y.2.trans z.2))))) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_infixN {a : G.Op} (hf : (G.operator a).fixity = .infix .nonAssoc)
    (tkns : List Token) :
    parseTree a tkns =
      (parseBelow a tkns).flatMap (fun x =>
        (Tree.next x.1, x.2) ::
        (parseWoven (G.operator a).nameParts x.2.list).flatMap (fun y =>
          (parseBelow a y.2.list).map (fun z =>
            (Tree.op a (hf ▸ Children.infixN x.1 y.1 z.1), x.2.trans (y.2.trans z.2))))) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

/-! ## Landing in the right branch of the fold parsers

`parseBelowList`/`parseExprRoots` fold over the worklist with `++`. These say: if
the node `b` is in the worklist `bs` and `(t,r)` is a parse of `b`, then the
wrapped tree is among the fold's results — by induction on `bs`. -/

theorem mem_parseBelowList_of_mem {a b : G.Op} {bs : List G.Op}
    (hsub : ∀ c ∈ bs, c ∈ G.tighter a) (tkns : List Token)
    (hb : b ∈ bs) (t : Tree G b) (r : RightSublist tkns) (htb : b ∈ G.tighter a)
    (hmem : (t, r) ∈ parseTree b tkns) :
    (TreeBelow.mk b htb t, r) ∈ parseBelowList a bs hsub tkns := by
  induction bs with
  | nil => exact absurd hb List.not_mem_nil
  | cons c rest ih =>
      rw [parseBelowList]
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨(t, r), hmem, rfl⟩))
      · apply List.mem_append.mpr; right
        exact ih _ hb'

theorem mem_parseExprRoots_of_mem {r₀ : G.Op} {rs : List G.Op}
    (hsub : ∀ s ∈ rs, s ∈ G.loosest) (tkns : List Token)
    (hr₀ : r₀ ∈ rs) (t : Tree G r₀) (r : RightSublist tkns) (hl : r₀ ∈ G.loosest)
    (hmem : (t, r) ∈ parseTree r₀ tkns) :
    (Expr.mk r₀ hl t, r) ∈ parseExprRoots rs hsub tkns := by
  induction rs with
  | nil => exact absurd hr₀ List.not_mem_nil
  | cons c rest ih =>
      rw [parseExprRoots]
      rcases List.mem_cons.mp hr₀ with rfl | hr'
      · exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨(t, r), hmem, rfl⟩))
      · apply List.mem_append.mpr; right
        exact ih _ hr'

/-! ## The tail-loop crux

`parseInfixLTail`/`parsePostfixTail` emit the stop case `(acc, r)` and every
further fold. Completeness for the left-recursive fixities is an induction on the
left spine. We package the spine induction as a standalone lemma over the
accumulator: from `acc` with leftover `r`, if the remaining spine flattens to a
prefix of `r.list`, the corresponding folded tree is reached. -/

/-- Stop case: the accumulator is always among the tail's outputs. -/
theorem mem_parseInfixLTail_stop {a : G.Op} (hf : (G.operator a).fixity = .infix .left)
    (acc : Tree G a) (tkns0 : List Token) (r : RightSublist tkns0) :
    (acc, r) ∈ parseInfixLTail a hf acc tkns0 r := by
  rw [parseInfixLTail]; exact List.mem_cons_self

theorem mem_parsePostfixTail_stop {a : G.Op} (hf : (G.operator a).fixity = .postfix)
    (acc : Tree G a) (tkns0 : List Token) (r : RightSublist tkns0) :
    (acc, r) ∈ parsePostfixTail a hf acc tkns0 r := by
  rw [parsePostfixTail]; exact List.mem_cons_self

/-- **Extension (the crux).** If `(acc', r')` is reachable in the left-assoc
tail loop, then folding one more occurrence of `a` (its name-parts parsed by
`wp`, its right operand by `bp`) is *also* reachable — because that fold's stop
case is `flatMap`-ped in. Well-founded recursion on `r.list.length` walks down
the part of the spine already consumed to find where `(acc', r')` sat, then steps
once more. The completeness inputs (`hwp`, `hbp`) are supplied by the caller. -/
theorem infixLTail_extend {a : G.Op} (hf : (G.operator a).fixity = .infix .left)
    (acc : Tree G a) (tkns0 : List Token) (r : RightSublist tkns0)
    (acc' : Tree G a) (r' : RightSublist tkns0)
    (hmem : (acc', r') ∈ parseInfixLTail a hf acc tkns0 r)
    (wp : Woven G (G.operator a).nameParts × RightSublist r'.list)
    (hwp : wp ∈ parseWoven (G.operator a).nameParts r'.list)
    (bp : TreeBelow G a × RightSublist wp.2.list)
    (hbp : bp ∈ parseBelow a wp.2.list) :
    (Tree.op a (hf ▸ Children.infixL acc' wp.1 bp.1),
        r'.trans (wp.2.trans bp.2)) ∈ parseInfixLTail a hf acc tkns0 r := by
  rw [parseInfixLTail] at hmem ⊢
  rcases List.mem_cons.mp hmem with heq | hmem'
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
    apply List.mem_cons.mpr; right
    apply List.mem_flatMap.mpr
    refine ⟨wp, hwp, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨bp, hbp, ?_⟩
    rw [parseInfixLTail]; exact List.mem_cons_self
  · apply List.mem_cons.mpr; right
    rcases List.mem_flatMap.mp hmem' with ⟨x, hx, hy⟩
    rcases List.mem_flatMap.mp hy with ⟨y, hy2, hz⟩
    apply List.mem_flatMap.mpr
    refine ⟨x, hx, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨y, hy2, ?_⟩
    exact infixLTail_extend hf _ tkns0 _ acc' r' hz wp hwp bp hbp
termination_by r.list.length
decreasing_by
  simp_wf
  have := x.2.length_lt
  have := y.2.length_lt
  simp only [RightSublist.trans]; omega

/-- The postfix analogue of `infixLTail_extend`. -/
theorem postfixTail_extend {a : G.Op} (hf : (G.operator a).fixity = .postfix)
    (acc : Tree G a) (tkns0 : List Token) (r : RightSublist tkns0)
    (acc' : Tree G a) (r' : RightSublist tkns0)
    (hmem : (acc', r') ∈ parsePostfixTail a hf acc tkns0 r)
    (wp : Woven G (G.operator a).nameParts × RightSublist r'.list)
    (hwp : wp ∈ parseWoven (G.operator a).nameParts r'.list) :
    (Tree.op a (hf ▸ Children.postfix acc' wp.1),
        r'.trans wp.2) ∈ parsePostfixTail a hf acc tkns0 r := by
  rw [parsePostfixTail] at hmem ⊢
  rcases List.mem_cons.mp hmem with heq | hmem'
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
    apply List.mem_cons.mpr; right
    apply List.mem_flatMap.mpr
    refine ⟨wp, hwp, ?_⟩
    rw [parsePostfixTail]; exact List.mem_cons_self
  · apply List.mem_cons.mpr; right
    rcases List.mem_flatMap.mp hmem' with ⟨x, hx, hz⟩
    apply List.mem_flatMap.mpr
    refine ⟨x, hx, ?_⟩
    exact postfixTail_extend hf _ tkns0 _ acc' r' hz wp hwp
termination_by r.list.length
decreasing_by
  simp_wf
  have := x.2.length_lt
  simp only [RightSublist.trans]; omega

/-- A below-parse `(tb, r)` always yields the fall-through tree `Tree.next tb` as
a parse — in every fixity branch (directly in the `++`-right for
closed/prefix/infixR/infixN, as the tail-loop stop case for postfix/infixL). -/
theorem mem_parseTree_next (a : G.Op) (tkns : List Token) (tb : TreeBelow G a)
    (r : RightSublist tkns) (hmem : (tb, r) ∈ parseBelow a tkns) :
    (Tree.next tb, r) ∈ parseTree a tkns := by
  rw [parseTree]
  split
  · exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨(tb, r), hmem, rfl⟩))
  · exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨(tb, r), hmem, rfl⟩))
  · apply List.mem_flatMap.mpr
    refine ⟨(tb, r), hmem, ?_⟩
    rw [parsePostfixTail]; exact List.mem_cons_self
  · apply List.mem_flatMap.mpr
    refine ⟨(tb, r), hmem, ?_⟩
    rw [parseInfixLTail]; exact List.mem_cons_self
  · exact List.mem_flatMap.mpr ⟨(tb, r), hmem, List.mem_cons_self⟩
  · exact List.mem_flatMap.mpr ⟨(tb, r), hmem, List.mem_cons_self⟩

/-! ## The completeness recursion (structural, via `Tree.rec`)

Completeness of all five parsers is proved together by structural recursion on
the mutual tree family, using the generated recursor `Tree.rec` (a plain
`mutual`/`termination_by structural` block does not see the operand subtrees as
decreasing because the fixity-indexed `Children` constructor must be reached
through `Children.casesOn`, which hides the subterm relation). Each motive
threads the equation `flatten ++ rest = tkns` so the appends re-associate freely;
the left-recursive fixities use `infixLTail_extend`/`postfixTail_extend` on the
spine IH. The `Children` motive is stated with the fixity cast `heq ▸ c` so that
`Tree.op a' (heq ▸ c)` is well-typed for an *arbitrary* fixity `f`. -/

/-- **Core completeness.** Every expression's flattening (followed by any `rest`)
is among the parses, with `rest` as the leftover. Proved by structural recursion
on the mutual tree family via `Tree.rec`. -/
theorem mem_parseExpr (tkns : List Token) (e : Expr G) (rest : List Token)
    (h : e.flatten ++ rest = tkns) :
    ∃ r : RightSublist tkns, (e, r) ∈ parseExpr tkns ∧ r.list = rest := by
  refine @Expr.rec G
      (motive_1 := fun a t => ∀ tkns rest, t.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (t, r) ∈ parseTree a tkns ∧ r.list = rest)
      (motive_2 := fun a b => ∀ tkns rest, b.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (b, r) ∈ parseBelow a tkns ∧ r.list = rest)
      (motive_3 := fun a f c => ∀ (heq : (G.operator a).fixity = f) tkns rest,
        (Tree.op a (heq ▸ c)).flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (Tree.op a (heq ▸ c), r) ∈ parseTree a tkns ∧ r.list = rest)
      (motive_4 := fun parts w => ∀ tkns rest, w.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (w, r) ∈ parseWoven parts tkns ∧ r.list = rest)
      (motive_5 := fun e => ∀ tkns rest, e.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (e, r) ∈ parseExpr tkns ∧ r.list = rest)
      ?op ?next ?mk ?closed ?«prefix» ?«postfix» ?infixL ?infixR ?infixN ?last ?cons ?expr
      e tkns rest h
  -- Tree.op: delegate to the Children motive at `heq := rfl`
  case op => intro a children ih tkns rest h; exact ih rfl tkns rest h
  -- Tree.next: fall-through (every fixity branch)
  case next =>
    intro a tb ih tkns rest h
    obtain ⟨r, hmem, hr⟩ := ih tkns rest (by simpa [Tree.flatten] using h)
    exact ⟨r, mem_parseTree_next a tkns tb r hmem, hr⟩
  -- TreeBelow.mk
  case mk =>
    intro a c hc t ih tkns rest h
    obtain ⟨r, hmem, hr⟩ := ih tkns rest (by simpa [TreeBelow.flatten] using h)
    exact ⟨r, by unfold parseBelow; exact mem_parseBelowList_of_mem _ tkns hc t r hc hmem, hr⟩
  -- Children.closed
  case closed =>
    intro a w ihw heq tkns rest hflat
    rw [flatten_cast_closed heq] at hflat
    obtain ⟨rw_, hmem, hrw⟩ := ihw tkns rest hflat
    refine ⟨rw_, ?_, hrw⟩
    rw [parseTree_eq_closed heq]
    exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨(w, rw_), hmem, rfl⟩))
  -- Children.prefix
  case «prefix» =>
    intro a w t' ihw iht heq tkns rest hflat
    rw [flatten_cast_prefix heq, List.append_assoc] at hflat
    obtain ⟨rw_, hmemw, hrw⟩ := ihw tkns (t'.flatten ++ rest) hflat
    obtain ⟨rt, hmemt, hrt⟩ := iht rw_.list rest hrw.symm
    refine ⟨rw_.trans rt, ?_, by simpa [RightSublist.trans] using hrt⟩
    rw [parseTree_eq_prefix heq]
    apply List.mem_append.mpr; left
    apply List.mem_flatMap.mpr
    refine ⟨(w, rw_), hmemw, ?_⟩
    exact List.mem_map.mpr ⟨(t', rt), hmemt, rfl⟩
  -- Children.postfix (spine: iht is the IH for the left operand `t'`)
  case «postfix» =>
    intro a t' w iht ihw heq tkns rest hflat
    rw [flatten_cast_postfix heq, List.append_assoc] at hflat
    obtain ⟨rt, hmemt, hrt⟩ := iht tkns (w.flatten ++ rest) hflat
    obtain ⟨rw_, hmemw, hrw⟩ := ihw rt.list rest hrt.symm
    rw [parseTree_eq_postfix heq] at hmemt
    rcases List.mem_flatMap.mp hmemt with ⟨x, hx, hxt⟩
    refine ⟨rt.trans rw_, ?_, by simpa [RightSublist.trans] using hrw⟩
    rw [parseTree_eq_postfix heq]
    apply List.mem_flatMap.mpr
    refine ⟨x, hx, ?_⟩
    exact postfixTail_extend heq (Tree.next x.1) tkns x.2 t' rt hxt (w, rw_) hmemw
  -- Children.infixL (spine: ihl is the IH for the left operand `l`)
  case infixL =>
    intro a l w r ihl ihw ihr heq tkns rest hflat
    rw [flatten_cast_infixL heq, List.append_assoc, List.append_assoc] at hflat
    obtain ⟨rl, hmeml, hrl⟩ := ihl tkns (w.flatten ++ (r.flatten ++ rest)) hflat
    obtain ⟨rw_, hmemw, hrw⟩ := ihw rl.list (r.flatten ++ rest) hrl.symm
    obtain ⟨rr, hmemr, hrr⟩ := ihr rw_.list rest hrw.symm
    rw [parseTree_eq_infixL heq] at hmeml
    rcases List.mem_flatMap.mp hmeml with ⟨x, hx, hxl⟩
    refine ⟨rl.trans (rw_.trans rr), ?_, by simpa [RightSublist.trans] using hrr⟩
    rw [parseTree_eq_infixL heq]
    apply List.mem_flatMap.mpr
    refine ⟨x, hx, ?_⟩
    exact infixLTail_extend heq (Tree.next x.1) tkns x.2 l rl hxl (w, rw_) hmemw (r, rr) hmemr
  -- Children.infixR
  case infixR =>
    intro a l w r ihl ihw ihr heq tkns rest hflat
    rw [flatten_cast_infixR heq, List.append_assoc, List.append_assoc] at hflat
    obtain ⟨rl, hmeml, hrl⟩ := ihl tkns (w.flatten ++ (r.flatten ++ rest)) hflat
    obtain ⟨rw_, hmemw, hrw⟩ := ihw rl.list (r.flatten ++ rest) hrl.symm
    obtain ⟨rr, hmemr, hrr⟩ := ihr rw_.list rest hrw.symm
    refine ⟨rl.trans (rw_.trans rr), ?_, by simpa [RightSublist.trans] using hrr⟩
    rw [parseTree_eq_infixR heq]
    apply List.mem_flatMap.mpr
    refine ⟨(l, rl), hmeml, ?_⟩
    apply List.mem_cons.mpr; right
    apply List.mem_flatMap.mpr
    refine ⟨(w, rw_), hmemw, ?_⟩
    exact List.mem_map.mpr ⟨(r, rr), hmemr, rfl⟩
  -- Children.infixN
  case infixN =>
    intro a l w r ihl ihw ihr heq tkns rest hflat
    rw [flatten_cast_infixN heq, List.append_assoc, List.append_assoc] at hflat
    obtain ⟨rl, hmeml, hrl⟩ := ihl tkns (w.flatten ++ (r.flatten ++ rest)) hflat
    obtain ⟨rw_, hmemw, hrw⟩ := ihw rl.list (r.flatten ++ rest) hrl.symm
    obtain ⟨rr, hmemr, hrr⟩ := ihr rw_.list rest hrw.symm
    refine ⟨rl.trans (rw_.trans rr), ?_, by simpa [RightSublist.trans] using hrr⟩
    rw [parseTree_eq_infixN heq]
    apply List.mem_flatMap.mpr
    refine ⟨(l, rl), hmeml, ?_⟩
    apply List.mem_cons.mpr; right
    apply List.mem_flatMap.mpr
    refine ⟨(w, rw_), hmemw, ?_⟩
    exact List.mem_map.mpr ⟨(r, rr), hmemr, rfl⟩
  -- Woven.cons
  case cons =>
    intro restParts tk e w' ihe ihw tkns rest h
    obtain ⟨p, ps, hps⟩ : ∃ p ps, restParts = p :: ps := by
      cases w' with
      | last tk2 => exact ⟨tk2, [], rfl⟩
      | cons tk2 _ _ => exact ⟨tk2, _, rfl⟩
    subst hps
    simp only [Woven.flatten, List.append_assoc, List.cons_append, List.nil_append] at h
    subst h
    obtain ⟨re, hmeme, hre⟩ := ihe (e.flatten ++ (w'.flatten ++ rest)) (w'.flatten ++ rest) rfl
    obtain ⟨rw2, hmemw2, hrw2⟩ := ihw re.list rest (by rw [hre])
    refine ⟨(RightSublist.cons tk _).trans (re.trans rw2), ?_, by
      simpa [RightSublist.trans, RightSublist.cons] using hrw2⟩
    show (Woven.cons tk e w', _) ∈
      parseWoven (tk :: p :: ps) (tk :: (e.flatten ++ (w'.flatten ++ rest)))
    rw [parseWoven.eq_2, if_pos rfl]
    apply List.mem_flatMap.mpr
    refine ⟨(e, re), hmeme, ?_⟩
    exact List.mem_map.mpr ⟨(w', rw2), hmemw2, rfl⟩
  -- Woven.last
  case last =>
    intro tk tkns rest h
    simp only [Woven.flatten] at h
    subst h
    refine ⟨RightSublist.cons tk rest, ?_, rfl⟩
    show (Woven.last tk, RightSublist.cons tk rest) ∈ parseWoven [tk] (tk :: rest)
    rw [parseWoven.eq_1, if_pos rfl]
    exact List.mem_singleton.mpr rfl
  -- Expr.mk
  case expr =>
    intro r₀ hl t iht tkns rest h
    obtain ⟨r, hmem, hr⟩ := iht tkns rest (by simpa [Expr.flatten] using h)
    exact ⟨r, by unfold parseExpr; exact mem_parseExprRoots_of_mem _ tkns hl t r hl hmem, hr⟩

/-- Completeness: every expression's flattening parses (fully) back to it. -/
theorem parse_complete (e : Expr G) : e ∈ parse (G := G) e.flatten := by
  obtain ⟨r, hmem, hr⟩ := mem_parseExpr e.flatten e [] (List.append_nil _)
  unfold parse
  exact List.mem_filterMap.mpr ⟨(e, r), hmem, by simp [hr]⟩

/-- Headline: `parse` accepts exactly the flattenings (membership form). -/
theorem mem_parse_iff {tkns : List Token} {e : Expr G} :
    e ∈ parse (G := G) tkns ↔ e.flatten = tkns := by
  constructor
  · intro hmem
    unfold parse at hmem
    obtain ⟨x, hx, hgx⟩ := List.mem_filterMap.mp hmem
    split at hgx
    · rename_i hnil
      obtain rfl := Option.some.inj hgx
      have := parseExpr_sound tkns x.1 x.2 hx
      simpa [hnil] using this
    · exact absurd hgx (by simp)
  · intro h; subst h; exact parse_complete e

end LambdaLab.Parser.Playground
