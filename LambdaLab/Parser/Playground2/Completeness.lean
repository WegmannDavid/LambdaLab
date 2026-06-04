import LambdaLab.Parser.Playground2.Soundness

/-!
# Completeness (membership) of the list-returning parser

Because the parser returns **all** parses, completeness is a *membership* fact:
every tree's flattening is among the parses of its flattening, for an
**arbitrary trailing `rest`**.

With the strictly-tighter (spine) tree encoding the parser's chaining functions
(`parsePrefixStack`/`parsePostfixTail`/`parseInfixTail`) build the spine by plain
structural recursion, so completeness for the chaining fixities is itself a plain
structural step — no tail-loop extension lemma is needed.

  `mem_parse_iff : e ∈ parse tkns ↔ e.flatten = tkns`

with `⟹` from `parse_sound` and `⟸` from the core completeness lemma
`mem_parseTree_complete` (structural recursion over the whole tree family via
`Tree.rec`, with the per-level parse function selected by `parseAtLevel`).
-/

namespace LambdaLab.Parser.Playground2

open LambdaLab.Parser

variable {G : Grammar}

/-- The parse function appropriate to a level: parsing at `.tighterEq a` is
`parseTree a`, at `.tighter a` is `parseBelow a`, at `.loosest` is `parseExpr`.
This lets a single `Tree`-motive cover all three former tree families. -/
def parseAtLevel (l : Level G) (tkns : List Token) : List (Tree G l × RightSublist tkns) :=
  match l with
  | .tighterEq a => parseTree a tkns
  | .tighter a   => parseBelow a tkns
  | .loosest     => parseExpr tkns

/-! ## Computing `parseTree` under a known fixity -/

theorem parseTree_eq_closed {a : G.Op} (hf : (G.operator a).fixity = .closed)
    (tkns : List Token) :
    parseTree a tkns =
      (parseWoven (G.operator a).nameParts tkns).map
          (fun x => (Tree.opSelf a (hf ▸ Children.closed x.1), x.2))
      ++ (parseBelow a tkns).map (fun x => (x.1.lift, x.2)) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_prefix {a : G.Op} (hf : (G.operator a).fixity = .prefix)
    (tkns : List Token) :
    parseTree a tkns =
      (parsePrefixStack a tkns).map (fun x => (Tree.opSelf a (hf ▸ Children.prefix x.1), x.2))
      ++ (parseBelow a tkns).map (fun x => (x.1.lift, x.2)) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_postfix {a : G.Op} (hf : (G.operator a).fixity = .postfix)
    (tkns : List Token) :
    parseTree a tkns =
      (parseBelow a tkns).flatMap (fun x =>
        (x.1.lift, x.2) ::
        (parsePostfixTail a x.2.list).map (fun y =>
          (Tree.opSelf a (hf ▸ Children.postfix x.1 y.1), x.2.trans y.2))) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_infixL {a : G.Op} (hf : (G.operator a).fixity = .infix .left)
    (tkns : List Token) :
    parseTree a tkns =
      (parseBelow a tkns).flatMap (fun x =>
        (x.1.lift, x.2) ::
        (parseInfixTail a x.2.list).map (fun y =>
          (Tree.opSelf a (hf ▸ Children.infixL x.1 y.1), x.2.trans y.2))) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_infixR {a : G.Op} (hf : (G.operator a).fixity = .infix .right)
    (tkns : List Token) :
    parseTree a tkns =
      (parseBelow a tkns).flatMap (fun x =>
        (x.1.lift, x.2) ::
        (parseInfixTail a x.2.list).map (fun y =>
          (Tree.opSelf a (hf ▸ Children.infixR x.1 y.1), x.2.trans y.2))) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_infixN {a : G.Op} (hf : (G.operator a).fixity = .infix .nonAssoc)
    (tkns : List Token) :
    parseTree a tkns =
      (parseBelow a tkns).flatMap (fun x =>
        (x.1.lift, x.2) ::
        (parseWoven (G.operator a).nameParts x.2.list).flatMap (fun y =>
          (parseBelow a y.2.list).map (fun z =>
            (Tree.opSelf a (hf ▸ Children.infixN x.1 y.1 z.1), x.2.trans (y.2.trans z.2))))) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

/-! ## Landing in the right branch of the fold parsers -/

/-- A parse `(u, r) ∈ parseTree b` with `b ∈ tighter a` lands (reindexed to the
strictly-tighter level) in `parseBelowList a bs` for any `bs ∋ b`. -/
theorem mem_parseBelowList_of_mem {a b : G.Op} {bs : List G.Op}
    (hsub : ∀ c ∈ bs, c ∈ G.tighter a) (tkns : List Token)
    (hb : b ∈ bs) (htb : b ∈ G.tighter a) (u : Tree G (.tighterEq b)) (r : RightSublist tkns)
    (hmem : (u, r) ∈ parseTree b tkns) :
    (Tree.reindex (l := Level.tighterEq b) (l' := Level.tighter a)
        (fun _ hc => (tighter_of_mem_tighterEq htb hc : Tighter G.tighter a _)) u, r)
      ∈ parseBelowList a bs hsub tkns := by
  induction bs with
  | nil => exact absurd hb List.not_mem_nil
  | cons c rest ih =>
      rw [parseBelowList]
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨(u, r), hmem, rfl⟩))
      · exact List.mem_append.mpr (.inr (ih _ hb'))

/-- A parse `(u, r) ∈ parseTree r₀` with `r₀ ∈ loosest` lands (reindexed to the
loosest level) in `parseExprRoots rs` for any `rs ∋ r₀`. -/
theorem mem_parseExprRoots_of_mem {r₀ : G.Op} {rs : List G.Op}
    (hsub : ∀ s ∈ rs, s ∈ G.loosest) (tkns : List Token)
    (hr₀ : r₀ ∈ rs) (hl : r₀ ∈ G.loosest) (u : Tree G (.tighterEq r₀)) (r : RightSublist tkns)
    (hmem : (u, r) ∈ parseTree r₀ tkns) :
    (Tree.reindex (l := Level.tighterEq r₀) (l' := Level.loosest)
        (fun _ hc => (⟨r₀, hl, hc⟩ : ∃ s, s ∈ G.loosest ∧ TighterEq G.tighter s _)) u, r)
      ∈ parseExprRoots rs hsub tkns := by
  induction rs with
  | nil => exact absurd hr₀ List.not_mem_nil
  | cons c rest ih =>
      rw [parseExprRoots]
      rcases List.mem_cons.mp hr₀ with rfl | hr'
      · exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨(u, r), hmem, rfl⟩))
      · exact List.mem_append.mpr (.inr (ih _ hr'))

/-- A below-parse `(tb, r)` always yields the fall-through tree `tb.lift` as a
parse — in every fixity branch (directly in the `++`-right for closed/prefix, as
the cons head of the flatMap for postfix/infix). -/
theorem mem_parseTree_lift (a : G.Op) (tkns : List Token) (tb : Tree G (.tighter a))
    (r : RightSublist tkns) (hmem : (tb, r) ∈ parseBelow a tkns) :
    (tb.lift, r) ∈ parseTree a tkns := by
  rw [parseTree]
  split
  · exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨(tb, r), hmem, rfl⟩))
  · exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨(tb, r), hmem, rfl⟩))
  · exact List.mem_flatMap.mpr ⟨(tb, r), hmem, List.mem_cons_self⟩
  · exact List.mem_flatMap.mpr ⟨(tb, r), hmem, List.mem_cons_self⟩
  · exact List.mem_flatMap.mpr ⟨(tb, r), hmem, List.mem_cons_self⟩
  · exact List.mem_flatMap.mpr ⟨(tb, r), hmem, List.mem_cons_self⟩

/-- `parseBelow`-flavoured corollary of `mem_parseBelowList_of_mem`. -/
theorem mem_parseBelow_of_mem {a b : G.Op} (htb : b ∈ G.tighter a) (tkns : List Token)
    (u : Tree G (.tighterEq b)) (r : RightSublist tkns) (hmem : (u, r) ∈ parseTree b tkns) :
    (Tree.reindex (l := Level.tighterEq b) (l' := Level.tighter a)
        (fun _ hc => (tighter_of_mem_tighterEq htb hc : Tighter G.tighter a _)) u, r)
      ∈ parseBelow a tkns := by
  rw [parseBelow]
  exact mem_parseBelowList_of_mem (fun _ h => h) tkns htb htb u r hmem

/-- `parseExpr`-flavoured corollary of `mem_parseExprRoots_of_mem`. -/
theorem mem_parseExpr_of_mem {r₀ : G.Op} (hl : r₀ ∈ G.loosest) (tkns : List Token)
    (u : Tree G (.tighterEq r₀)) (r : RightSublist tkns) (hmem : (u, r) ∈ parseTree r₀ tkns) :
    (Tree.reindex (l := Level.tighterEq r₀) (l' := Level.loosest)
        (fun _ hc => (⟨r₀, hl, hc⟩ : ∃ s, s ∈ G.loosest ∧ TighterEq G.tighter s _)) u, r)
      ∈ parseExpr tkns := by
  rw [parseExpr]
  exact mem_parseExprRoots_of_mem (fun _ h => h) tkns hl hl u r hmem

/-- A parse at a tighter node `b` lifts to a parse at any looser node `a` with
`TighterEq a b` — by walking the `tighter`-path one rung at a time
(`mem_parseTree_lift` per rung). Reindexes collapse by proof-irrelevance once the
tree is exposed as a constructor (`cases t`). -/
theorem mem_parseTree_reindex {a b : G.Op} (tkns : List Token)
    (hab : TighterEq G.tighter a b) :
    ∀ (t : Tree G (.tighterEq b)) (r : RightSublist tkns), (t, r) ∈ parseTree b tkns →
      (Tree.reindexEq hab t, r) ∈ parseTree a tkns := by
  induction hab with
  | refl => intro t r hmem; cases t with | op a' hc ch => exact hmem
  | step hb h' ih =>
      intro t r hmem
      cases t with
      | op a' hc ch =>
          exact mem_parseTree_lift _ tkns _ r
            (mem_parseBelow_of_mem hb tkns _ r (ih _ r hmem))

/-- The key transport: a parse `(u, r) ∈ parseTree a` reindexed to any level `l`
that `a` satisfies (`hc : Level.condition l a`) lands in `parseAtLevel l`. Unifies
the three former membership steps (reindex / below / roots) into one. -/
theorem mem_parseAtLevel_reindex {l : Level G} {a : G.Op} (hc : Level.condition l a)
    (tkns : List Token) (u : Tree G (.tighterEq a)) (r : RightSublist tkns)
    (hmem : (u, r) ∈ parseTree a tkns) :
    (u.reindex (l := Level.tighterEq a) (l' := l) (fun _ hb => Level.condition_trans hc hb), r)
      ∈ parseAtLevel l tkns := by
  cases u with
  | op a'' hcw ch =>
    cases l with
    | tighterEq a' => exact mem_parseTree_reindex tkns hc _ r hmem
    | tighter a' =>
        obtain ⟨c, hcm, hca⟩ := hc.split
        exact mem_parseBelow_of_mem hcm tkns _ r (mem_parseTree_reindex tkns hca _ r hmem)
    | loosest =>
        obtain ⟨r₀, hr₀, hr₀a⟩ := hc
        exact mem_parseExpr_of_mem hr₀ tkns _ r (mem_parseTree_reindex tkns hr₀a _ r hmem)

/-! ## The completeness recursion (structural, via `Tree.rec`) -/

/-- **Core completeness.** Every tree's flattening (followed by any `rest`) is
among the parses at its level, with `rest` as the leftover. Proved by structural
recursion on the mutual tree family via `Tree.rec`. -/
theorem mem_parseTree_complete {l : Level G} (t : Tree G l) (tkns rest : List Token)
    (h : t.flatten ++ rest = tkns) :
    ∃ r : RightSublist tkns, (t, r) ∈ parseAtLevel l tkns ∧ r.list = rest := by
  refine @Tree.rec G
      (motive_1 := fun l t => ∀ tkns rest, t.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (t, r) ∈ parseAtLevel l tkns ∧ r.list = rest)
      (motive_2 := fun a f c => ∀ (heq : (G.operator a).fixity = f) tkns rest,
        (Tree.opSelf a (heq ▸ c)).flatten ++ rest = tkns →
        ∃ r : RightSublist tkns,
          (Tree.opSelf a (heq ▸ c), r) ∈ parseTree a tkns ∧ r.list = rest)
      (motive_3 := fun a ps => ∀ tkns rest, ps.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (ps, r) ∈ parsePrefixStack a tkns ∧ r.list = rest)
      (motive_4 := fun a pt => ∀ tkns rest, pt.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (pt, r) ∈ parsePostfixTail a tkns ∧ r.list = rest)
      (motive_5 := fun a tl => ∀ tkns rest, tl.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (tl, r) ∈ parseInfixTail a tkns ∧ r.list = rest)
      (motive_6 := fun parts w => ∀ tkns rest, w.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (w, r) ∈ parseWoven parts tkns ∧ r.list = rest)
      ?op ?closed ?cpre ?cpost ?ciL ?ciR ?ciN ?psl ?psm ?ptl ?ptc ?itl ?itc ?wl ?wc
      l t tkns rest h
  -- Tree.op: children parse at the op's own node; transport up to level `l`.
  case op =>
    intro lev a hc ch ih tkns rest hflat
    have hflat' : (Tree.opSelf a ch).flatten ++ rest = tkns := by
      simpa only [Tree.opSelf_flatten, Tree.flatten] using hflat
    obtain ⟨r, hmem, hr⟩ := ih rfl tkns rest hflat'
    exact ⟨r, mem_parseAtLevel_reindex hc tkns _ r hmem, hr⟩
  -- Children.closed
  case closed =>
    intro a w ihw heq tkns rest hflat
    rw [flatten_cast_closed heq] at hflat
    obtain ⟨rw_, hmem, hrw⟩ := ihw tkns rest hflat
    refine ⟨rw_, ?_, hrw⟩
    rw [parseTree_eq_closed heq]
    exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨(w, rw_), hmem, rfl⟩))
  -- Children.prefix
  case cpre =>
    intro a ps ihps heq tkns rest hflat
    rw [flatten_cast_prefix heq] at hflat
    obtain ⟨r, hmem, hr⟩ := ihps tkns rest hflat
    refine ⟨r, ?_, hr⟩
    rw [parseTree_eq_prefix heq]
    exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨(ps, r), hmem, rfl⟩))
  -- Children.postfix
  case cpost =>
    intro a tb pt ihtb ihpt heq tkns rest hflat
    rw [flatten_cast_postfix heq, List.append_assoc] at hflat
    obtain ⟨rt, hmemt, hrt⟩ := ihtb tkns (pt.flatten ++ rest) hflat
    obtain ⟨rp, hmemp, hrp⟩ := ihpt rt.list rest hrt.symm
    refine ⟨rt.trans rp, ?_, by simpa [RightSublist.trans] using hrp⟩
    rw [parseTree_eq_postfix heq]
    apply List.mem_flatMap.mpr
    refine ⟨(tb, rt), hmemt, ?_⟩
    apply List.mem_cons.mpr; right
    exact List.mem_map.mpr ⟨(pt, rp), hmemp, rfl⟩
  -- Children.infixL
  case ciL =>
    intro a hd tl ihhd ihtl heq tkns rest hflat
    rw [flatten_cast_infixL heq, List.append_assoc] at hflat
    obtain ⟨rh, hmemh, hrh⟩ := ihhd tkns (tl.flatten ++ rest) hflat
    obtain ⟨rt, hmemt, hrt⟩ := ihtl rh.list rest hrh.symm
    refine ⟨rh.trans rt, ?_, by simpa [RightSublist.trans] using hrt⟩
    rw [parseTree_eq_infixL heq]
    apply List.mem_flatMap.mpr
    refine ⟨(hd, rh), hmemh, ?_⟩
    apply List.mem_cons.mpr; right
    exact List.mem_map.mpr ⟨(tl, rt), hmemt, rfl⟩
  -- Children.infixR
  case ciR =>
    intro a hd tl ihhd ihtl heq tkns rest hflat
    rw [flatten_cast_infixR heq, List.append_assoc] at hflat
    obtain ⟨rh, hmemh, hrh⟩ := ihhd tkns (tl.flatten ++ rest) hflat
    obtain ⟨rt, hmemt, hrt⟩ := ihtl rh.list rest hrh.symm
    refine ⟨rh.trans rt, ?_, by simpa [RightSublist.trans] using hrt⟩
    rw [parseTree_eq_infixR heq]
    apply List.mem_flatMap.mpr
    refine ⟨(hd, rh), hmemh, ?_⟩
    apply List.mem_cons.mpr; right
    exact List.mem_map.mpr ⟨(tl, rt), hmemt, rfl⟩
  -- Children.infixN
  case ciN =>
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
  -- PrefixStack.last
  case psl =>
    intro a w tb ihw ihtb tkns rest hflat
    simp only [PrefixStack.flatten, List.append_assoc] at hflat
    obtain ⟨rw_, hmemw, hrw⟩ := ihw tkns (tb.flatten ++ rest) hflat
    obtain ⟨rt, hmemt, hrt⟩ := ihtb rw_.list rest hrw.symm
    refine ⟨rw_.trans rt, ?_, by simpa [RightSublist.trans] using hrt⟩
    rw [parsePrefixStack]
    apply List.mem_flatMap.mpr
    refine ⟨(w, rw_), hmemw, ?_⟩
    apply List.mem_append.mpr; left
    exact List.mem_map.mpr ⟨(tb, rt), hmemt, rfl⟩
  -- PrefixStack.more
  case psm =>
    intro a w ps ihw ihps tkns rest hflat
    simp only [PrefixStack.flatten, List.append_assoc] at hflat
    obtain ⟨rw_, hmemw, hrw⟩ := ihw tkns (ps.flatten ++ rest) hflat
    obtain ⟨rp, hmemp, hrp⟩ := ihps rw_.list rest hrw.symm
    refine ⟨rw_.trans rp, ?_, by simpa [RightSublist.trans] using hrp⟩
    rw [parsePrefixStack]
    apply List.mem_flatMap.mpr
    refine ⟨(w, rw_), hmemw, ?_⟩
    apply List.mem_append.mpr; right
    exact List.mem_map.mpr ⟨(ps, rp), hmemp, rfl⟩
  -- PostfixTail.last
  case ptl =>
    intro a w ihw tkns rest hflat
    simp only [PostfixTail.flatten] at hflat
    obtain ⟨rw_, hmemw, hrw⟩ := ihw tkns rest hflat
    refine ⟨rw_, ?_, hrw⟩
    rw [parsePostfixTail]
    exact List.mem_flatMap.mpr ⟨(w, rw_), hmemw, List.mem_cons_self⟩
  -- PostfixTail.cons
  case ptc =>
    intro a w pt ihw ihpt tkns rest hflat
    simp only [PostfixTail.flatten, List.append_assoc] at hflat
    obtain ⟨rw_, hmemw, hrw⟩ := ihw tkns (pt.flatten ++ rest) hflat
    obtain ⟨rp, hmemp, hrp⟩ := ihpt rw_.list rest hrw.symm
    refine ⟨rw_.trans rp, ?_, by simpa [RightSublist.trans] using hrp⟩
    rw [parsePostfixTail]
    apply List.mem_flatMap.mpr
    refine ⟨(w, rw_), hmemw, ?_⟩
    apply List.mem_cons.mpr; right
    exact List.mem_map.mpr ⟨(pt, rp), hmemp, rfl⟩
  -- InfixTail.last
  case itl =>
    intro a w tb ihw ihtb tkns rest hflat
    simp only [InfixTail.flatten, List.append_assoc] at hflat
    obtain ⟨rw_, hmemw, hrw⟩ := ihw tkns (tb.flatten ++ rest) hflat
    obtain ⟨rt, hmemt, hrt⟩ := ihtb rw_.list rest hrw.symm
    refine ⟨rw_.trans rt, ?_, by simpa [RightSublist.trans] using hrt⟩
    rw [parseInfixTail]
    apply List.mem_flatMap.mpr
    refine ⟨(w, rw_), hmemw, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨(tb, rt), hmemt, ?_⟩
    exact List.mem_cons_self
  -- InfixTail.cons
  case itc =>
    intro a w tb tl ihw ihtb ihtl tkns rest hflat
    simp only [InfixTail.flatten, List.append_assoc] at hflat
    obtain ⟨rw_, hmemw, hrw⟩ := ihw tkns (tb.flatten ++ (tl.flatten ++ rest)) hflat
    obtain ⟨rt, hmemt, hrt⟩ := ihtb rw_.list (tl.flatten ++ rest) hrw.symm
    obtain ⟨rl, hmeml, hrl⟩ := ihtl rt.list rest hrt.symm
    refine ⟨rw_.trans (rt.trans rl), ?_, by simpa [RightSublist.trans] using hrl⟩
    rw [parseInfixTail]
    apply List.mem_flatMap.mpr
    refine ⟨(w, rw_), hmemw, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨(tb, rt), hmemt, ?_⟩
    apply List.mem_cons.mpr; right
    exact List.mem_map.mpr ⟨(tl, rl), hmeml, rfl⟩
  -- Woven.last
  case wl =>
    intro tk tkns rest h
    simp only [Woven.flatten] at h
    subst h
    refine ⟨RightSublist.cons tk rest, ?_, rfl⟩
    show (Woven.last tk, RightSublist.cons tk rest) ∈ parseWoven [tk] (tk :: rest)
    rw [parseWoven.eq_1, if_pos rfl]
    exact List.mem_singleton.mpr rfl
  -- Woven.cons
  case wc =>
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

/-- Core completeness specialised to top-level expressions. -/
theorem mem_parseExpr (tkns : List Token) (e : Tree G .loosest) (rest : List Token)
    (h : e.flatten ++ rest = tkns) :
    ∃ r : RightSublist tkns, (e, r) ∈ parseExpr tkns ∧ r.list = rest := by
  simpa only [parseAtLevel] using mem_parseTree_complete e tkns rest h

/-- Completeness: every expression's flattening parses (fully) back to it. -/
theorem parse_complete (e : Tree G .loosest) : e ∈ parse (G := G) e.flatten := by
  obtain ⟨r, hmem, hr⟩ := mem_parseExpr e.flatten e [] (List.append_nil _)
  unfold parse
  exact List.mem_filterMap.mpr ⟨(e, r), hmem, by simp [hr]⟩

/-- Headline: `parse` accepts exactly the flattenings (membership form). -/
theorem mem_parse_iff {tkns : List Token} {e : Tree G .loosest} :
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

end LambdaLab.Parser.Playground2
