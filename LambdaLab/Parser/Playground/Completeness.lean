import LambdaLab.Parser.Playground.Soundness

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
`mem_parseExpr` (structural recursion over the whole tree family via `Expr.rec`).
-/

namespace LambdaLab.Parser.Playground

open LambdaLab.Parser

variable {G : Grammar}

/-! ## Computing `parseTree` under a known fixity -/

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
      (parsePrefixStack a tkns).map (fun x => (Tree.op a (hf ▸ Children.prefix x.1), x.2))
      ++ (parseBelow a tkns).map (fun x => (Tree.next x.1, x.2)) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_postfix {a : G.Op} (hf : (G.operator a).fixity = .postfix)
    (tkns : List Token) :
    parseTree a tkns =
      (parseBelow a tkns).flatMap (fun x =>
        (Tree.next x.1, x.2) ::
        (parsePostfixTail a x.2.list).map (fun y =>
          (Tree.op a (hf ▸ Children.postfix x.1 y.1), x.2.trans y.2))) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_infixL {a : G.Op} (hf : (G.operator a).fixity = .infix .left)
    (tkns : List Token) :
    parseTree a tkns =
      (parseBelow a tkns).flatMap (fun x =>
        (Tree.next x.1, x.2) ::
        (parseInfixTail a x.2.list).map (fun y =>
          (Tree.op a (hf ▸ Children.infixL x.1 y.1), x.2.trans y.2))) := by
  rw [parseTree]; split <;> first | rfl | (rename_i heq; rw [hf] at heq; cases heq)

theorem parseTree_eq_infixR {a : G.Op} (hf : (G.operator a).fixity = .infix .right)
    (tkns : List Token) :
    parseTree a tkns =
      (parseBelow a tkns).flatMap (fun x =>
        (Tree.next x.1, x.2) ::
        (parseInfixTail a x.2.list).map (fun y =>
          (Tree.op a (hf ▸ Children.infixR x.1 y.1), x.2.trans y.2))) := by
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

/-! ## Landing in the right branch of the fold parsers -/

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

/-- A below-parse `(tb, r)` always yields the fall-through tree `Tree.next tb` as
a parse — in every fixity branch (directly in the `++`-right for closed/prefix,
as the cons head of the flatMap for postfix/infix). -/
theorem mem_parseTree_next (a : G.Op) (tkns : List Token) (tb : TreeBelow G a)
    (r : RightSublist tkns) (hmem : (tb, r) ∈ parseBelow a tkns) :
    (Tree.next tb, r) ∈ parseTree a tkns := by
  rw [parseTree]
  split
  · exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨(tb, r), hmem, rfl⟩))
  · exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨(tb, r), hmem, rfl⟩))
  · exact List.mem_flatMap.mpr ⟨(tb, r), hmem, List.mem_cons_self⟩
  · exact List.mem_flatMap.mpr ⟨(tb, r), hmem, List.mem_cons_self⟩
  · exact List.mem_flatMap.mpr ⟨(tb, r), hmem, List.mem_cons_self⟩
  · exact List.mem_flatMap.mpr ⟨(tb, r), hmem, List.mem_cons_self⟩

/-! ## The completeness recursion (structural, via `Expr.rec`) -/

/-- **Core completeness.** Every expression's flattening (followed by any `rest`)
is among the parses, with `rest` as the leftover. Proved by structural recursion
on the mutual tree family via `Expr.rec`. -/
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
      (motive_4 := fun a ps => ∀ tkns rest, ps.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (ps, r) ∈ parsePrefixStack a tkns ∧ r.list = rest)
      (motive_5 := fun a pt => ∀ tkns rest, pt.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (pt, r) ∈ parsePostfixTail a tkns ∧ r.list = rest)
      (motive_6 := fun a tl => ∀ tkns rest, tl.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (tl, r) ∈ parseInfixTail a tkns ∧ r.list = rest)
      (motive_7 := fun parts w => ∀ tkns rest, w.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (w, r) ∈ parseWoven parts tkns ∧ r.list = rest)
      (motive_8 := fun e => ∀ tkns rest, e.flatten ++ rest = tkns →
        ∃ r : RightSublist tkns, (e, r) ∈ parseExpr tkns ∧ r.list = rest)
      ?op ?next ?mk ?closed ?cpre ?cpost ?ciL ?ciR ?ciN ?psl ?psm ?ptl ?ptc ?itl ?itc ?wl ?wc ?em
      e tkns rest h
  -- Tree.op: delegate to the Children motive at `heq := rfl`
  case op => intro a children ih tkns rest h; exact ih rfl tkns rest h
  -- Tree.next: fall-through
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
  -- Woven.last
  case wl =>
    intro tk tkns rest h
    simp only [Woven.flatten] at h
    subst h
    refine ⟨RightSublist.cons tk rest, ?_, rfl⟩
    show (Woven.last tk, RightSublist.cons tk rest) ∈ parseWoven [tk] (tk :: rest)
    rw [parseWoven.eq_1, if_pos rfl]
    exact List.mem_singleton.mpr rfl
  -- Expr.mk
  case em =>
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
