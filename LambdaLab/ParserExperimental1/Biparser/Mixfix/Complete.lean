import LambdaLab.ParserExperimental1.Biparser.Mixfix.Render
import LambdaLab.ParserExperimental1.Biparser.Mixfix.Parse

/-!
# `parse_complete` and the assembled biparser

Every rendering round-trips: for any tree `t`, gap counter `f`, start counter `i` and
continuation `rest`, parsing `(Tree.render t f i).1 ++ rest` finds `t`, leaving exactly
`rest`. Proved by structural induction on `Tree`, generalized over the level `p` and the
counter `i`; the `var`/`paren`/`op` cases mirror `Telescope.lean`, with the `op` case
navigating the parser's `range`+`dite`+`afterLeft` structure. Each gap/token joint is
discharged by the corresponding combinator leaf's own `parse_complete` (`lpGap`, `gapRp`,
`gapOpGap`), composed with the `RightSublist.cast` plumbing.
-/

namespace LambdaLab.ParserExperimental1.Mixfix

open LambdaLab.ParserExperimental1

mutual
theorem parseAt_complete {G : Grammar} :
    (p : Nat) → (t : Tree G p) → (f : Nat → Nat) → (i : Nat) → (rest : List Char) →
    ∃ s : RightSublist ((Tree.render t f i).1 ++ rest),
      s.list = rest ∧ (t, s) ∈ parseAt p ((Tree.render t f i).1 ++ rest)
  | p, .var c hc, f, i, rest => by
    have hv : (Tree.render (Tree.var c hc : Tree G p) f i).1 = [c] := by simp [Tree.render]
    rw [hv]
    refine ⟨RightSublist.cons c rest, rfl, ?_⟩
    show (Tree.var c hc, RightSublist.cons c rest) ∈ parseAt p ([c] ++ rest)
    rw [parseAt]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    refine List.mem_map.mpr ⟨(⟨c, hc⟩, RightSublist.cons c rest), ?_, rfl⟩
    show (⟨c, hc⟩, RightSublist.cons c rest) ∈
      (if h : (fun c => G.isVar c) c = true then
        [((⟨c, h⟩ : {c : Char // (fun c => G.isVar c) c = true}), RightSublist.cons c rest)] else [])
    rw [dif_pos hc, List.mem_singleton]
  | p, .paren t', f, i, rest => by
    obtain ⟨u1, hu1, hm1⟩ := (lpGap G).parse_complete (lpVal, ()) ((), f i)
      ((Tree.render t' f (i + 1)).1 ++
        ((gapRp G).render ((), rpVal) (f (Tree.render t' f (i + 1)).2, ()) ++ rest))
    obtain ⟨u2, hu2, hm2⟩ := parseAt_complete 0 t' f (i + 1)
      ((gapRp G).render ((), rpVal) (f (Tree.render t' f (i + 1)).2, ()) ++ rest)
    obtain ⟨u3, hu3, hm3⟩ := (gapRp G).parse_complete ((), rpVal)
      (f (Tree.render t' f (i + 1)).2, ()) rest
    have hexp : (Tree.render (Tree.paren t' : Tree G p) f i).1 ++ rest
        = (lpGap G).render (lpVal, ()) ((), f i) ++
          ((Tree.render t' f (i + 1)).1 ++
            ((gapRp G).render ((), rpVal) (f (Tree.render t' f (i + 1)).2, ()) ++ rest)) := by
      simp only [Tree.render, List.append_assoc]
    rw [hexp]
    refine ⟨u1.trans ((u2.cast hu1.symm).trans (u3.cast hu2.symm)),
            by simp [RightSublist.trans, RightSublist.cast_list, hu3], ?_⟩
    rw [parseAt]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨((lpVal, ()), u1), hm1,
           (t', u2.cast hu1.symm), mem_cast_gen (parseAt 0) hu1.symm hm2,
           (((), rpVal), u3.cast hu2.symm), mem_cast_gen (gapRp G).parse hu2.symm hm3, rfl⟩
  | p, .op k hk hfix hp l r, f, i, rest => by
    obtain ⟨uL, huL, hmL⟩ := parseAt_complete (k + 1) l f i
      ((gapOpGap G k hk).render ((), opVal G k hk, ())
          (f (Tree.render l f i).2, (), f ((Tree.render l f i).2 + 1)) ++
        ((Tree.render r f ((Tree.render l f i).2 + 2)).1 ++ rest))
    obtain ⟨uM, huM, hmM⟩ := (gapOpGap G k hk).parse_complete ((), opVal G k hk, ())
      (f (Tree.render l f i).2, (), f ((Tree.render l f i).2 + 1))
      ((Tree.render r f ((Tree.render l f i).2 + 2)).1 ++ rest)
    obtain ⟨uR, huR, hmR⟩ := parseAt_complete k r f ((Tree.render l f i).2 + 2) rest
    have hexp : (Tree.render (Tree.op k hk hfix hp l r) f i).1 ++ rest
        = (Tree.render l f i).1 ++
          ((gapOpGap G k hk).render ((), opVal G k hk, ())
              (f (Tree.render l f i).2, (), f ((Tree.render l f i).2 + 1)) ++
            ((Tree.render r f ((Tree.render l f i).2 + 2)).1 ++ rest)) := by
      simp only [Tree.render, List.append_assoc]
    rw [hexp]
    refine ⟨uL.trans ((uM.cast huL.symm).trans (uR.cast huM.symm)),
            by simp [RightSublist.trans, RightSublist.cast_list, huR], ?_⟩
    rw [parseAt]
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_flatMap]
    refine ⟨k, List.mem_range.mpr hk, ?_⟩
    rw [dif_pos hk, dif_pos hp, dif_pos hfix]
    simp only [List.mem_flatMap]
    refine ⟨(l, uL), hmL, ?_⟩
    rw [afterInfixr]
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨(((), opVal G k hk, ()), uM.cast huL.symm),
             mem_cast_gen (gapOpGap G k hk).parse huL.symm hmM,
           (r, uR.cast huM.symm), mem_cast_gen (parseAt k) huM.symm hmR, rfl⟩
  | p, .pre k hk hfix hp e, f, i, rest => by
    obtain ⟨uO, huO, hmO⟩ := (opGap G k hk).parse_complete (opVal G k hk, ()) ((), f i)
      ((Tree.render e f (i + 1)).1 ++ rest)
    obtain ⟨uE, huE, hmE⟩ := parseAt_complete (k + 1) e f (i + 1) rest
    have hexp : (Tree.render (Tree.pre k hk hfix hp e) f i).1 ++ rest
        = (opGap G k hk).render (opVal G k hk, ()) ((), f i) ++
          ((Tree.render e f (i + 1)).1 ++ rest) := by
      simp only [Tree.render, List.append_assoc]
    rw [hexp]
    refine ⟨uO.trans (uE.cast huO.symm),
            by simp [RightSublist.trans, RightSublist.cast_list, huE], ?_⟩
    rw [parseAt]
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_flatMap]
    refine ⟨k, List.mem_range.mpr hk, ?_⟩
    rw [dif_pos hk, dif_pos hp, dif_neg (show ¬ G.opFixity k hk = .infixr by rw [hfix]; decide),
      dif_neg (show ¬ G.opFixity k hk = .infixl by rw [hfix]; decide), dif_pos hfix]
    simp only [List.mem_flatMap]
    refine ⟨((opVal G k hk, ()), uO), hmO, ?_⟩
    rw [afterPre]
    simp only [List.mem_map]
    exact ⟨(e, uE.cast huO.symm), mem_cast_gen (parseAt (k + 1)) huO.symm hmE, rfl⟩
  | p, .post k hk hfix hp e, f, i, rest => by
    obtain ⟨uE, huE, hmE⟩ := parseAt_complete (k + 1) e f i
      ((gapOp G k hk).render ((), opVal G k hk) (f (Tree.render e f i).2, ()) ++ rest)
    obtain ⟨uP, huP, hmP⟩ := (gapOp G k hk).parse_complete ((), opVal G k hk)
      (f (Tree.render e f i).2, ()) rest
    have hexp : (Tree.render (Tree.post k hk hfix hp e) f i).1 ++ rest
        = (Tree.render e f i).1 ++
          ((gapOp G k hk).render ((), opVal G k hk) (f (Tree.render e f i).2, ()) ++ rest) := by
      simp only [Tree.render, List.append_assoc]
    rw [hexp]
    refine ⟨uE.trans (uP.cast huE.symm),
            by simp [RightSublist.trans, RightSublist.cast_list, huP], ?_⟩
    rw [parseAt]
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_flatMap]
    refine ⟨k, List.mem_range.mpr hk, ?_⟩
    rw [dif_pos hk, dif_pos hp,
      dif_neg (show ¬ G.opFixity k hk = .infixr by rw [hfix]; decide),
      dif_neg (show ¬ G.opFixity k hk = .infixl by rw [hfix]; decide),
      dif_neg (show ¬ G.opFixity k hk = .prefix by rw [hfix]; decide), dif_pos hfix]
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨(e, uE), hmE, (((), opVal G k hk), uP.cast huE.symm),
           mem_cast_gen (gapOp G k hk).parse huE.symm hmP, rfl⟩
  | p, .opl k hk hfix hp head chainHead chainRest, f, i, rest => by
    obtain ⟨uH, huH, hmH⟩ := parseAt_complete (k + 1) head f i
      (renderChainFull k hk chainHead chainRest f (Tree.render head f i).2 ++ rest)
    obtain ⟨uC, huC, hmC⟩ := chainL_complete k hk chainHead chainRest f (Tree.render head f i).2 rest
    have hexp : (Tree.render (Tree.opl k hk hfix hp head chainHead chainRest) f i).1 ++ rest
        = (Tree.render head f i).1 ++
          (renderChainFull k hk chainHead chainRest f (Tree.render head f i).2 ++ rest) := by
      simp only [Tree.render, renderChainFull, List.append_assoc]
    rw [hexp]
    refine ⟨uH.trans (uC.cast huH.symm),
            by simp [RightSublist.trans, RightSublist.cast_list, huC], ?_⟩
    rw [parseAt]
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_flatMap]
    refine ⟨k, List.mem_range.mpr hk, ?_⟩
    rw [dif_pos hk, dif_pos hp, dif_neg (by rw [hfix]; decide), dif_pos hfix]
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨(head, uH), hmH, ((chainHead, chainRest), uC.cast huH.symm),
           mem_cast_gen (chainL k hk) huH.symm hmC, rfl⟩
  | p, .jux hj hp head chainHead chainRest, f, i, rest => by
    obtain ⟨uH, huH, hmH⟩ := parseAt_complete (G.ops.length + 1) head f i
      (renderJuxtChainFull chainHead chainRest f (Tree.render head f i).2 ++ rest)
    obtain ⟨uC, huC, hmC⟩ := juxtChainL_complete chainHead chainRest f (Tree.render head f i).2 rest
    have hexp : (Tree.render (Tree.jux hj hp head chainHead chainRest) f i).1 ++ rest
        = (Tree.render head f i).1 ++
          (renderJuxtChainFull chainHead chainRest f (Tree.render head f i).2 ++ rest) := by
      simp only [Tree.render, renderJuxtChainFull, List.append_assoc]
    rw [hexp]
    refine ⟨uH.trans (uC.cast huH.symm),
            by simp [RightSublist.trans, RightSublist.cast_list, huC], ?_⟩
    rw [parseAt]
    apply List.mem_append_right
    rw [dif_pos hj, dif_pos hp]
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨(head, uH), hmH, ((chainHead, chainRest), uC.cast huH.symm),
           mem_cast_gen juxtChainL huH.symm hmC, rfl⟩
  termination_by p t _ _ _ => sizeOf t
theorem chainL_complete {G : Grammar} (k : Nat) (hk : k < G.ops.length) :
    (chainHead : Tree G (k + 1)) → (chainRest : TreeChain G (k + 1)) → (f : Nat → Nat) →
    (i : Nat) → (rest : List Char) →
    ∃ s : RightSublist (renderChainFull k hk chainHead chainRest f i ++ rest),
      s.list = rest ∧
        ((chainHead, chainRest), s) ∈ chainL k hk (renderChainFull k hk chainHead chainRest f i ++ rest)
  | chainHead, .nil, f, i, rest => by
    obtain ⟨uM, huM, hmM⟩ := (gapOpGap G k hk).parse_complete ((), opVal G k hk, ())
      (f i, (), f (i + 1)) ((Tree.render chainHead f (i + 2)).1 ++ rest)
    obtain ⟨uE, huE, hmE⟩ := parseAt_complete (k + 1) chainHead f (i + 2) rest
    have hexp : renderChainFull k hk chainHead .nil f i ++ rest
        = (gapOpGap G k hk).render ((), opVal G k hk, ()) (f i, (), f (i + 1)) ++
          ((Tree.render chainHead f (i + 2)).1 ++ rest) := by
      simp only [renderChainFull, renderSeg, renderChain, List.append_nil, List.append_assoc]
    rw [hexp]
    refine ⟨uM.trans (uE.cast huM.symm),
            by simp [RightSublist.trans, RightSublist.cast_list, huE], ?_⟩
    rw [chainL]
    simp only [List.mem_flatMap]
    refine ⟨(chainHead, uM.trans (uE.cast huM.symm)), ?_, List.mem_cons_self⟩
    rw [segParse]
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨(((), opVal G k hk, ()), uM), hmM,
           (chainHead, uE.cast huM.symm), mem_cast_gen (parseAt (k + 1)) huM.symm hmE, rfl⟩
  | chainHead, .cons c cs, f, i, rest => by
    obtain ⟨uM, huM, hmM⟩ := (gapOpGap G k hk).parse_complete ((), opVal G k hk, ())
      (f i, (), f (i + 1))
      ((Tree.render chainHead f (i + 2)).1 ++
        (renderChainFull k hk c cs f (renderSeg k hk chainHead f i).2 ++ rest))
    obtain ⟨uE, huE, hmE⟩ := parseAt_complete (k + 1) chainHead f (i + 2)
      (renderChainFull k hk c cs f (renderSeg k hk chainHead f i).2 ++ rest)
    obtain ⟨uC, huC, hmC⟩ := chainL_complete k hk c cs f (renderSeg k hk chainHead f i).2 rest
    have hexp : renderChainFull k hk chainHead (.cons c cs) f i ++ rest
        = (gapOpGap G k hk).render ((), opVal G k hk, ()) (f i, (), f (i + 1)) ++
          ((Tree.render chainHead f (i + 2)).1 ++
            (renderChainFull k hk c cs f (renderSeg k hk chainHead f i).2 ++ rest)) := by
      simp only [renderChainFull, renderSeg, renderChain, List.append_assoc]
    rw [hexp]
    refine ⟨(uM.trans (uE.cast huM.symm)).trans (uC.cast huE.symm),
            by simp [RightSublist.trans, RightSublist.cast_list, huC], ?_⟩
    rw [chainL]
    simp only [List.mem_flatMap]
    refine ⟨(chainHead, uM.trans (uE.cast huM.symm)), ?_, ?_⟩
    · rw [segParse]
      simp only [List.mem_flatMap, List.mem_map]
      exact ⟨(((), opVal G k hk, ()), uM), hmM,
             (chainHead, uE.cast huM.symm), mem_cast_gen (parseAt (k + 1)) huM.symm hmE, rfl⟩
    · simp only [List.mem_cons, List.mem_map]
      refine Or.inr ⟨((c, cs), uC.cast huE.symm), ?_, rfl⟩
      exact mem_cast_gen (chainL k hk) huE.symm hmC
  termination_by chainHead chainRest _ _ _ => sizeOf chainHead + sizeOf chainRest
theorem juxtChainL_complete {G : Grammar} :
    (chainHead : Tree G (G.ops.length + 1)) → (chainRest : TreeChain G (G.ops.length + 1)) →
    (f : Nat → Nat) → (i : Nat) → (rest : List Char) →
    ∃ s : RightSublist (renderJuxtChainFull chainHead chainRest f i ++ rest),
      s.list = rest ∧
        ((chainHead, chainRest), s) ∈ juxtChainL (renderJuxtChainFull chainHead chainRest f i ++ rest)
  | chainHead, .nil, f, i, rest => by
    obtain ⟨uG, huG, hmG⟩ := (sepRun G).parse_complete () (f i)
      ((Tree.render chainHead f (i + 1)).1 ++ rest)
    obtain ⟨uE, huE, hmE⟩ := parseAt_complete (G.ops.length + 1) chainHead f (i + 1) rest
    have hexp : renderJuxtChainFull chainHead .nil f i ++ rest
        = (sepRun G).render () (f i) ++ ((Tree.render chainHead f (i + 1)).1 ++ rest) := by
      simp only [renderJuxtChainFull, renderJuxtSeg, renderJuxtChain, List.append_nil,
        List.append_assoc]
    rw [hexp]
    refine ⟨uG.trans (uE.cast huG.symm),
            by simp [RightSublist.trans, RightSublist.cast_list, huE], ?_⟩
    rw [juxtChainL]
    simp only [List.mem_flatMap]
    refine ⟨(chainHead, uG.trans (uE.cast huG.symm)), ?_, List.mem_cons_self⟩
    rw [juxtSegParse]
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨((), uG), hmG,
           (chainHead, uE.cast huG.symm), mem_cast_gen (parseAt (G.ops.length + 1)) huG.symm hmE, rfl⟩
  | chainHead, .cons c cs, f, i, rest => by
    obtain ⟨uG, huG, hmG⟩ := (sepRun G).parse_complete () (f i)
      ((Tree.render chainHead f (i + 1)).1 ++
        (renderJuxtChainFull c cs f (renderJuxtSeg chainHead f i).2 ++ rest))
    obtain ⟨uE, huE, hmE⟩ := parseAt_complete (G.ops.length + 1) chainHead f (i + 1)
      (renderJuxtChainFull c cs f (renderJuxtSeg chainHead f i).2 ++ rest)
    obtain ⟨uC, huC, hmC⟩ := juxtChainL_complete c cs f (renderJuxtSeg chainHead f i).2 rest
    have hexp : renderJuxtChainFull chainHead (.cons c cs) f i ++ rest
        = (sepRun G).render () (f i) ++
          ((Tree.render chainHead f (i + 1)).1 ++
            (renderJuxtChainFull c cs f (renderJuxtSeg chainHead f i).2 ++ rest)) := by
      simp only [renderJuxtChainFull, renderJuxtSeg, renderJuxtChain, List.append_assoc]
    rw [hexp]
    refine ⟨(uG.trans (uE.cast huG.symm)).trans (uC.cast huE.symm),
            by simp [RightSublist.trans, RightSublist.cast_list, huC], ?_⟩
    rw [juxtChainL]
    simp only [List.mem_flatMap]
    refine ⟨(chainHead, uG.trans (uE.cast huG.symm)), ?_, ?_⟩
    · rw [juxtSegParse]
      simp only [List.mem_flatMap, List.mem_map]
      exact ⟨((), uG), hmG,
             (chainHead, uE.cast huG.symm), mem_cast_gen (parseAt (G.ops.length + 1)) huG.symm hmE, rfl⟩
    · simp only [List.mem_cons, List.mem_map]
      refine Or.inr ⟨((c, cs), uC.cast huE.symm), ?_, rfl⟩
      exact mem_cast_gen juxtChainL huE.symm hmC
  termination_by chainHead chainRest _ _ _ => sizeOf chainHead + sizeOf chainRest
end

/-- The generic mixfix biparser at the loosest level: parse chars into a `Tree G 0`,
render a tree back under a telescope policy `f : Nat → Nat`. Weak target
(`parse_complete` only). -/
def mixfixBip {G : Grammar} : Biparser Char (Nat → Nat) (Tree G 0) where
  render t f := (Tree.render t f 0).1
  parse := parseAt 0
  parse_complete := fun t f rest => parseAt_complete 0 t f 0 rest

end LambdaLab.ParserExperimental1.Mixfix
