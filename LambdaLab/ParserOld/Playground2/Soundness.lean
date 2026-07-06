import LambdaLab.ParserOld.Playground2.Parse

/-!
# Soundness of the (list-returning) precedence parser

Every parse the parser *returns* is faithful: for each `(a, r)` in the result
list, `a` flattens to the consumed prefix with `r` as leftover. For the two tail
loops the statement is relative to the accumulator (`acc.flatten ++ r.list`).

All eight mutually-recursive parsers are handled in one shot by the
functional-induction principle `parseExpr.induct`, now over list membership.
(Motive order is Lean's, not source order: parseExpr, parseExprRoots, parseTree,
parseInfixLTail, parseWoven, parseBelow, parseBelowList, parsePostfixTail.)
-/

namespace LambdaLab.ParserOld.Playground2

open LambdaLab.ParserOld

variable {G : Grammar}

/-! ## Flattening through the fixity cast

`parseTree`/`parseInfixLTail`/`parsePostfixTail` build a `Children` at the
statically-`closed`/`prefix`/… constructor and then cast it to the abstract
fixity `(G.operator a).fixity` via `hf ▸ _`. These lemmas push `flatten` through
that cast — `Children.flatten` ignores the fixity index, so each reduces to the
obvious concatenation once `hf` is substituted (`generalize`-then-`subst`). -/

theorem flatten_cast_closed {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.closed) (w : Children G a (.weave (G.operator a).nameParts)) :
    (Tree.opSelf a (hf ▸ Children.closed w)).flatten = w.flatten := by
  simp only [Tree.opSelf, Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

theorem flatten_cast_prefix {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.prefix) (ps : Children G a .prefix) :
    (Tree.opSelf a (hf ▸ Children.prefix ps)).flatten = ps.flatten := by
  simp only [Tree.opSelf, Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

theorem flatten_cast_postfix {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.postfix) (tb : Tree G (.tighter a))
    (pt : Children G a .postTail) :
    (Tree.opSelf a (hf ▸ Children.postfix tb pt)).flatten = tb.flatten ++ pt.flatten := by
  simp only [Tree.opSelf, Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

theorem flatten_cast_infixL {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.infix .left) (hd : Tree G (.tighter a))
    (tl : Children G a .infixTail) :
    (Tree.opSelf a (hf ▸ Children.infixL hd tl)).flatten = hd.flatten ++ tl.flatten := by
  simp only [Tree.opSelf, Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

theorem flatten_cast_infixR {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.infix .right) (hd : Tree G (.tighter a))
    (tl : Children G a .infixTail) :
    (Tree.opSelf a (hf ▸ Children.infixR hd tl)).flatten = hd.flatten ++ tl.flatten := by
  simp only [Tree.opSelf, Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

theorem flatten_cast_infixN {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.infix .nonAssoc) (l : Tree G (.tighter a))
    (w : Children G a (.weave (G.operator a).nameParts)) (r : Tree G (.tighter a)) :
    (Tree.opSelf a (hf ▸ Children.infixN l w r)).flatten = l.flatten ++ w.flatten ++ r.flatten := by
  simp only [Tree.opSelf, Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

/-- Soundness for `parseExpr`, proved together with the other eight parsers via
mutual functional induction (over list membership). -/
theorem parseExpr_sound :
    ∀ (tkns : List Token) (e : Tree G .loosest) (r : RightSublist tkns),
      (e, r) ∈ parseExpr tkns → e.flatten ++ r.list = tkns := by
  apply parseExpr.induct (G := G)
    (motive1 := fun (tkns : List Token) =>
      ∀ e r, (e, r) ∈ parseExpr tkns → e.flatten ++ r.list = tkns)
    (motive2 := fun (rs : List G.Op) (hsub : ∀ r ∈ rs, r ∈ G.loosest) (tkns : List Token) =>
      ∀ e r, (e, r) ∈ parseExprRoots rs hsub tkns → e.flatten ++ r.list = tkns)
    (motive3 := fun (a : G.Op) (tkns : List Token) =>
      ∀ t r, (t, r) ∈ parseTree a tkns → t.flatten ++ r.list = tkns)
    (motive4 := fun (a : G.Op) (tkns : List Token) =>
      ∀ p r, (p, r) ∈ parseInfixTail a tkns → p.flatten ++ r.list = tkns)
    (motive5 := fun (a : G.Op) (parts : List Token) (tkns : List Token) =>
      ∀ w r, (w, r) ∈ parseWoven a parts tkns → w.flatten ++ r.list = tkns)
    (motive6 := fun (a : G.Op) (tkns : List Token) =>
      ∀ b r, (b, r) ∈ parseBelow a tkns → b.flatten ++ r.list = tkns)
    (motive7 := fun (a : G.Op) (bs : List G.Op) (hsub : ∀ b ∈ bs, b ∈ G.tighter a)
        (tkns : List Token) =>
      ∀ b r, (b, r) ∈ parseBelowList a bs hsub tkns → b.flatten ++ r.list = tkns)
    (motive8 := fun (a : G.Op) (tkns : List Token) =>
      ∀ p r, (p, r) ∈ parsePostfixTail a tkns → p.flatten ++ r.list = tkns)
    (motive9 := fun (a : G.Op) (tkns : List Token) =>
      ∀ p r, (p, r) ∈ parsePrefixStack a tkns → p.flatten ++ r.list = tkns)
  -- parseExpr: delegate to parseExprRoots IH
  case case1 => intro tkns IH e r h; unfold parseExpr at h; exact IH e r h
  -- parseExprRoots []
  case case2 =>
    intro tkns _ _ e r h
    rw [parseExprRoots.eq_1] at h
    exact absurd h List.not_mem_nil
  -- parseExprRoots (r::rest)
  case case3 =>
    intro tkns rr rest hsub1 hsub2 IH3 IH2 e r h
    simp only [parseExprRoots.eq_2, List.mem_append, List.mem_map] at h
    rcases h with ⟨x, hx, heq⟩ | h
    · obtain ⟨xt, xr⟩ := x
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Tree.reindex_flatten]
      exact IH3 xt xr hx
    · exact IH2 e r h
  -- parseTree closed
  case case4 =>
    intro a tkns hf IH2 IH1 t r h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_map.mp h with ⟨x, hx, heq⟩
      obtain ⟨xw, xr⟩ := x
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, rfl⟩ := heq
      rw [← h1, flatten_cast_closed]
      all_goals first | exact IH2 xw xr hx | exact hf
    · rcases List.mem_map.mp h with ⟨x, hx, heq⟩
      obtain ⟨xb, xr⟩ := x
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Tree.lift_flatten]
      exact IH1 xb _ hx
  -- parseTree prefix
  case case5 =>
    intro a tkns hf IH2 IH1 t r h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_map.mp h with ⟨x, hx, heq⟩
      obtain ⟨xp, xr⟩ := x
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, rfl⟩ := heq
      rw [← h1, flatten_cast_prefix hf]
      exact IH2 xp xr hx
    · rcases List.mem_map.mp h with ⟨x, hx, heq⟩
      obtain ⟨xb, xr⟩ := x
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Tree.lift_flatten]
      exact IH1 xb _ hx
  -- parseTree postfix
  case case6 =>
    intro a tkns hf IH2 IH1 t r h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    rcases List.mem_flatMap.mp h with ⟨x, hx, hmem⟩
    obtain ⟨xb, xr⟩ := x
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Tree.lift_flatten]
      exact IH1 xb _ hx
    · rcases List.mem_map.mp hmem with ⟨y, hy, heq⟩
      obtain ⟨yp, yr⟩ := y
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, rfl⟩ := heq
      rw [← h1, flatten_cast_postfix hf]
      simp only [RightSublist.trans]
      have hb := IH1 xb xr hx
      have hpt := IH2 (xb, xr) yp yr hy
      rw [List.append_assoc, hpt, hb]
  -- parseTree infixL
  case case7 =>
    intro a tkns hf IH2 IH1 t r h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    rcases List.mem_flatMap.mp h with ⟨x, hx, hmem⟩
    obtain ⟨xb, xr⟩ := x
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Tree.lift_flatten]
      exact IH1 xb _ hx
    · rcases List.mem_map.mp hmem with ⟨y, hy, heq⟩
      obtain ⟨yt, yr⟩ := y
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, rfl⟩ := heq
      rw [← h1, flatten_cast_infixL hf]
      simp only [RightSublist.trans]
      have hb := IH1 xb xr hx
      have htl := IH2 (xb, xr) yt yr hy
      rw [List.append_assoc, htl, hb]
  -- parseTree infixR
  case case8 =>
    intro a tkns hf IH2 IH1 t r h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    rcases List.mem_flatMap.mp h with ⟨x, hx, hmem⟩
    obtain ⟨xb, xr⟩ := x
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Tree.lift_flatten]
      exact IH1 xb _ hx
    · rcases List.mem_map.mp hmem with ⟨y, hy, heq⟩
      obtain ⟨yt, yr⟩ := y
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, rfl⟩ := heq
      rw [← h1, flatten_cast_infixR hf]
      simp only [RightSublist.trans]
      have hb := IH1 xb xr hx
      have htl := IH2 (xb, xr) yt yr hy
      rw [List.append_assoc, htl, hb]
  -- parseTree infixN
  case case9 =>
    intro a tkns hf IH3 IH2 IH1 t r h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    rcases List.mem_flatMap.mp h with ⟨x, hx, hmem⟩
    obtain ⟨xb, xr⟩ := x
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Tree.lift_flatten]
      exact IH1 xb _ hx
    · rcases List.mem_flatMap.mp hmem with ⟨y, hy, hz⟩
      obtain ⟨yw, yr⟩ := y
      rcases List.mem_map.mp hz with ⟨z, hzz, heq⟩
      obtain ⟨zb, zr⟩ := z
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, rfl⟩ := heq
      rw [← h1, flatten_cast_infixN]
      simp only [RightSublist.trans]
      have hl := IH1 xb xr hx
      have hw := IH2 (xb, xr) yw yr hy
      have hr := IH3 (xb, xr) (yw, yr) zb zr hzz
      rw [List.append_assoc, List.append_assoc, hr, hw, hl]
      all_goals exact hf
  -- parseInfixTail
  case case10 =>
    intro a tkns IH2 IH1 IH0 p r h
    rw [parseInfixTail] at h
    rcases List.mem_flatMap.mp h with ⟨x, hx, hy⟩
    obtain ⟨xw, xr⟩ := x
    rcases List.mem_flatMap.mp hy with ⟨y, hy2, hmem⟩
    obtain ⟨yb, yr⟩ := y
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Children.flatten, RightSublist.trans]
      have hw := IH0 xw xr hx
      have hb := IH1 (xw, xr) yb yr hy2
      rw [List.append_assoc, hb, hw]
    · rcases List.mem_map.mp hmem with ⟨z, hz, heq⟩
      obtain ⟨zt, zr⟩ := z
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Children.flatten, RightSublist.trans]
      have hw := IH0 xw xr hx
      have hb := IH1 (xw, xr) yb yr hy2
      have htl := IH2 (xw, xr) (yb, yr) zt zr hz
      rw [List.append_assoc, List.append_assoc, htl, hb, hw]
  -- parseWoven [t] (t::rest)
  case case11 =>
    intro _a t rest w r h
    rw [parseWoven.eq_1, if_pos rfl] at h
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Children.flatten, RightSublist.cons, List.singleton_append]
  -- parseWoven [tk] (t::rest), t ≠ tk
  case case12 =>
    intro _a tk t rest hne w r h
    rw [parseWoven.eq_1, if_neg hne] at h
    exact absurd h List.not_mem_nil
  -- parseWoven (tk::p::ps) (t::rest)
  case case13 =>
    intro _a p ps t rest IH1 IH2 w r h
    rw [parseWoven.eq_2, if_pos rfl] at h
    rcases List.mem_flatMap.mp h with ⟨x, hx, hy⟩
    obtain ⟨xe, xr⟩ := x
    rcases List.mem_map.mp hy with ⟨y, hyy, heq⟩
    obtain ⟨yw, yr⟩ := y
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Children.flatten, RightSublist.trans, RightSublist.cons]
    have he := IH2 xe xr hx
    have hw := IH1 (xe, xr) yw yr hyy
    rw [List.append_assoc, hw, List.append_assoc, he, List.singleton_append]
  -- parseWoven (tk::p::ps) (t::rest), t ≠ tk
  case case14 =>
    intro _a tk p ps t rest hne w r h
    rw [parseWoven.eq_2, if_neg hne] at h
    exact absurd h List.not_mem_nil
  -- parseWoven catch-all
  case case15 =>
    intro _a parts tkns h1 h2 w r h
    rw [parseWoven.eq_3 _ _ _ h1 h2] at h
    exact absurd h List.not_mem_nil
  -- parseBelow: delegate to parseBelowList IH
  case case16 => intro a tkns IH b r h; unfold parseBelow at h; exact IH b r h
  -- parseBelowList []
  case case17 =>
    intro a tkns _ _ b r h
    rw [parseBelowList.eq_1] at h
    exact absurd h List.not_mem_nil
  -- parseBelowList (b::rest)
  case case18 =>
    intro a tkns bb rest hsub1 hsub2 IH2 IH1 b r h
    simp only [parseBelowList.eq_2, List.mem_append, List.mem_map] at h
    rcases h with ⟨x, hx, heq⟩ | h
    · obtain ⟨xt, xr⟩ := x
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Tree.reindex_flatten]
      exact IH2 xt xr hx
    · exact IH1 b r h
  -- parsePostfixTail
  case case19 =>
    intro a tkns IH2 IH1 p r h
    rw [parsePostfixTail] at h
    rcases List.mem_flatMap.mp h with ⟨x, hx, hmem⟩
    obtain ⟨xw, xr⟩ := x
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Children.flatten]
      exact IH1 xw _ hx
    · rcases List.mem_map.mp hmem with ⟨z, hz, heq⟩
      obtain ⟨zp, zr⟩ := z
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Children.flatten, RightSublist.trans]
      have hw := IH1 xw xr hx
      have hpt := IH2 (xw, xr) zp zr hz
      rw [List.append_assoc, hpt, hw]
  -- parsePrefixStack
  case case20 =>
    intro a tkns IH2 IH1 IH0 p r h
    rw [parsePrefixStack] at h
    rcases List.mem_flatMap.mp h with ⟨x, hx, hmem⟩
    obtain ⟨xw, xr⟩ := x
    rcases List.mem_append.mp hmem with hmem | hmem
    · rcases List.mem_map.mp hmem with ⟨y, hy, heq⟩
      obtain ⟨yb, yr⟩ := y
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Children.flatten, RightSublist.trans]
      have hw := IH0 xw xr hx
      have hb := IH2 (xw, xr) yb yr hy
      rw [List.append_assoc, hb, hw]
    · rcases List.mem_map.mp hmem with ⟨z, hz, heq⟩
      obtain ⟨zp, zr⟩ := z
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Children.flatten, RightSublist.trans]
      have hw := IH0 xw xr hx
      have hps := IH1 (xw, xr) zp zr hz
      rw [List.append_assoc, hps, hw]

/-- Top-level soundness: every full `parse` is a tree flattening to all input. -/
theorem parse_sound {tkns : List Token} {e : Tree G .loosest}
    (h : e ∈ parse (G := G) tkns) : e.flatten = tkns := by
  unfold parse at h
  rcases List.mem_filterMap.mp h with ⟨x, hx, heq⟩
  obtain ⟨e', r⟩ := x
  by_cases hr : r.list = []
  · simp only [hr, reduceIte, Option.some.injEq] at heq
    subst heq
    have := parseExpr_sound tkns e' r hx
    rw [hr, List.append_nil] at this
    exact this
  · simp only [hr, reduceIte] at heq
    exact absurd heq (by simp)

end LambdaLab.ParserOld.Playground2
