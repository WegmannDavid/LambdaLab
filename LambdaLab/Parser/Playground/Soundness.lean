import LambdaLab.Parser.Playground.Parse

/-!
# Soundness of the precedence parser

A successful parse explains exactly the tokens it consumed: the tree (resp.
children/expr/…) flattens to the consumed prefix, with the returned
`RightSublist` as the leftover. For the two tail loops (`parseInfixLTail`,
`parsePostfixTail`) the statement is *relative*: the fold preserves
`acc.flatten ++ r.list`.

All eight mutually-recursive parsers are handled in one shot by the
functional-induction principle `parseExpr.induct`.
-/

namespace LambdaLab.Parser.Playground

open LambdaLab.Parser

variable {G : Grammar}

/-! ## Flattening through the fixity cast

`parseTree`/`parseInfixLTail`/`parsePostfixTail` build a `Children` at the
statically-`closed`/`prefix`/… constructor and then cast it to the abstract
fixity `(G.operator a).fixity` via `hf ▸ _`. These lemmas push `flatten` through
that cast — `Children.flatten` ignores the fixity index, so each reduces to the
obvious concatenation once `hf` is substituted (`generalize`-then-`subst`). -/

theorem flatten_cast_closed {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.closed) (w : Woven G (G.operator a).nameParts) :
    (Tree.op a (hf ▸ Children.closed w)).flatten = w.flatten := by
  simp only [Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

theorem flatten_cast_prefix {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.prefix) (w : Woven G (G.operator a).nameParts)
    (t : Tree G a) :
    (Tree.op a (hf ▸ Children.prefix w t)).flatten = w.flatten ++ t.flatten := by
  simp only [Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

theorem flatten_cast_postfix {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.postfix) (t : Tree G a)
    (w : Woven G (G.operator a).nameParts) :
    (Tree.op a (hf ▸ Children.postfix t w)).flatten = t.flatten ++ w.flatten := by
  simp only [Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

theorem flatten_cast_infixL {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.infix .left) (l : Tree G a)
    (w : Woven G (G.operator a).nameParts) (r : TreeBelow G a) :
    (Tree.op a (hf ▸ Children.infixL l w r)).flatten = l.flatten ++ w.flatten ++ r.flatten := by
  simp only [Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

theorem flatten_cast_infixR {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.infix .right) (l : TreeBelow G a)
    (w : Woven G (G.operator a).nameParts) (r : Tree G a) :
    (Tree.op a (hf ▸ Children.infixR l w r)).flatten = l.flatten ++ w.flatten ++ r.flatten := by
  simp only [Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

theorem flatten_cast_infixN {a : G.Op}
    (hf : (G.operator a).fixity = Fixity.infix .nonAssoc) (l : TreeBelow G a)
    (w : Woven G (G.operator a).nameParts) (r : TreeBelow G a) :
    (Tree.op a (hf ▸ Children.infixN l w r)).flatten = l.flatten ++ w.flatten ++ r.flatten := by
  simp only [Tree.flatten]; generalize (G.operator a).fixity = fx at hf; subst hf; rfl

/-- Soundness for `parseExpr`, proved together with the other seven parsers via
mutual functional induction. -/
theorem parseExpr_sound :
    ∀ (tkns : List Token) (e : Expr G) (r : RightSublist tkns),
      parseExpr tkns = some (e, r) → e.flatten ++ r.list = tkns := by
  apply parseExpr.induct (G := G)
    (motive1 := fun tkns => ∀ e r, parseExpr tkns = some (e, r) → e.flatten ++ r.list = tkns)
    (motive2 := fun rs hsub tkns => ∀ e r, parseExprRoots rs hsub tkns = some (e, r) →
      e.flatten ++ r.list = tkns)
    (motive3 := fun a tkns => ∀ t r, parseTree a tkns = some (t, r) → t.flatten ++ r.list = tkns)
    (motive4 := fun a hf acc tkns0 r =>
      (parseInfixLTail a hf acc tkns0 r).1.flatten ++ (parseInfixLTail a hf acc tkns0 r).2.list
        = acc.flatten ++ r.list)
    (motive5 := fun a tkns => ∀ b r, parseBelow a tkns = some (b, r) → b.flatten ++ r.list = tkns)
    (motive6 := fun a bs hsub tkns => ∀ b r, parseBelowList a bs hsub tkns = some (b, r) →
      b.flatten ++ r.list = tkns)
    (motive7 := fun parts tkns => ∀ w r, parseWoven parts tkns = some (w, r) →
      w.flatten ++ r.list = tkns)
    (motive8 := fun a hf acc tkns0 r =>
      (parsePostfixTail a hf acc tkns0 r).1.flatten ++ (parsePostfixTail a hf acc tkns0 r).2.list
        = acc.flatten ++ r.list)
  -- parseExpr: delegate to parseExprRoots IH
  case case1 => intro tkns IH e r h; unfold parseExpr at h; exact IH e r h
  -- parseExprRoots []
  case case2 => intro tkns _ _ e r h; exact absurd h (by simp [parseExprRoots])
  -- parseExprRoots (r::rest), head succeeds
  case case3 =>
    intro tkns rr rest hsub t rsl hpt _ IH3 e r h
    simp only [parseExprRoots, hpt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Expr.flatten]
    exact IH3 t rsl hpt
  -- parseExprRoots (r::rest), head fails, recurse
  case case4 =>
    intro tkns rr rest hsub hnone _ _ IH4 e r h
    simp only [parseExprRoots, hnone] at h
    exact IH4 e r h
  -- parseTree closed, woven succeeds
  case case5 =>
    intro a tkns hf w r hpw IH7 t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    rw [hpw] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [flatten_cast_closed]
    exact IH7 w r hpw
    all_goals exact hf
  -- parseTree closed, woven fails, fall through to parseBelow
  case case6 =>
    intro a tkns hf hnone _ IH5 t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hnone, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨b, rb, hpb, rfl, rfl⟩ := h
    simp only [Tree.flatten]
    exact IH5 b rb hpb
    all_goals exact hf
  -- parseTree prefix, woven + tail tree succeed
  case case7 =>
    intro a tkns hf w r1 hpw t2 r2 hpt2 IH7 IHt t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hpw, hpt2, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [flatten_cast_prefix]
    simp only [RightSublist.trans]
    have hw := IH7 w r1 hpw
    have ht := IHt t2 r2 hpt2
    rw [List.append_assoc, ht, hw]
    all_goals exact hf
  -- parseTree prefix, woven succeeds, tail tree fails
  case case8 =>
    intro a tkns hf w r1 hpw hnone _ _ t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hpw, hnone] at h
    exact absurd h (by simp)
    all_goals exact hf
  -- parseTree prefix, woven fails, fall through
  case case9 =>
    intro a tkns hf hnone _ IH5 t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hnone, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨b, rb, hpb, rfl, rfl⟩ := h
    simp only [Tree.flatten]
    exact IH5 b rb hpb
    all_goals exact hf
  -- parseTree postfix, head succeeds, then tail loop
  case case10 =>
    intro a tkns hf first r0 hpb IH5 IHtail t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hpb, Option.some.injEq] at h
    rw [show t = (parsePostfixTail a hf (Tree.next first) tkns r0).1 by rw [h],
        show r' = (parsePostfixTail a hf (Tree.next first) tkns r0).2 by rw [h]]
    rw [IHtail]
    simp only [Tree.flatten]
    exact IH5 first r0 hpb
    all_goals exact hf
  -- parseTree postfix, head fails
  case case11 =>
    intro a tkns hf hnone _ t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hnone] at h
    exact absurd h (by simp)
    all_goals exact hf
  -- parseTree infixL, head succeeds, then tail loop
  case case12 =>
    intro a tkns hf first r0 hpb IH5 IHtail t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hpb, Option.some.injEq] at h
    rw [show t = (parseInfixLTail a hf (Tree.next first) tkns r0).1 by rw [h],
        show r' = (parseInfixLTail a hf (Tree.next first) tkns r0).2 by rw [h]]
    rw [IHtail]
    simp only [Tree.flatten]
    exact IH5 first r0 hpb
    all_goals exact hf
  -- parseTree infixL, head fails
  case case13 =>
    intro a tkns hf hnone _ t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hnone] at h
    exact absurd h (by simp)
    all_goals exact hf
  -- parseTree infixR, all three succeed
  case case14 =>
    intro a tkns hf first r0 hpb w r2 hpw right r3 hpt IH5 IH7 IHt t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hpb, hpw, hpt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [flatten_cast_infixR]
    simp only [RightSublist.trans]
    have hl := IH5 first r0 hpb
    have hw := IH7 w r2 hpw
    have hr := IHt right r3 hpt
    simp only [] at hl
    rw [List.append_assoc, List.append_assoc, hr, hw, hl]
    all_goals exact hf
  -- parseTree infixR, left + woven succeed, right tree fails
  case case15 =>
    intro a tkns hf first r0 hpb w r2 hpw hnone _ _ _ t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hpb, hpw, hnone] at h
    exact absurd h (by simp)
    all_goals exact hf
  -- parseTree infixR, left succeeds, woven fails => just left
  case case16 =>
    intro a tkns hf first r0 hpb hnone IH5 _ t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hpb, hnone, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Tree.flatten]
    exact IH5 first r0 hpb
    all_goals exact hf
  -- parseTree infixR, left fails
  case case17 =>
    intro a tkns hf hnone _ t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hnone] at h
    exact absurd h (by simp)
    all_goals exact hf
  -- parseTree infixN, all three succeed
  case case18 =>
    intro a tkns hf first r0 hpb w r2 hpw right r3 hpb2 IH5 IH7 IHb t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hpb, hpw, hpb2, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [flatten_cast_infixN]
    simp only [RightSublist.trans]
    have hl := IH5 first r0 hpb
    have hw := IH7 w r2 hpw
    have hr := IHb right r3 hpb2
    simp only [] at hl hr
    rw [List.append_assoc, List.append_assoc, hr, hw, hl]
    all_goals exact hf
  -- parseTree infixN, left + woven succeed, right fails
  case case19 =>
    intro a tkns hf first r0 hpb w r2 hpw hnone _ _ _ t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hpb, hpw, hnone] at h
    exact absurd h (by simp)
    all_goals exact hf
  -- parseTree infixN, left succeeds, woven fails => just left
  case case20 =>
    intro a tkns hf first r0 hpb hnone IH5 _ t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hpb, hnone, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Tree.flatten]
    exact IH5 first r0 hpb
    all_goals exact hf
  -- parseTree infixN, left fails
  case case21 =>
    intro a tkns hf hnone _ t r' h
    unfold parseTree at h
    split at h <;>
      first
        | (rename_i heqf; exact absurd (hf ▸ heqf) (by decide))
        | skip
    simp only [hnone] at h
    exact absurd h (by simp)
    all_goals exact hf
  -- parseInfixLTail, woven + below succeed: recurse
  case case22 =>
    intro a hf acc tkns0 r w r2 hpw right r3 hpb IH7 IHb IHtail
    rw [parseInfixLTail]
    simp only [hpw, hpb]
    rw [IHtail, flatten_cast_infixL hf]
    simp only [RightSublist.trans]
    have hw := IH7 w r2 hpw
    have hr := IHb right r3 hpb
    simp only [] at hr
    rw [List.append_assoc, List.append_assoc, hr, hw]
  -- parseInfixLTail, woven succeeds, below fails: stop
  case case23 =>
    intro a hf acc tkns0 r w r2 hpw hnone _ _
    rw [parseInfixLTail]
    simp only [hpw, hnone]
  -- parseInfixLTail, woven fails: stop
  case case24 =>
    intro a hf acc tkns0 r hnone _
    rw [parseInfixLTail]
    simp only [hnone]
  -- parseBelow: delegate to parseBelowList IH
  case case25 => intro a tkns IH b r h; unfold parseBelow at h; exact IH b r h
  -- parseBelowList []
  case case26 => intro a tkns _ _ b r h; exact absurd h (by simp [parseBelowList])
  -- parseBelowList (b::rest), head succeeds
  case case27 =>
    intro a tkns bb rest hsub t rsl hpt _ IH3 b r h
    simp only [parseBelowList, hpt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [TreeBelow.flatten]
    exact IH3 t rsl hpt
  -- parseBelowList (b::rest), head fails, recurse
  case case28 =>
    intro a tkns bb rest hsub hnone _ _ IH6 b r h
    simp only [parseBelowList, hnone] at h
    exact IH6 b r h
  -- parseWoven [t] (t::rest), matches
  case case29 =>
    intro t rest w r h
    by_cases ht : t = t
    · simp only [parseWoven] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Woven.flatten, RightSublist.cons, List.singleton_append]
    · exact absurd rfl ht
  -- parseWoven [tk] (t::rest), t ≠ tk
  case case30 =>
    intro tk t rest hne w r h
    simp only [parseWoven, if_neg hne] at h
    exact absurd h (by simp)
  -- parseWoven (tk::p::ps) (t::rest), expr + inner woven succeed
  case case31 =>
    intro p ps t rest e r1 hpe w r2 hpw IHe IH7 w' r' h
    by_cases ht : t = t
    · simp only [parseWoven, hpe, hpw] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Woven.flatten, RightSublist.trans, RightSublist.cons]
      have he := IHe e r1 hpe
      have hw := IH7 w r2 hpw
      rw [List.append_assoc, hw, List.append_assoc, he, List.singleton_append]
    · exact absurd rfl ht
  -- parseWoven (tk::p::ps) (t::rest), expr succeeds, inner woven fails
  case case32 =>
    intro p ps t rest e r1 hpe hnone _ _ w' r' h
    by_cases ht : t = t
    · simp only [parseWoven, hpe, hnone] at h
      exact absurd h (by simp)
    · exact absurd rfl ht
  -- parseWoven (tk::p::ps) (t::rest), expr fails
  case case33 =>
    intro p ps t rest hnone _ w' r' h
    by_cases ht : t = t
    · simp only [parseWoven, hnone] at h
      exact absurd h (by simp)
    · exact absurd rfl ht
  -- parseWoven (tk::p::ps) (t::rest), t ≠ tk
  case case34 =>
    intro tk p ps t rest hne w' r' h
    simp only [parseWoven, if_neg hne] at h
    exact absurd h (by simp)
  -- parseWoven catch-all (none)
  case case35 =>
    intro parts tkns h1 h2 w r h
    match parts, tkns with
    | [], _ => exact absurd h (by simp [parseWoven])
    | [tk], [] => exact absurd h (by simp [parseWoven])
    | [tk], (t :: rest) => exact (h1 tk t rest rfl rfl).elim
    | (tk :: p :: ps), [] => exact absurd h (by simp [parseWoven])
    | (tk :: p :: ps), (t :: rest) => exact (h2 tk p ps t rest rfl rfl).elim
  -- parsePostfixTail, woven succeeds: recurse
  case case36 =>
    intro a hf acc tkns0 r w r2 hpw IH7 IHtail
    rw [parsePostfixTail]
    simp only [hpw]
    rw [IHtail, flatten_cast_postfix hf]
    simp only [RightSublist.trans]
    have hw := IH7 w r2 hpw
    rw [List.append_assoc, hw]
  -- parsePostfixTail, woven fails: stop
  case case37 =>
    intro a hf acc tkns0 r hnone _
    rw [parsePostfixTail]
    simp only [hnone]

/-- Top-level soundness: a full `parse` returns a tree flattening to all input. -/
theorem parse_sound {tkns : List Token} {e : Expr G}
    (h : parse (G := G) tkns = some e) : e.flatten = tkns := by
  unfold parse at h
  cases hpe : parseExpr (G := G) tkns with
  | none => rw [hpe] at h; exact absurd h (by simp)
  | some p =>
    obtain ⟨e', r⟩ := p
    rw [hpe] at h
    by_cases hr : r.list = []
    · simp only [hr, reduceIte] at h
      injection h with h
      subst h
      have := parseExpr_sound tkns e' r hpe
      rw [hr, List.append_nil] at this
      exact this
    · exact absurd h (by simp [hr])

end LambdaLab.Parser.Playground
