import LambdaLab.Parser.Playground.Parse

/-!
# Soundness of the closed-operator parser

A successful parse is a faithful explanation of the tokens it consumed: the
tree (resp. children) flattens to exactly the consumed prefix, with the
returned `RightSublist` as the leftover. Formally, for both mutually-recursive
parsers,

* `parseTree tkns = some (t, r) → t.flatten ++ r.list = tkns`
* `parseChildren d tkns = some (cs, r) → Children.flatten d cs ++ r.list = tkns`

These hold for *any* grammar — no well-formedness of `lookup` is needed; that
is only required for the converse (completeness/round-trip).

The proof rides the functional-induction principle `parseChildren.induct`,
whose cases mirror the parser's branches one-for-one.
-/

namespace LambdaLab.Parser.Playground

open LambdaLab.Parser

/-- Soundness for `parseChildren`: the parsed children flatten (against their
driving `OpDesc`) to exactly the consumed prefix. -/
theorem parseChildren_sound {G : Grammar} {n : Nat} (d : OpDesc n) (cs : Children G n)
    {tkns : List Token} {r : RightSublist tkns}
    (h : parseChildren d tkns = some (cs, r)) :
    Children.flatten d cs ++ r.list = tkns := by
  refine parseChildren.induct (G := G)
    (motive1 := fun tkns => ∀ (t : Tree G) (r : RightSublist tkns),
      parseTree tkns = some (t, r) → t.flatten ++ r.list = tkns)
    (motive2 := fun n d tkns => ∀ (cs : Children G n) (r : RightSublist tkns),
      parseChildren d tkns = some (cs, r) → Children.flatten d cs ++ r.list = tkns)
    ?case1 ?case2 ?case3 ?case4 ?case5 ?case6 ?case7 ?case8 ?case9 n d tkns cs r h
  case case1 => -- parseTree []
    intro t r h; simp [parseTree] at h
  case case2 => -- parseTree (tk :: rest), lookup tk = some o
    intro tk rest o hlk ih t r h
    simp only [parseTree, hlk, Option.map_eq_some_iff] at h
    obtain ⟨⟨cs, r'⟩, hpc, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨ht, hr⟩ := heq
    subst ht; subst hr
    simpa [Tree.flatten] using ih cs r' hpc
  case case3 => -- parseTree (tk :: rest), lookup tk = none
    intro tk rest hlk t r h; simp [parseTree, hlk] at h
  case case4 => -- parseChildren (.last tk) (tk :: rest)
    intro tk rest cs r h
    simp only [parseChildren, if_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hcs, hr⟩ := h
    subst hcs; subst hr
    simp [Children.flatten, RightSublist.cons]
  case case5 => -- parseChildren (.last t) (tk :: rest), t ≠ tk
    intro t tk rest hne cs r h
    simp [parseChildren, hne] at h
  case case6 => -- parseChildren (.part tk d') (tk :: rest), child parse succeeds
    intro n d' tk rest child rest' hpt ih1 ih2 cs r h
    simp only [parseChildren, if_true, hpt, Option.map_eq_some_iff] at h
    obtain ⟨⟨cs'', r2⟩, hpc, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hcs, hr⟩ := heq
    subst hcs; subst hr
    have hch := ih2 cs'' r2 hpc
    have hchild := ih1 child rest' hpt
    simp [Children.flatten, RightSublist.trans, RightSublist.cons, List.append_assoc, hch, hchild]
  case case7 => -- parseChildren (.part tk d') (tk :: rest), child parse fails
    intro n d' tk rest hpt ih1 cs r h
    simp [parseChildren, hpt] at h
  case case8 => -- parseChildren (.part t d') (tk :: rest), t ≠ tk
    intro n t d' tk rest hne cs r h
    simp [parseChildren, hne] at h
  case case9 => -- parseChildren d []
    intro n d cs r h
    simp [parseChildren] at h

/-- Soundness for `parseTree`: the parsed tree flattens to exactly the consumed
prefix. Follows directly from `parseChildren_sound` — `parseTree` only selects
an operator and delegates. -/
theorem parseTree_sound {G : Grammar} (t : Tree G) {tkns : List Token} {r : RightSublist tkns}
    (h : parseTree tkns = some (t, r)) : t.flatten ++ r.list = tkns := by
  cases tkns with
  | nil => simp [parseTree] at h
  | cons tk rest =>
    cases hlk : G.lookup tk with
    | none => simp [parseTree, hlk] at h
    | some o =>
      simp only [parseTree, hlk, Option.map_eq_some_iff] at h
      obtain ⟨⟨cs, r'⟩, hpc, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨ht, hr⟩ := heq
      subst ht; subst hr
      simpa [Tree.flatten] using parseChildren_sound (G.OpDescs o) cs hpc

/-- Top-level soundness: anything `parseAll (parser G)` accepts is the flattening
of the tree it returns. -/
theorem parseAll_sound {G : Grammar} {tkns : List Token} {t : Tree G}
    (h : parseAll (parser G) tkns = some t) : t.flatten = tkns := by
  unfold parseAll parser at h
  cases hp : parseTree tkns with
  | none => rw [hp] at h; simp at h
  | some tr =>
    obtain ⟨t', r⟩ := tr
    rw [hp] at h
    simp only at h
    split at h
    · rename_i hempty
      simp only [Option.some.injEq] at h
      subst h
      have := parseTree_sound t' hp
      simpa [hempty] using this
    · simp at h

end LambdaLab.Parser.Playground
