import LambdaLab.ParserExperimental1.Biparser.Mixfix.Basic
import LambdaLab.ParserExperimental1.Biparser.Example

/-!
# The generic combinator parser — Stage 2

A char-level parser for the data-driven grammar of `Basic.lean`, producing
precedence-indexed `Tree G p`. Right-associative precedence climbing:

* an **atom** is a variable, or `"(" expr ")"` (a bracketed level-0 tree);
* an **operator** node at precedence `k ≥ p` parses its left operand one level tighter
  (`parseAt (k+1)`, on the *same* input — the source of the level recursion) then, after
  the operator token, its right operand at the same level (`parseAt k`, on shorter input).

Every gap is `spaces1` pre-composed with its adjacent token (`lpGap`, `gapRp`,
`gapOpGap`), so each recursive call is one `flatMap` deep (the `afterLeft` helper keeps
the right-operand call shallow, as `afterAtomWS` did in `Telescope.lean`). Termination is
the lexicographic measure `(input.length, G.ops.length - level)`: descending a level is
same-input but lowers the second component; every other recursive call consumes ≥1 char.
-/

namespace LambdaLab.ParserExperimental1.Mixfix

open LambdaLab.ParserExperimental1

/-! ### The parser (leaves `varTok`/`lpGap`/`gapRp`/`gapOpGap` live in `Basic.lean`). -/

mutual
def parseAt {G : Grammar} (p : Nat) (input : List Char) : List (Tree G p × RightSublist input) :=
  ((varTok G).parse input).map (fun r => (Tree.var r.1.val r.1.property, r.2)) ++
  (lpGap.parse input).flatMap (fun r1 =>
    (parseAt 0 r1.2.list).flatMap (fun r2 =>
      (gapRp.parse r2.2.list).map (fun r3 =>
        (Tree.paren r2.1, r1.2.trans (r2.2.trans r3.2))))) ++
  (List.range G.ops.length).flatMap (fun k =>
    if hk : k < G.ops.length then
      if hp : p ≤ k then
        (parseAt (k + 1) input).flatMap (fun rL => afterLeft p k hk hp rL.1 rL.2)
      else []
    else [])
  termination_by (input.length, G.ops.length - p)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ r1.2.length_lt
      | exact Prod.Lex.left _ _ rL.2.length_lt
      | (apply Prod.Lex.right; omega)
def afterLeft {G : Grammar} (p k : Nat) (hk : k < G.ops.length) (hp : p ≤ k)
    (left : Tree G (k + 1)) {input : List Char} (s : RightSublist input) :
    List (Tree G p × RightSublist input) :=
  ((gapOpGap G k hk).parse s.list).flatMap (fun rM =>
    (parseAt k rM.2.list).map (fun rR =>
      (Tree.op k hk hp left rR.1, s.trans (rM.2.trans rR.2))))
  termination_by (s.list.length, 0)
  decreasing_by exact Prod.Lex.left _ _ rM.2.length_lt
end

/-! ### `parse_complete`, generalized over the level `p` and the gap counter `i`. -/

theorem parseAt_complete {G : Grammar} :
    (p : Nat) → (t : Tree G p) → (f : Nat → Nat) → (i : Nat) → (rest : List Char) →
    ∃ s : RightSublist ((Tree.render t f i).1 ++ rest),
      s.list = rest ∧ (t, s) ∈ parseAt p ((Tree.render t f i).1 ++ rest)
  | p, .var c hc, f, i, rest => by
    refine ⟨RightSublist.cons c rest, rfl, ?_⟩
    show (Tree.var c hc, RightSublist.cons c rest) ∈ parseAt p ([c] ++ rest)
    rw [parseAt]
    apply List.mem_append_left
    apply List.mem_append_left
    refine List.mem_map.mpr ⟨(⟨c, hc⟩, RightSublist.cons c rest), ?_, rfl⟩
    show (⟨c, hc⟩, RightSublist.cons c rest) ∈
      (if h : (fun c => G.isVar c) c = true then
        [((⟨c, h⟩ : {c : Char // (fun c => G.isVar c) c = true}), RightSublist.cons c rest)] else [])
    rw [dif_pos hc, List.mem_singleton]
  | p, .paren t', f, i, rest => by
    obtain ⟨u1, hu1, hm1⟩ := lpGap.parse_complete (lpVal, ()) ((), f i)
      ((Tree.render t' f (i + 1)).1 ++
        (gapRp.render ((), rpVal) (f (Tree.render t' f (i + 1)).2, ()) ++ rest))
    obtain ⟨u2, hu2, hm2⟩ := parseAt_complete 0 t' f (i + 1)
      (gapRp.render ((), rpVal) (f (Tree.render t' f (i + 1)).2, ()) ++ rest)
    obtain ⟨u3, hu3, hm3⟩ := gapRp.parse_complete ((), rpVal)
      (f (Tree.render t' f (i + 1)).2, ()) rest
    have hexp : (Tree.render (Tree.paren t' : Tree G p) f i).1 ++ rest
        = lpGap.render (lpVal, ()) ((), f i) ++
          ((Tree.render t' f (i + 1)).1 ++
            (gapRp.render ((), rpVal) (f (Tree.render t' f (i + 1)).2, ()) ++ rest)) := by
      simp only [Tree.render, List.append_assoc]
    rw [hexp]
    refine ⟨u1.trans ((u2.cast hu1.symm).trans (u3.cast hu2.symm)),
            by simp [RightSublist.trans, RightSublist.cast_list, hu3], ?_⟩
    rw [parseAt]
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨((lpVal, ()), u1), hm1,
           (t', u2.cast hu1.symm), mem_cast_gen (parseAt 0) hu1.symm hm2,
           (((), rpVal), u3.cast hu2.symm), mem_cast_gen gapRp.parse hu2.symm hm3, rfl⟩
  | p, .op k hk hp l r, f, i, rest => by
    obtain ⟨uL, huL, hmL⟩ := parseAt_complete (k + 1) l f i
      ((gapOpGap G k hk).render ((), opVal G k hk, ())
          (f (Tree.render l f i).2, (), f ((Tree.render l f i).2 + 1)) ++
        ((Tree.render r f ((Tree.render l f i).2 + 2)).1 ++ rest))
    obtain ⟨uM, huM, hmM⟩ := (gapOpGap G k hk).parse_complete ((), opVal G k hk, ())
      (f (Tree.render l f i).2, (), f ((Tree.render l f i).2 + 1))
      ((Tree.render r f ((Tree.render l f i).2 + 2)).1 ++ rest)
    obtain ⟨uR, huR, hmR⟩ := parseAt_complete k r f ((Tree.render l f i).2 + 2) rest
    have hexp : (Tree.render (Tree.op k hk hp l r) f i).1 ++ rest
        = (Tree.render l f i).1 ++
          ((gapOpGap G k hk).render ((), opVal G k hk, ())
              (f (Tree.render l f i).2, (), f ((Tree.render l f i).2 + 1)) ++
            ((Tree.render r f ((Tree.render l f i).2 + 2)).1 ++ rest)) := by
      simp only [Tree.render, List.append_assoc]
    rw [hexp]
    refine ⟨uL.trans ((uM.cast huL.symm).trans (uR.cast huM.symm)),
            by simp [RightSublist.trans, RightSublist.cast_list, huR], ?_⟩
    rw [parseAt]
    apply List.mem_append_right
    simp only [List.mem_flatMap]
    refine ⟨k, List.mem_range.mpr hk, ?_⟩
    rw [dif_pos hk, dif_pos hp]
    simp only [List.mem_flatMap]
    refine ⟨(l, uL), hmL, ?_⟩
    rw [afterLeft]
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨(((), opVal G k hk, ()), uM.cast huL.symm),
             mem_cast_gen (gapOpGap G k hk).parse huL.symm hmM,
           (r, uR.cast huM.symm), mem_cast_gen (parseAt k) huM.symm hmR, rfl⟩

def mixfixBip {G : Grammar} : Biparser Char (Nat → Nat) (Tree G 0) where
  render t f := (Tree.render t f 0).1
  parse := parseAt 0
  parse_complete := fun t f rest => parseAt_complete 0 t f 0 rest

#eval ((parseAt (G := sample) 0 "a + b * c".toList).filter (fun r => r.2.list.isEmpty)).length  -- ≥1
#eval ((parseAt (G := sample) 0 "( a + b )".toList).filter (fun r => r.2.list.isEmpty)).length  -- ≥1

end LambdaLab.ParserExperimental1.Mixfix
