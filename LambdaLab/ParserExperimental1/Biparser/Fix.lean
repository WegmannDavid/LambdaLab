import LambdaLab.ParserExperimental1.Biparser.Combinators
namespace LambdaLab.ParserExperimental1

/-- Nested parens around a single variable `x`. -/
inductive PTree where
  | var : PTree
  | paren : PTree → PTree
deriving Repr

def varTok : Biparser Char Unit {c : Char // (c == 'x') = true} := tok (· == 'x')
def lpTok  : Biparser Char Unit {c : Char // (c == '(') = true} := tok (· == '(')
def rpTok  : Biparser Char Unit {c : Char // (c == ')') = true} := tok (· == ')')

def atomRender : PTree → List Char
  | .var     => ['x']
  | .paren t => '(' :: atomRender t ++ [')']

/-- The recursive parse: a `var`, or `(` then a recursive `atom` then `)`. WF on the
leftover (the `(` is consumed before recursing). -/
def atomParse : (input : List Char) → List (PTree × RightSublist input)
  | input =>
    (varTok.parse input).map (fun r => (PTree.var, r.2)) ++
    (lpTok.parse input).flatMap (fun r1 =>
      (atomParse r1.2.list).flatMap (fun r2 =>
        (rpTok.parse r2.2.list).map (fun r3 =>
          (PTree.paren r2.1, r1.2.trans (r2.2.trans r3.2)))))
  termination_by input => input.length
  decreasing_by exact r1.2.length_lt

def atom : Biparser Char Unit PTree where
  render t _ := atomRender t
  parse := atomParse
  parse_complete := by
    intro t _ rest
    induction t generalizing rest with
    | var =>
      refine ⟨RightSublist.cons 'x' rest, rfl, ?_⟩
      rw [atomParse]
      apply List.mem_append_left
      refine List.mem_map.mpr ⟨(⟨'x', by decide⟩, RightSublist.cons 'x' rest), ?_, rfl⟩
      show (⟨'x', by decide⟩, RightSublist.cons 'x' rest) ∈
        (if h : ('x' == 'x') = true then [((⟨'x', h⟩ : {c : Char // (c == 'x') = true}), RightSublist.cons 'x' rest)] else [])
      rw [dif_pos (by decide), List.mem_singleton]
    | paren t' ih =>
      obtain ⟨s', hs', hmem'⟩ := ih ([')'] ++ rest)
      have hrp : (⟨')', by decide⟩, RightSublist.cons ')' rest) ∈
          rpTok.parse (([')'] : List Char) ++ rest) := by
        show _ ∈ (if h : (')' == ')') = true then
          [((⟨')', h⟩ : {c : Char // (c == ')') = true}), RightSublist.cons ')' rest)] else [])
        rw [dif_pos (by decide), List.mem_singleton]
      have hexp : atomRender (PTree.paren t') ++ rest
          = '(' :: (atomRender t' ++ ([')'] ++ rest)) := by
        simp only [atomRender, List.cons_append, List.append_assoc]
      rw [hexp]
      refine ⟨(RightSublist.cons '(' (atomRender t' ++ ([')'] ++ rest))).trans
                (s'.trans ((RightSublist.cons ')' rest).cast hs'.symm)),
              by simp [RightSublist.trans, RightSublist.cons, RightSublist.cast_list], ?_⟩
      rw [atomParse]
      apply List.mem_append_right
      simp only [List.mem_flatMap, List.mem_map]
      refine ⟨(⟨'(', by decide⟩, RightSublist.cons '(' (atomRender t' ++ ([')'] ++ rest))), ?_,
              (t', s'), hmem',
              (⟨')', by decide⟩, (RightSublist.cons ')' rest).cast hs'.symm),
              mem_cast_gen rpTok.parse hs'.symm hrp, rfl⟩
      show _ ∈ (if h : ('(' == '(') = true then
        [((⟨'(', h⟩ : {c : Char // (c == '(') = true}), RightSublist.cons '(' (atomRender t' ++ ([')'] ++ rest)))] else [])
      rw [dif_pos (by decide), List.mem_singleton]

#eval (atomParse "((x))".toList).map (fun r => (r.1, r.2.list))
#eval String.ofList (atom.render (.paren (.paren .var)) ())   -- "((x))"
#print axioms atom
end LambdaLab.ParserExperimental1
