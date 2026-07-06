import LambdaLab.ParserExperimental1.Biparser.Combinators

namespace LambdaLab.ParserExperimental1

mutual
inductive Atom where
  | var  : Atom
  | paren : Expr → Atom
inductive Expr where
  | single : Atom → Expr
  | plus   : Atom → Expr → Expr
end

def varTok : Biparser Char Unit {c : Char // (c == 'x') = true} := tok (· == 'x')
def lpTok  : Biparser Char Unit {c : Char // (c == '(') = true} := tok (· == '(')
def rpTok  : Biparser Char Unit {c : Char // (c == ')') = true} := tok (· == ')')
def plTok  : Biparser Char Unit {c : Char // (c == '+') = true} := tok (· == '+')

mutual
def Atom.render : Atom → List Char
  | .var     => ['x']
  | .paren e => '(' :: Expr.render e ++ [')']
def Expr.render : Expr → List Char
  | .single a => Atom.render a
  | .plus a e => Atom.render a ++ '+' :: Expr.render e
end

mutual
def atomParse : (input : List Char) → List (Atom × RightSublist input)
  | input =>
    (varTok.parse input).map (fun r => (Atom.var, r.2)) ++
    (lpTok.parse input).flatMap (fun r1 =>
      (exprParse r1.2.list).flatMap (fun r2 =>
        (rpTok.parse r2.2.list).map (fun r3 =>
          (Atom.paren r2.1, r1.2.trans (r2.2.trans r3.2)))))
  termination_by input => (input.length, 0)
  decreasing_by exact Prod.Lex.left _ _ r1.2.length_lt
def exprParse : (input : List Char) → List (Expr × RightSublist input)
  | input => (atomParse input).flatMap (fun rA => afterAtomExpr rA.1 rA.2)
  termination_by input => (input.length, 2)
  decreasing_by
    · exact Prod.Lex.left _ _ rA.2.length_lt
    · exact Prod.Lex.right _ (by decide)
def afterAtomExpr {input : List Char} (head : Atom) (s : RightSublist input) :
    List (Expr × RightSublist input) :=
  (Expr.single head, s) ::
  (plTok.parse s.list).flatMap (fun rP =>
    (exprParse rP.2.list).map (fun rE =>
      (Expr.plus head rE.1, s.trans (rP.2.trans rE.2))))
  termination_by (s.list.length, 1)
  decreasing_by exact Prod.Lex.left _ _ rP.2.length_lt
end

/-! ## `parse_complete`: every rendering round-trips (mutual induction on `Atom`/`Expr`).

The grammar has no formatting freedom (fixed spelling, no whitespace), so the policy is
`Unit`. The two statements are proved by simultaneous structural recursion: `atomParse`'s
`paren` case recurses through `exprParse` on the inner expression; `exprParse`'s `plus`
case recurses through `atomParse` on the head and `exprParse` on the tail. Every recursive
call is on a strict subterm, so the mutual block is well-founded structurally. -/

mutual
theorem atomParse_complete : (a : Atom) → (rest : List Char) →
    ∃ s : RightSublist (Atom.render a ++ rest),
      s.list = rest ∧ (a, s) ∈ atomParse (Atom.render a ++ rest)
  | .var, rest => by
    refine ⟨RightSublist.cons 'x' rest, rfl, ?_⟩
    show (Atom.var, RightSublist.cons 'x' rest) ∈ atomParse (['x'] ++ rest)
    rw [atomParse]
    apply List.mem_append_left
    refine List.mem_map.mpr ⟨(⟨'x', by decide⟩, RightSublist.cons 'x' rest), ?_, rfl⟩
    show (⟨'x', by decide⟩, RightSublist.cons 'x' rest) ∈
      (if h : ('x' == 'x') = true then
        [((⟨'x', h⟩ : {c : Char // (c == 'x') = true}), RightSublist.cons 'x' rest)] else [])
    rw [dif_pos (by decide), List.mem_singleton]
  | .paren e, rest => by
    obtain ⟨s', hs', hmem'⟩ := exprParse_complete e ([')'] ++ rest)
    have hrp : (⟨')', by decide⟩, RightSublist.cons ')' rest) ∈
        rpTok.parse (([')'] : List Char) ++ rest) := by
      show _ ∈ (if h : (')' == ')') = true then
        [((⟨')', h⟩ : {c : Char // (c == ')') = true}), RightSublist.cons ')' rest)] else [])
      rw [dif_pos (by decide), List.mem_singleton]
    have hexp : Atom.render (Atom.paren e) ++ rest
        = '(' :: (Expr.render e ++ ([')'] ++ rest)) := by
      simp only [Atom.render, List.cons_append, List.append_assoc]
    rw [hexp]
    refine ⟨(RightSublist.cons '(' (Expr.render e ++ ([')'] ++ rest))).trans
              (s'.trans ((RightSublist.cons ')' rest).cast hs'.symm)),
            by simp [RightSublist.trans, RightSublist.cons, RightSublist.cast_list], ?_⟩
    rw [atomParse]
    apply List.mem_append_right
    simp only [List.mem_flatMap, List.mem_map]
    refine ⟨(⟨'(', by decide⟩, RightSublist.cons '(' (Expr.render e ++ ([')'] ++ rest))), ?_,
            (e, s'), hmem',
            (⟨')', by decide⟩, (RightSublist.cons ')' rest).cast hs'.symm),
            mem_cast_gen rpTok.parse hs'.symm hrp, rfl⟩
    show _ ∈ (if h : ('(' == '(') = true then
      [((⟨'(', h⟩ : {c : Char // (c == '(') = true}),
        RightSublist.cons '(' (Expr.render e ++ ([')'] ++ rest)))] else [])
    rw [dif_pos (by decide), List.mem_singleton]
theorem exprParse_complete : (e : Expr) → (rest : List Char) →
    ∃ s : RightSublist (Expr.render e ++ rest),
      s.list = rest ∧ (e, s) ∈ exprParse (Expr.render e ++ rest)
  | .single a, rest => by
    obtain ⟨s, hs, hmem⟩ := atomParse_complete a rest
    refine ⟨s, hs, ?_⟩
    show (Expr.single a, s) ∈ exprParse (Atom.render a ++ rest)
    rw [exprParse]
    simp only [List.mem_flatMap]
    exact ⟨(a, s), hmem, by rw [afterAtomExpr]; exact List.mem_cons_self⟩
  | .plus a e, rest => by
    obtain ⟨sE, hsE, hmemE⟩ := exprParse_complete e rest
    obtain ⟨sA, hsA, hmemA⟩ := atomParse_complete a ('+' :: (Expr.render e ++ rest))
    have hpl : (⟨'+', by decide⟩, RightSublist.cons '+' (Expr.render e ++ rest)) ∈
        plTok.parse ('+' :: (Expr.render e ++ rest)) := by
      show _ ∈ (if h : ('+' == '+') = true then
        [((⟨'+', h⟩ : {c : Char // (c == '+') = true}),
          RightSublist.cons '+' (Expr.render e ++ rest))] else [])
      rw [dif_pos (by decide), List.mem_singleton]
    have hexp : Expr.render (Expr.plus a e) ++ rest
        = Atom.render a ++ ('+' :: (Expr.render e ++ rest)) := by
      simp only [Expr.render, List.cons_append, List.append_assoc]
    rw [hexp]
    refine ⟨sA.trans (((RightSublist.cons '+' (Expr.render e ++ rest)).cast hsA.symm).trans sE),
            by simp [RightSublist.trans, RightSublist.cons, RightSublist.cast_list, hsE], ?_⟩
    rw [exprParse]
    simp only [List.mem_flatMap]
    refine ⟨(a, sA), hmemA, ?_⟩
    rw [afterAtomExpr]
    apply List.mem_cons_of_mem
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨(⟨'+', by decide⟩, (RightSublist.cons '+' (Expr.render e ++ rest)).cast hsA.symm),
           mem_cast_gen plTok.parse hsA.symm hpl, (e, sE), hmemE, rfl⟩
end

/-- The atom biparser: `x` or a parenthesized expression. Policy `Unit` (no freedom). -/
def atomBip : Biparser Char Unit Atom where
  render a _ := Atom.render a
  parse := atomParse
  parse_complete := fun a _ rest => atomParse_complete a rest

/-- The expression biparser: an atom, or `atom + expr` (right-associative). -/
def exprBip : Biparser Char Unit Expr where
  render e _ := Expr.render e
  parse := exprParse
  parse_complete := fun e _ rest => exprParse_complete e rest

#eval (exprParse "x+(x+x)".toList).filter (fun r => r.2.list.isEmpty) |>.length  -- 1
#eval String.ofList (exprBip.render (.plus .var (.single (.paren (.plus .var (.single .var))))) ())
  -- "x+(x+x)"
#print axioms exprBip
end LambdaLab.ParserExperimental1
