import LambdaLab.ParserExperimental1.Biparser.Mixfix
import LambdaLab.ParserExperimental1.Biparser.Example

/-!
# The mixfix grammar with the `Parser` telescope whitespace policy, from combinators

Same grammar as `Mixfix.lean` (`atom = "x" | "(" expr ")"`, `expr = atom | atom "+" expr`,
right-assoc) but carrying the **telescope separator policy** of `Parser/Mixfix/Render.lean`:
a nonempty whitespace run at every internal gap, chosen by a state-threading policy.

Here the telescope is realized minimally as `Tel := Nat → Nat` — the run at gap `i` is
`f i + 1` spaces — threaded through the tree walk by a gap **counter** (the policy `State`,
`step` = `+1` per gap). `render_complete` is unsatisfiable (variable gaps), so this is a
weak-target (`parse_complete`-only) biparser, exactly where the extra whitespace freedom
lives.

**Combinators do the whitespace.** Each gap is `spaces1` (the verified `≥1`-space
biparser, `Example.lean`), pre-composed with its adjacent name token via `seq`
(`lpGap = seq lpTok spaces1`, …). So every gap's round-trip is discharged by that
combinator's own `parse_complete`, and pre-composing keeps each recursive call one
`flatMap` deep — the recursion skeleton, its termination, and its proof are the same
shape as `Mixfix.lean`. Only the *recursion* is hand-rolled (combinators can't carry a
termination measure through the recursive call); every *leaf* is a combinator.
-/

namespace LambdaLab.ParserExperimental1

/-- The telescope policy: the whitespace run at gap `i` is `f i + 1` spaces. -/
abbrev Tel : Type := Nat → Nat

def lpVal : {c : Char // (c == '(') = true} := ⟨'(', by decide⟩
def rpVal : {c : Char // (c == ')') = true} := ⟨')', by decide⟩
def plVal : {c : Char // (c == '+') = true} := ⟨'+', by decide⟩

/-- `"(" ++ gap` as one combinator (policy `Unit × Nat`). -/
def lpGap := seq lpTok spaces1
/-- `gap ++ ")"` as one combinator. -/
def gapRp := seq spaces1 rpTok
/-- `gap ++ "+" ++ gap` as one combinator. -/
def gapPlusGap := seq spaces1 (seq plTok spaces1)

/-! ### Render: walk the tree, emitting each gap's run, threading the gap counter. -/

mutual
def Atom.renderT : Atom → Tel → Nat → List Char × Nat
  | .var,     _, i => (['x'], i)
  | .paren e, f, i =>
      (lpGap.render (lpVal, ()) ((), f i)
        ++ (Expr.renderT e f (i + 1)).1
        ++ gapRp.render ((), rpVal) (f (Expr.renderT e f (i + 1)).2, ()),
       (Expr.renderT e f (i + 1)).2 + 1)
def Expr.renderT : Expr → Tel → Nat → List Char × Nat
  | .single a, f, i => Atom.renderT a f i
  | .plus a e, f, i =>
      ((Atom.renderT a f i).1
        ++ gapPlusGap.render ((), plVal, ())
             (f (Atom.renderT a f i).2, (), f ((Atom.renderT a f i).2 + 1))
        ++ (Expr.renderT e f ((Atom.renderT a f i).2 + 2)).1,
       (Expr.renderT e f ((Atom.renderT a f i).2 + 2)).2)
end

/-! ### Parse: accept `≥1` spaces at each gap; recursion one `flatMap` deep. -/

mutual
def atomParseWS : (input : List Char) → List (Atom × RightSublist input)
  | input =>
    (varTok.parse input).map (fun r => (Atom.var, r.2)) ++
    (lpGap.parse input).flatMap (fun r1 =>
      (exprParseWS r1.2.list).flatMap (fun r2 =>
        (gapRp.parse r2.2.list).map (fun r3 =>
          (Atom.paren r2.1, r1.2.trans (r2.2.trans r3.2)))))
  termination_by input => (input.length, 0)
  decreasing_by exact Prod.Lex.left _ _ r1.2.length_lt
def exprParseWS : (input : List Char) → List (Expr × RightSublist input)
  | input => (atomParseWS input).flatMap (fun rA => afterAtomWS rA.1 rA.2)
  termination_by input => (input.length, 2)
  decreasing_by
    · exact Prod.Lex.left _ _ rA.2.length_lt
    · exact Prod.Lex.right _ (by decide)
def afterAtomWS {input : List Char} (head : Atom) (s : RightSublist input) :
    List (Expr × RightSublist input) :=
  (Expr.single head, s) ::
  (gapPlusGap.parse s.list).flatMap (fun rP =>
    (exprParseWS rP.2.list).map (fun rE =>
      (Expr.plus head rE.1, s.trans (rP.2.trans rE.2))))
  termination_by (s.list.length, 1)
  decreasing_by exact Prod.Lex.left _ _ rP.2.length_lt
end

/-! ### `parse_complete`, generalized over the gap counter. -/

mutual
theorem atomParseWS_complete : (a : Atom) → (f : Tel) → (i : Nat) → (rest : List Char) →
    ∃ s : RightSublist ((Atom.renderT a f i).1 ++ rest),
      s.list = rest ∧ (a, s) ∈ atomParseWS ((Atom.renderT a f i).1 ++ rest)
  | .var, f, i, rest => by
    refine ⟨RightSublist.cons 'x' rest, rfl, ?_⟩
    show (Atom.var, RightSublist.cons 'x' rest) ∈ atomParseWS (['x'] ++ rest)
    rw [atomParseWS]
    apply List.mem_append_left
    refine List.mem_map.mpr ⟨(⟨'x', by decide⟩, RightSublist.cons 'x' rest), ?_, rfl⟩
    show (⟨'x', by decide⟩, RightSublist.cons 'x' rest) ∈
      (if h : ('x' == 'x') = true then
        [((⟨'x', h⟩ : {c : Char // (c == 'x') = true}), RightSublist.cons 'x' rest)] else [])
    rw [dif_pos (by decide), List.mem_singleton]
  | .paren e, f, i, rest => by
    obtain ⟨u1, hu1, hm1⟩ := lpGap.parse_complete (lpVal, ()) ((), f i)
      ((Expr.renderT e f (i + 1)).1 ++
        (gapRp.render ((), rpVal) (f (Expr.renderT e f (i + 1)).2, ()) ++ rest))
    obtain ⟨u2, hu2, hm2⟩ := exprParseWS_complete e f (i + 1)
      (gapRp.render ((), rpVal) (f (Expr.renderT e f (i + 1)).2, ()) ++ rest)
    obtain ⟨u3, hu3, hm3⟩ := gapRp.parse_complete ((), rpVal)
      (f (Expr.renderT e f (i + 1)).2, ()) rest
    have hexp : (Atom.renderT (Atom.paren e) f i).1 ++ rest
        = lpGap.render (lpVal, ()) ((), f i) ++
          ((Expr.renderT e f (i + 1)).1 ++
            (gapRp.render ((), rpVal) (f (Expr.renderT e f (i + 1)).2, ()) ++ rest)) := by
      simp only [Atom.renderT, List.append_assoc]
    rw [hexp]
    refine ⟨u1.trans ((u2.cast hu1.symm).trans (u3.cast hu2.symm)),
            by simp [RightSublist.trans, RightSublist.cast_list, hu3], ?_⟩
    rw [atomParseWS]
    apply List.mem_append_right
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨((lpVal, ()), u1), hm1,
           (e, u2.cast hu1.symm), mem_cast_gen exprParseWS hu1.symm hm2,
           (((), rpVal), u3.cast hu2.symm), mem_cast_gen gapRp.parse hu2.symm hm3, rfl⟩
theorem exprParseWS_complete : (e : Expr) → (f : Tel) → (i : Nat) → (rest : List Char) →
    ∃ s : RightSublist ((Expr.renderT e f i).1 ++ rest),
      s.list = rest ∧ (e, s) ∈ exprParseWS ((Expr.renderT e f i).1 ++ rest)
  | .single a, f, i, rest => by
    obtain ⟨s, hs, hmem⟩ := atomParseWS_complete a f i rest
    refine ⟨s, hs, ?_⟩
    show (Expr.single a, s) ∈ exprParseWS ((Atom.renderT a f i).1 ++ rest)
    rw [exprParseWS]
    simp only [List.mem_flatMap]
    exact ⟨(a, s), hmem, by rw [afterAtomWS]; exact List.mem_cons_self⟩
  | .plus a e, f, i, rest => by
    obtain ⟨uA, huA, hmA⟩ := atomParseWS_complete a f i
      (gapPlusGap.render ((), plVal, ())
          (f (Atom.renderT a f i).2, (), f ((Atom.renderT a f i).2 + 1)) ++
        ((Expr.renderT e f ((Atom.renderT a f i).2 + 2)).1 ++ rest))
    obtain ⟨uP, huP, hmP⟩ := gapPlusGap.parse_complete ((), plVal, ())
      (f (Atom.renderT a f i).2, (), f ((Atom.renderT a f i).2 + 1))
      ((Expr.renderT e f ((Atom.renderT a f i).2 + 2)).1 ++ rest)
    obtain ⟨uE, huE, hmE⟩ := exprParseWS_complete e f ((Atom.renderT a f i).2 + 2) rest
    have hexp : (Expr.renderT (Expr.plus a e) f i).1 ++ rest
        = (Atom.renderT a f i).1 ++
          (gapPlusGap.render ((), plVal, ())
              (f (Atom.renderT a f i).2, (), f ((Atom.renderT a f i).2 + 1)) ++
            ((Expr.renderT e f ((Atom.renderT a f i).2 + 2)).1 ++ rest)) := by
      simp only [Expr.renderT, List.append_assoc]
    rw [hexp]
    refine ⟨uA.trans ((uP.cast huA.symm).trans (uE.cast huP.symm)),
            by simp [RightSublist.trans, RightSublist.cast_list, huE], ?_⟩
    rw [exprParseWS]
    simp only [List.mem_flatMap]
    refine ⟨(a, uA), hmA, ?_⟩
    rw [afterAtomWS]
    apply List.mem_cons_of_mem
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨(((), plVal, ()), uP.cast huA.symm), mem_cast_gen gapPlusGap.parse huA.symm hmP,
           (e, uE.cast huP.symm), mem_cast_gen exprParseWS huP.symm hmE, rfl⟩
end

def atomBipWS : Biparser Char Tel Atom where
  render a f := (Atom.renderT a f 0).1
  parse := atomParseWS
  parse_complete := fun a f rest => atomParseWS_complete a f 0 rest

def exprBipWS : Biparser Char Tel Expr where
  render e f := (Expr.renderT e f 0).1
  parse := exprParseWS
  parse_complete := fun e f rest => exprParseWS_complete e f 0 rest

#eval String.ofList (exprBipWS.render (.plus .var (.single (.paren (.plus .var (.single .var))))) (fun _ => 0))
  -- "x + (x + x)"
#eval String.ofList (exprBipWS.render (.plus .var (.single .var)) (fun i => i))
  -- gap widths follow the counter

end LambdaLab.ParserExperimental1
