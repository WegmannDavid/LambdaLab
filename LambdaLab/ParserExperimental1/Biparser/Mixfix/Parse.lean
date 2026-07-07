import LambdaLab.ParserExperimental1.Biparser.Mixfix.Leaves

/-!
# The generic combinator parser

A char-level parser for the data-driven grammar, producing precedence-indexed `Tree G p`.
Right-associative precedence climbing:

* an **atom** is a variable, or `"(" expr ")"` (a bracketed level-0 tree);
* an **operator** node at precedence `k ≥ p` parses its left operand one level tighter
  (`parseAt (k+1)`, on the *same* input — the source of the level recursion) then, after
  the operator token, its right operand at the same level (`parseAt k`, on shorter input).

Every gap is `spaces1` pre-composed with its adjacent token (`lpGap`, `gapRp`,
`gapOpGap`), so each recursive call is one `flatMap` deep — the `afterLeft` helper keeps
the right-operand call shallow, as `afterAtomWS` did in `Telescope.lean`. Termination is
the lexicographic measure `(input.length, G.ops.length - level)`: descending a level is
same-input but lowers the second component; every other recursive call consumes ≥1 char.
-/

namespace LambdaLab.ParserExperimental1.Mixfix

open LambdaLab.ParserExperimental1

mutual
def parseAt {G : Grammar} (p : Nat) (input : List Char) : List (Tree G p × RightSublist input) :=
  ((varWord G).parse input).map (fun r => (Tree.var r.1, r.2)) ++
  ((lpGap G).parse input).flatMap (fun r1 =>
    (parseAt 0 r1.2.list).flatMap (fun r2 =>
      ((gapRp G).parse r2.2.list).map (fun r3 =>
        (Tree.paren r2.1, r1.2.trans (r2.2.trans r3.2))))) ++
  (List.range G.ops.length).flatMap (fun k =>
    if hk : k < G.ops.length then
      if hp : p ≤ k then
        if hi : G.opFixity k hk = .infixr then
          (parseAt (k + 1) input).flatMap (fun rL => afterInfixr p k hk hi hp rL.1 rL.2)
        else if hl : G.opFixity k hk = .infixl then
          (parseAt (k + 1) input).flatMap (fun rH =>
            (chainL k hk rH.2.list).map (fun rC =>
              (Tree.opl k hk hl hp rH.1 rC.1.1 rC.1.2, rH.2.trans rC.2)))
        else if hr : G.opFixity k hk = .prefix then
          ((opGap G k hk).parse input).flatMap (fun rO => afterPre p k hk hr hp rO.2)
        else if hpo : G.opFixity k hk = .postfix then
          (parseAt (k + 1) input).flatMap (fun rO =>
            ((gapOp G k hk).parse rO.2.list).map (fun rP =>
              (Tree.post k hk hpo hp rO.1, rO.2.trans rP.2)))
        else []
      else []
    else []) ++
  (if hj : G.juxt = true then
    if hpj : p ≤ G.ops.length then
      (parseAt (G.ops.length + 1) input).flatMap (fun rH =>
        (juxtChainL rH.2.list).map (fun rC =>
          (Tree.jux hj hpj rH.1 rC.1.1 rC.1.2, rH.2.trans rC.2)))
    else []
   else [])
  termination_by (input.length, (G.ops.length + 1 - p) * 4)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ r1.2.length_lt
      | exact Prod.Lex.left _ _ rL.2.length_lt
      | exact Prod.Lex.left _ _ rH.2.length_lt
      | exact Prod.Lex.left _ _ rO.2.length_lt
      | (apply Prod.Lex.right; omega)
def afterInfixr {G : Grammar} (p k : Nat) (hk : k < G.ops.length)
    (hfix : G.opFixity k hk = .infixr) (hp : p ≤ k)
    (left : Tree G (k + 1)) {input : List Char} (s : RightSublist input) :
    List (Tree G p × RightSublist input) :=
  ((gapOpGap G k hk).parse s.list).flatMap (fun rM =>
    (parseAt k rM.2.list).map (fun rR =>
      (Tree.op k hk hfix hp left rR.1, s.trans (rM.2.trans rR.2))))
  termination_by (s.list.length, 0)
  decreasing_by exact Prod.Lex.left _ _ rM.2.length_lt
def afterPre {G : Grammar} (p k : Nat) (hk : k < G.ops.length)
    (hfix : G.opFixity k hk = .prefix) (hp : p ≤ k)
    {input : List Char} (s : RightSublist input) :
    List (Tree G p × RightSublist input) :=
  (parseAt (k + 1) s.list).map (fun rE =>
    (Tree.pre k hk hfix hp rE.1, s.trans rE.2))
  termination_by (s.list.length, (G.ops.length + 1 - (k + 1)) * 4 + 3)
  decreasing_by apply Prod.Lex.right; omega
/-- One `⊙ operand` segment: the infix operator token (with gaps), then an operand parsed
one level tighter. -/
def segParse {G : Grammar} (k : Nat) (hk : k < G.ops.length) (input : List Char) :
    List (Tree G (k + 1) × RightSublist input) :=
  ((gapOpGap G k hk).parse input).flatMap (fun rM =>
    (parseAt (k + 1) rM.2.list).map (fun rE => (rE.1, rM.2.trans rE.2)))
  termination_by (input.length, 0)
  decreasing_by exact Prod.Lex.left _ _ rM.2.length_lt
/-- A **nonempty** left-assoc chain: one or more `⊙ operand` segments, as a head operand
plus the rest (a `TreeChain`). Modelled on the verified `«some»`/`someParse`, so its
self-recursion is one `flatMap` deep. -/
def chainL {G : Grammar} (k : Nat) (hk : k < G.ops.length) (input : List Char) :
    List ((Tree G (k + 1) × TreeChain G (k + 1)) × RightSublist input) :=
  (segParse k hk input).flatMap (fun r =>
    ((r.1, TreeChain.nil), r.2) ::
      (chainL k hk r.2.list).map (fun r' =>
        ((r.1, TreeChain.cons r'.1.1 r'.1.2), r.2.trans r'.2)))
  termination_by (input.length, 1)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ r.2.length_lt
      | (apply Prod.Lex.right; omega)
/-- One juxtaposition segment: a gap then an operand (no operator token). -/
def juxtSegParse {G : Grammar} (input : List Char) :
    List (Tree G (G.ops.length + 1) × RightSublist input) :=
  ((sepRun G).parse input).flatMap (fun rG =>
    (parseAt (G.ops.length + 1) rG.2.list).map (fun rE => (rE.1, rG.2.trans rE.2)))
  termination_by (input.length, 0)
  decreasing_by exact Prod.Lex.left _ _ rG.2.length_lt
/-- A nonempty juxtaposition chain: one or more gap-then-operand segments. -/
def juxtChainL {G : Grammar} (input : List Char) :
    List ((Tree G (G.ops.length + 1) × TreeChain G (G.ops.length + 1)) × RightSublist input) :=
  (juxtSegParse input).flatMap (fun r =>
    ((r.1, TreeChain.nil), r.2) ::
      (juxtChainL r.2.list).map (fun r' =>
        ((r.1, TreeChain.cons r'.1.1 r'.1.2), r.2.trans r'.2)))
  termination_by (input.length, 1)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ r.2.length_lt
      | (apply Prod.Lex.right; omega)
end

#eval ((parseAt (G := sample) 0 "a + b * c".toList).filter (fun r => r.2.list.isEmpty)).length  -- 1
#eval ((parseAt (G := sample) 0 "( a + b )".toList).filter (fun r => r.2.list.isEmpty)).length  -- 1

end LambdaLab.ParserExperimental1.Mixfix
