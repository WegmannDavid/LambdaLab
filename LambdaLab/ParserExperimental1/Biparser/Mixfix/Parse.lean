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

#eval ((parseAt (G := sample) 0 "a + b * c".toList).filter (fun r => r.2.list.isEmpty)).length  -- 1
#eval ((parseAt (G := sample) 0 "( a + b )".toList).filter (fun r => r.2.list.isEmpty)).length  -- 1

end LambdaLab.ParserExperimental1.Mixfix
