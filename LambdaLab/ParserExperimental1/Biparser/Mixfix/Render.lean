import LambdaLab.ParserExperimental1.Biparser.Mixfix.Leaves

/-!
# The telescope render

Walk the tree, emitting a nonempty whitespace run at every internal gap, chosen by a gap
counter `f : Nat → Nat` (`gap i = f i + 1` spaces) and threaded top-down — the plain-`Nat`
realization of `Parser/Mixfix/Render.lean`'s stateful telescope `Policy`. Gaps are emitted
through the very same combinator leaves the parser consumes (`lpGap`/`gapRp`/`gapOpGap`/
`opGap`), so `parse_complete` discharges each gap's round-trip from that combinator's own
law. A left-assoc `opl` node renders its head then a fold of `⊙ operand` **segments**
(`renderSeg`/`renderChain`), mutually with the tree render.
-/

namespace LambdaLab.ParserExperimental1.Mixfix

open LambdaLab.ParserExperimental1

mutual
/-- Telescope render: returns the chars and the next gap counter. -/
def Tree.render {G : Grammar} : {p : Nat} → Tree G p → (Nat → Nat) → Nat → List Char × Nat
  | _, .var c _,        _, i => ([c], i)
  | _, .paren t,        f, i =>
      ((lpGap G).render (lpVal, ()) ((), f i)
         ++ (Tree.render t f (i + 1)).1
         ++ (gapRp G).render ((), rpVal) (f (Tree.render t f (i + 1)).2, ()),
       (Tree.render t f (i + 1)).2 + 1)
  | _, .op k hk _ _ l r,  f, i =>
      ((Tree.render l f i).1
         ++ (gapOpGap G k hk).render ((), opVal G k hk, ())
              (f (Tree.render l f i).2, (), f ((Tree.render l f i).2 + 1))
         ++ (Tree.render r f ((Tree.render l f i).2 + 2)).1,
       (Tree.render r f ((Tree.render l f i).2 + 2)).2)
  | _, .opl k hk _ _ head chainHead chainRest, f, i =>
      let rH := Tree.render head f i
      let rS := renderSeg k hk chainHead f rH.2
      let rC := renderChain k hk chainRest f rS.2
      (rH.1 ++ rS.1 ++ rC.1, rC.2)
  | _, .pre k hk _ _ e,   f, i =>
      ((opGap G k hk).render (opVal G k hk, ()) ((), f i) ++ (Tree.render e f (i + 1)).1,
       (Tree.render e f (i + 1)).2)
  | _, .post k hk _ _ e,  f, i =>
      ((Tree.render e f i).1
         ++ (gapOp G k hk).render ((), opVal G k hk) (f (Tree.render e f i).2, ()),
       (Tree.render e f i).2 + 1)
  | _, .jux _ _ head chainHead chainRest, f, i =>
      let rH := Tree.render head f i
      let rS := renderJuxtSeg chainHead f rH.2
      let rC := renderJuxtChain chainRest f rS.2
      (rH.1 ++ rS.1 ++ rC.1, rC.2)
/-- One `⊙ operand` segment of a left-assoc chain: the infix operator with its gaps,
then the operand. -/
def renderSeg {G : Grammar} (k : Nat) (hk : k < G.ops.length)
    (c : Tree G (k + 1)) (f : Nat → Nat) (i : Nat) : List Char × Nat :=
  ((gapOpGap G k hk).render ((), opVal G k hk, ()) (f i, (), f (i + 1))
     ++ (Tree.render c f (i + 2)).1,
   (Tree.render c f (i + 2)).2)
/-- The rest of a left-assoc chain: a fold of `⊙ operand` segments. -/
def renderChain {G : Grammar} (k : Nat) (hk : k < G.ops.length) :
    TreeChain G (k + 1) → (Nat → Nat) → Nat → List Char × Nat
  | .nil,       _, i => ([], i)
  | .cons c cs, f, i =>
      let rS := renderSeg k hk c f i
      let rC := renderChain k hk cs f rS.2
      (rS.1 ++ rC.1, rC.2)
/-- One juxtaposition segment: a gap then the operand (no operator token). Generic in the
operand level `n` so the mutual block keeps a variable index. -/
def renderJuxtSeg {G : Grammar} {n : Nat} (c : Tree G n) (f : Nat → Nat) (i : Nat) :
    List Char × Nat :=
  ((sepRun G).render () (f i) ++ (Tree.render c f (i + 1)).1, (Tree.render c f (i + 1)).2)
/-- The rest of a juxtaposition chain: a fold of gap-then-operand segments. -/
def renderJuxtChain {G : Grammar} :
    {n : Nat} → TreeChain G n → (Nat → Nat) → Nat → List Char × Nat
  | _, .nil,       _, i => ([], i)
  | _, .cons c cs, f, i =>
      let rS := renderJuxtSeg c f i
      let rC := renderJuxtChain cs f rS.2
      (rS.1 ++ rC.1, rC.2)
end

/-- The chars of a nonempty juxtaposition chain `(chainHead, chainRest)` at counter `i`. -/
def renderJuxtChainFull {G : Grammar} {n : Nat}
    (chainHead : Tree G n) (chainRest : TreeChain G n) (f : Nat → Nat) (i : Nat) : List Char :=
  (renderJuxtSeg chainHead f i).1
    ++ (renderJuxtChain chainRest f (renderJuxtSeg chainHead f i).2).1

/-- The chars of a **nonempty** left-assoc chain `(chainHead, chainRest)` at counter `i`:
the first `⊙ operand` segment then the fold of the rest. This is exactly what the chain
collector `chainL` consumes. -/
def renderChainFull {G : Grammar} (k : Nat) (hk : k < G.ops.length)
    (chainHead : Tree G (k + 1)) (chainRest : TreeChain G (k + 1)) (f : Nat → Nat) (i : Nat) :
    List Char :=
  (renderSeg k hk chainHead f i).1
    ++ (renderChain k hk chainRest f (renderSeg k hk chainHead f i).2).1

#eval String.ofList (Tree.render sampleTree (fun _ => 0) 0).1        -- "a + b * c"
#eval String.ofList (Tree.render sampleTree2 (fun _ => 0) 0).1       -- "- a + b"
#eval String.ofList (Tree.render sampleLTree (fun _ => 0) 0).1       -- "a + b + c"
#eval String.ofList (Tree.render sampleLTree (fun i => i) 0).1       -- widening gaps

end LambdaLab.ParserExperimental1.Mixfix
