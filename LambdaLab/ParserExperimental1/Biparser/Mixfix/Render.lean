import LambdaLab.ParserExperimental1.Biparser.Mixfix.Leaves

/-!
# The telescope render

Walk the tree, emitting a nonempty whitespace run at every internal gap, chosen by a gap
counter `f : Nat → Nat` (`gap i = f i + 1` spaces) and threaded top-down — the plain-`Nat`
realization of `Parser/Mixfix/Render.lean`'s stateful telescope `Policy`. The gaps are
emitted through the very same combinator leaves the parser consumes (`lpGap`/`gapRp`/
`gapOpGap`), so `parse_complete` can discharge each gap's round-trip from that combinator's
own law. Brackets appear only at `paren` nodes; the precedence index makes rendering
structural (no parenthesization decision).
-/

namespace LambdaLab.ParserExperimental1.Mixfix

open LambdaLab.ParserExperimental1

/-- Telescope render: returns the chars and the next gap counter. -/
def Tree.render {G : Grammar} : {p : Nat} → Tree G p → (Nat → Nat) → Nat → List Char × Nat
  | _, .var c _,        _, i => ([c], i)
  | _, .paren t,        f, i =>
      (lpGap.render (lpVal, ()) ((), f i)
         ++ (Tree.render t f (i + 1)).1
         ++ gapRp.render ((), rpVal) (f (Tree.render t f (i + 1)).2, ()),
       (Tree.render t f (i + 1)).2 + 1)
  | _, .op k hk _ _ l r,  f, i =>
      ((Tree.render l f i).1
         ++ (gapOpGap G k hk).render ((), opVal G k hk, ())
              (f (Tree.render l f i).2, (), f ((Tree.render l f i).2 + 1))
         ++ (Tree.render r f ((Tree.render l f i).2 + 2)).1,
       (Tree.render r f ((Tree.render l f i).2 + 2)).2)
  | _, .pre k hk _ _ e,   f, i =>
      ((opGap G k hk).render (opVal G k hk, ()) ((), f i) ++ (Tree.render e f (i + 1)).1,
       (Tree.render e f (i + 1)).2)

#eval String.ofList (Tree.render sampleTree (fun _ => 0) 0).1        -- "a + b * c"
#eval String.ofList (Tree.render sampleTree (fun i => i) 0).1        -- widening gaps
#eval String.ofList (Tree.render (Tree.paren sampleTree : Tree sample 0) (fun _ => 0) 0).1  -- "( a + b * c )"

end LambdaLab.ParserExperimental1.Mixfix
