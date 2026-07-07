import LambdaLab.ParserExperimental1.Biparser.Example

/-!
# A generic, data-driven mixfix grammar — combinator weak-biparser, Stage 1

`Telescope.lean` verified *one* hardcoded grammar (parens + right-assoc `+`) from
combinators. This generalizes it to a **data-driven** grammar: a precedence-ordered
table of right-associative infix operator characters, plus a variable predicate.
Brackets `(`/`)` and the separator space are built in.

The tree is **precedence-indexed** (`Tree G p` binds at least as tightly as level `p`),
the analogue of `Parser/Mixfix`'s `Level`-indexed `Expr G` but over a plain `Nat`
precedence rather than a DAG — so `render` never has to *decide* where to parenthesize;
the index makes it structural (a `paren` node is the only place brackets appear).

The **telescope** `render` (a nonempty whitespace run at every internal gap, chosen by a
gap counter `f : Nat → Nat`) is built from the same combinator leaves the parser uses
(`lpGap`/`gapRp`/`gapOpGap` — each a gap `spaces1` pre-composed with its adjacent token
via `seq`), so `parse_complete` (later stage) composes each gap's round-trip from that
combinator's own law, exactly as in `Telescope.lean`.
-/

namespace LambdaLab.ParserExperimental1.Mixfix

open LambdaLab.ParserExperimental1

/-- A generic grammar: `ops[k]` is the right-associative infix operator character at
precedence level `k` (higher index = binds tighter); `isVar` recognizes variable
characters. Brackets `(`/`)` and the space separator are built in and assumed disjoint
from `ops` and `isVar`. -/
structure Grammar where
  ops : List Char
  isVar : Char → Bool

/-- A precedence-indexed parse tree: an inhabitant of `Tree G p` is an expression whose
top operator binds **at least as tightly as** level `p`. A `var`/`paren` is an atom
(tighter than everything, so valid at any `p`); an `op k` node has precedence `k` and is
valid at levels `p ≤ k`. Right-associative: the left operand is one level tighter
(`k+1`), the right operand chains at the same level (`k`). -/
inductive Tree (G : Grammar) : Nat → Type where
  | var   {p : Nat} (c : Char) : G.isVar c = true → Tree G p
  | paren {p : Nat} : Tree G 0 → Tree G p
  | op    {p : Nat} (k : Nat) (hk : k < G.ops.length) (hp : p ≤ k) :
            Tree G (k + 1) → Tree G k → Tree G p

/-! ### Combinator leaves (all single-char tokens; gaps are `spaces1`). -/

def varTok (G : Grammar) : Biparser Char Unit {c : Char // G.isVar c = true} :=
  tok (fun c => G.isVar c)
def lparen : Biparser Char Unit {c : Char // (c == '(') = true} := tok (· == '(')
def rparen : Biparser Char Unit {c : Char // (c == ')') = true} := tok (· == ')')
def opTok (G : Grammar) (k : Nat) (hk : k < G.ops.length) :
    Biparser Char Unit {c : Char // (c == G.ops[k]'hk) = true} := tok (· == G.ops[k]'hk)

/-- `"(" ++ gap`. -/
def lpGap := seq lparen spaces1
/-- `gap ++ ")"`. -/
def gapRp := seq spaces1 rparen
/-- `gap ++ opₖ ++ gap`. -/
def gapOpGap (G : Grammar) (k : Nat) (hk : k < G.ops.length) :=
  seq spaces1 (seq (opTok G k hk) spaces1)

/-- The bracket / operator token values used by `render`. -/
def lpVal : {c : Char // (c == '(') = true} := ⟨'(', by decide⟩
def rpVal : {c : Char // (c == ')') = true} := ⟨')', by decide⟩
def opVal (G : Grammar) (k : Nat) (hk : k < G.ops.length) :
    {c : Char // (c == G.ops[k]'hk) = true} := ⟨G.ops[k]'hk, beq_self_eq_true _⟩

/-- Telescope render: walk the tree, emitting each internal gap's run (via the same
combinator leaves the parser consumes) and threading the gap counter `i`. Returns the
chars and the next counter. Brackets appear only at `paren` nodes. -/
def Tree.render {G : Grammar} : {p : Nat} → Tree G p → (Nat → Nat) → Nat → List Char × Nat
  | _, .var c _,        _, i => ([c], i)
  | _, .paren t,        f, i =>
      (lpGap.render (lpVal, ()) ((), f i)
         ++ (Tree.render t f (i + 1)).1
         ++ gapRp.render ((), rpVal) (f (Tree.render t f (i + 1)).2, ()),
       (Tree.render t f (i + 1)).2 + 1)
  | _, .op k hk _ l r,  f, i =>
      ((Tree.render l f i).1
         ++ (gapOpGap G k hk).render ((), opVal G k hk, ())
              (f (Tree.render l f i).2, (), f ((Tree.render l f i).2 + 1))
         ++ (Tree.render r f ((Tree.render l f i).2 + 2)).1,
       (Tree.render r f ((Tree.render l f i).2 + 2)).2)

/-! ### A sample grammar for `#eval` sanity checks. -/

/-- `+` (prec 0, loose) and `*` (prec 1, tight); lowercase letters are variables. -/
def sample : Grammar where
  ops := ['+', '*']
  isVar := fun c => 'a' ≤ c && c ≤ 'z'

/-- `a + b * c` as a tree: `+` at prec 0 with right operand `b * c` at prec 1. -/
def sampleTree : Tree sample 0 :=
  .op 0 (by decide) (by decide)
    (.var 'a' (by decide))
    (.op 1 (by decide) (by decide) (.var 'b' (by decide)) (.var 'c' (by decide)))

#eval String.ofList (Tree.render sampleTree (fun _ => 0) 0).1        -- "a + b * c"
#eval String.ofList (Tree.render sampleTree (fun i => i) 0).1        -- widening gaps
#eval String.ofList (Tree.render (Tree.paren sampleTree : Tree sample 0) (fun _ => 0) 0).1  -- "( a + b * c )"

end LambdaLab.ParserExperimental1.Mixfix
