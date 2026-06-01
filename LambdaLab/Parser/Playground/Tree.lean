import LambdaLab.Parser.Playground.Basic

/-!
# Precedence-indexed parse trees

A `Tree G a` is an expression parseable *starting at precedence node `a`*.
Indexing by the node makes precedence **structural**: a tree at `a` can only
mention operators reachable from `a` via `tighter`, so unreachable ("dead")
operators are excluded by construction and no `covers` side-condition is
needed. The headline round-trip is stated for top-level expressions (`Expr`),
i.e. trees at a `loosest` node.

The mutual family:

* `Tree G a` — operator `a` applied (`op`), or a fall-through to something
  strictly tighter (`below`).
* `TreeBelow G a` — the strict step: an immediately-tighter `b ∈ tighter a`
  together with a `Tree G b`. This is `TransTighter` made structural.
* `Children G a f` — the holes of `a`, indexed by its fixity `f` so the layout
  is forced to match. Boundary holes sit at `Tree G a` (same level *or*
  tighter) or `TreeBelow G a` (strictly tighter), exactly tracking
  associativity:
  - `infixL` : left `Tree G a` (so `a-b-c` nests left), right `TreeBelow G a`.
  - `infixR` : mirror.
  - `infixN` : both `TreeBelow G a` (no chaining without parens).
  - `prefix`/`postfix` : the single boundary operand at `Tree G a` (stacks).
* `Woven G parts` — the interior weave: between consecutive name-parts sits a
  top-level `Expr`. `Woven [n₀,…,nₖ]` carries `k` interior holes.
* `Expr G` — a top-level expression: a `Tree G r` for some `r ∈ loosest`. Used
  both for the parser entry and for interior (delimited) holes, which admit the
  whole grammar.
-/

namespace LambdaLab.Parser.Playground

open LambdaLab.Parser

mutual
  /-- An expression at precedence node `a`. -/
  inductive Tree (G : Grammar) : G.Op → Type where
    | op   : (a : G.Op) → Children G a (G.operator a).fixity → Tree G a
    | next : TreeBelow G a → Tree G a

  /-- A strictly-tighter expression than `a`: step to an immediately-tighter
  operator and continue there. -/
  inductive TreeBelow (G : Grammar) : G.Op → Type where
    | mk : (b : G.Op) → b ∈ G.tighter a → Tree G b → TreeBelow G a

  /-- The holes of operator `a`, with placement and level dictated by fixity.
  (`a` is an index, not a parameter — a `mutual` block forces all of `Tree`,
  `Children`, … to share the same parameter list, namely just `G`.) -/
  inductive Children (G : Grammar) : G.Op → Fixity → Type where
    | closed  : Woven G (G.operator a).nameParts → Children G a .closed
    | prefix  : Woven G (G.operator a).nameParts → Tree G a → Children G a .prefix
    | postfix : Tree G a → Woven G (G.operator a).nameParts → Children G a .postfix
    | infixL  : Tree G a → Woven G (G.operator a).nameParts → TreeBelow G a →
                Children G a (.infix .left)
    | infixR  : TreeBelow G a → Woven G (G.operator a).nameParts → Tree G a →
                Children G a (.infix .right)
    | infixN  : TreeBelow G a → Woven G (G.operator a).nameParts → TreeBelow G a →
                Children G a (.infix .nonAssoc)

  /-- The interior weave of a non-empty name-part list: a top-level expression
  sits between each pair of consecutive name-parts. -/
  inductive Woven (G : Grammar) : List Token → Type where
    | last : (tk : Token) → Woven G [tk]
    | cons : (tk : Token) → Expr G → Woven G rest → Woven G (tk :: rest)

  /-- A top-level expression: an expression at one of the loosest operators. -/
  inductive Expr (G : Grammar) : Type where
    | mk : (r : G.Op) → r ∈ G.loosest → Tree G r → Expr G
end

mutual
  /-- Flatten a tree to its token stream. -/
  def Tree.flatten {G : Grammar} {a : G.Op} : Tree G a → List Token
    | .op _ ch => ch.flatten
    | .next tb => tb.flatten

  def TreeBelow.flatten {G : Grammar} {a : G.Op} : TreeBelow G a → List Token
    | .mk _ _ t => t.flatten

  def Children.flatten {G : Grammar} {a : G.Op} {f : Fixity} : Children G a f → List Token
    | .closed w     => w.flatten
    | .prefix w t   => w.flatten ++ t.flatten
    | .postfix t w  => t.flatten ++ w.flatten
    | .infixL l w r => l.flatten ++ w.flatten ++ r.flatten
    | .infixR l w r => l.flatten ++ w.flatten ++ r.flatten
    | .infixN l w r => l.flatten ++ w.flatten ++ r.flatten

  def Woven.flatten {G : Grammar} {parts : List Token} : Woven G parts → List Token
    | .last tk     => [tk]
    | .cons tk e w => [tk] ++ e.flatten ++ w.flatten

  def Expr.flatten {G : Grammar} : Expr G → List Token
    | .mk _ _ t => t.flatten
end

end LambdaLab.Parser.Playground
