import LambdaLab.Parser.Playground.Basic

/-!
# Precedence-indexed parse trees (strictly-tighter operands)

A `Tree G a` is an expression parseable *starting at precedence node `a`*.
Indexing by the node makes precedence **structural**: a tree at `a` can only
mention operators reachable from `a` via `tighter`, so unreachable ("dead")
operators are excluded by construction and no `covers` side-condition is
needed.

**Key design choice (unique-reading).** Every operand of an operator is
*strictly tighter* than that operator — there are **no same-level operands**.
Associativity, which classically wants a same-level operand (`x + y + z`
nesting `(x + y) + z`), is instead encoded by *iteration*: a left or right
associative operator carries an explicit non-empty spine of strictly-tighter
operands, and prefix/postfix operators carry an explicit stack. This is
isomorphic to the nested trees (no expressiveness lost — the canonical nesting
is the unique one), but it makes the operator's separator token a reliable
*discriminator*: the separator lives at level `a`, strictly looser than every
operand, so by acyclicity it can never appear at a top-level operand boundary
of any operand. That is exactly what unique decomposition needs.

The mutual family:

* `Tree G a` — operator `a` applied (`op`), or a fall-through to something
  strictly tighter (`next`).
* `TreeBelow G a` — the strict step: an immediately-tighter `b ∈ tighter a`
  together with a `Tree G b`.
* `Children G a f` — the holes of `a`, indexed by its fixity `f`. **All**
  boundary operands sit at `TreeBelow G a` (strictly tighter); chaining is via
  the spine/stack inductives below.
* `PrefixStack` / `PostfixTail` — a non-empty stack of one operator's
  prefix/postfix applications, bottoming out in a strictly-tighter operand.
* `InfixTail` — the non-empty `(separator, operand)` spine shared by the left
  and right associative cases.
* `Woven G parts` — the interior weave: between consecutive name-parts sits a
  top-level `Expr`.
* `Expr G` — a top-level expression: a `Tree G r` for some `r ∈ loosest`.
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
  Every boundary operand is `TreeBelow G a` (strictly tighter); chaining lives
  in the spine/stack inductives. -/
  inductive Children (G : Grammar) : G.Op → Fixity → Type where
    | closed  : Woven G (G.operator a).nameParts → Children G a .closed
    | prefix  : PrefixStack G a → Children G a .prefix
    | postfix : TreeBelow G a → PostfixTail G a → Children G a .postfix
    | infixL  : TreeBelow G a → InfixTail G a → Children G a (.infix .left)
    | infixR  : TreeBelow G a → InfixTail G a → Children G a (.infix .right)
    | infixN  : TreeBelow G a → Woven G (G.operator a).nameParts → TreeBelow G a →
                Children G a (.infix .nonAssoc)

  /-- A non-empty stack of `a`-prefix applications: each layer is `a`'s prefix
  weave, wrapping either a strictly-tighter body (`last`) or another `a`-prefix
  layer (`more`) — encoding ` - - x `. The recursion is on the right, so the
  body is reached carrying the outer leftover. -/
  inductive PrefixStack (G : Grammar) : G.Op → Type where
    | last : Woven G (G.operator a).nameParts → TreeBelow G a → PrefixStack G a
    | more : Woven G (G.operator a).nameParts → PrefixStack G a → PrefixStack G a

  /-- The trailing weaves of a postfix stack — the ` ! ! ` of ` x ! ! ` (the
  leading operand lives in `Children.postfix`). A non-empty right-nesting list,
  so the recursion always carries the outer leftover. -/
  inductive PostfixTail (G : Grammar) : G.Op → Type where
    | last : Woven G (G.operator a).nameParts → PostfixTail G a
    | cons : Woven G (G.operator a).nameParts → PostfixTail G a → PostfixTail G a

  /-- The associative tail shared by `infixL`/`infixR`: one-or-more
  `(separator-weave, tighter operand)` steps. With a leading `TreeBelow G a` head
  (in `Children`) this represents `x + y + z` as the spine `x , (+ y) , (+ z)`.
  The two fixities produce the same token stream and differ only by their
  `Children` constructor (forced by the operator's fixity), so they share this
  tail and are never compared against each other. -/
  inductive InfixTail (G : Grammar) : G.Op → Type where
    | last : Woven G (G.operator a).nameParts → TreeBelow G a → InfixTail G a
    | cons : Woven G (G.operator a).nameParts → TreeBelow G a → InfixTail G a → InfixTail G a

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
    | .closed w      => w.flatten
    | .prefix ps     => ps.flatten
    | .postfix tb pt => tb.flatten ++ pt.flatten
    | .infixL hd tl  => hd.flatten ++ tl.flatten
    | .infixR hd tl  => hd.flatten ++ tl.flatten
    | .infixN l w r  => l.flatten ++ w.flatten ++ r.flatten

  def PrefixStack.flatten {G : Grammar} {a : G.Op} : PrefixStack G a → List Token
    | .last w tb => w.flatten ++ tb.flatten
    | .more w ps => w.flatten ++ ps.flatten

  def PostfixTail.flatten {G : Grammar} {a : G.Op} : PostfixTail G a → List Token
    | .last w   => w.flatten
    | .cons w t => w.flatten ++ t.flatten

  def InfixTail.flatten {G : Grammar} {a : G.Op} : InfixTail G a → List Token
    | .last w tb   => w.flatten ++ tb.flatten
    | .cons w tb t => w.flatten ++ tb.flatten ++ t.flatten

  def Woven.flatten {G : Grammar} {parts : List Token} : Woven G parts → List Token
    | .last tk     => [tk]
    | .cons tk e w => [tk] ++ e.flatten ++ w.flatten

  def Expr.flatten {G : Grammar} : Expr G → List Token
    | .mk _ _ t => t.flatten
end

end LambdaLab.Parser.Playground
