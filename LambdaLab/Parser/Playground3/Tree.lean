import LambdaLab.Parser.Playground3.Basic

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

namespace LambdaLab.Parser.Playground3

open LambdaLab.Parser

/-- A precedence *level*: the constraint placed on a tree's top operator. -/
inductive Level (G : Grammar) : Type where
| tighter   : G.Op → Level G
| tighterEq : G.Op → Level G
| loosest   : Level G

/-- The predicate a top operator `b` must satisfy to inhabit level `l`. -/
def Level.condition {G : Grammar} (l : Level G) : G.Op → Prop :=
  match l with
  | Level.tighter a   => fun b => Tighter G.tighter a b
  | Level.tighterEq a => fun b => TighterEq G.tighter a b
  | Level.loosest     => fun b => ∃ a, a ∈ G.loosest ∧ TighterEq G.tighter a b

def Level.innerChildren (tkns : NonEmptyList Token) : List (Level G) :=
  match tkns with
  | .last _ => []
  | .cons _ tkns => Level.loosest :: (innerChildren tkns)

def Level.children (op : G.Op) : NonEmptyList (Level G) :=
  match (G.operator op).fixity with
  | .closed => Level.innerChildren (G.operator op).nameParts
  | .infix .nonAssoc => [Level.tighter op] ++ [Level.tighter op]

mutual
  inductive Expr (G : Grammar) : Level G → Type where
  | op : (o : G.Op) → Level.condition l o → Children G (Level.children o) → Expr G l

  inductive Children (G : Grammar) : List (Level G) → Type where
  | nil : Children G nil
  | cons : Expr G l → Children G ls → Children G (l::ls)
end

end LambdaLab.Parser.Playground3
