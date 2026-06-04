import LambdaLab.Parser.Playground2.Basic

/-!
# Precedence-indexed parse trees (strictly-tighter operands)

A `Tree G l` is an expression whose **top operator** satisfies the level
constraint `l : Level G`. Indexing by a level makes precedence *structural*: a
tree may only mention operators allowed by `l` (and, recursively, tighter ones),
so unreachable ("dead") operators are excluded by construction and no `covers`
side-condition is needed.

A `Level` records *which* precedence constraint the top operator must meet:

* `Level.tighter a`   — strictly tighter than `a` (an operand position);
* `Level.tighterEq a` — tighter-or-equal to `a` (what parsing *at* node `a`
  yields: either `a` applied, or a strictly-tighter fall-through);
* `Level.loosest`     — reachable from some loosest operator (a top-level
  expression).

This single index folds the three former notions — the jump-tree `Tree G a`,
the strictly-tighter `TreeBelow G a`, and the top-level `Expr G` — into one
type:

* `Tree G (.tighterEq a)` is the old jump-tree at `a`;
* `Tree G (.tighter a)`   is the old `TreeBelow G a`;
* `Tree G .loosest`       is the old `Expr G`.

**Key design choice (unique-reading).** Every operand of an operator is
*strictly tighter* than that operator — there are **no same-level operands**.
Associativity, which classically wants a same-level operand (`x + y + z`
nesting `(x + y) + z`), is instead encoded by *iteration*: a left or right
associative operator carries an explicit non-empty spine of strictly-tighter
operands, and prefix/postfix operators carry an explicit stack. This is
isomorphic to the nested trees (no expressiveness lost — the canonical nesting
is the unique one), but it makes the operator's separator token a reliable
*discriminator*: the separator lives at the operator's own level, strictly
looser than every operand, so by acyclicity it can never appear at a top-level
operand boundary of any operand. That is exactly what unique decomposition
needs.

The mutual family:

* `Tree G l` — an operator applied at a node satisfying `l` (`op`). The node is
  packed in the constructor, so a tree carries its own root; `reindex` weakens
  the *level* without touching the tree.
* `Children G a f` — the holes of `a`, indexed by its fixity `f`. **All**
  boundary operands sit at `Tree G (.tighter a)` (strictly tighter); chaining is
  via the spine/stack inductives below.
* `PrefixStack` / `PostfixTail` — a non-empty stack of one operator's
  prefix/postfix applications, bottoming out in a strictly-tighter operand.
* `InfixTail` — the non-empty `(separator, operand)` spine shared by the left
  and right associative cases.
* `Woven G parts` — the interior weave: between consecutive name-parts sits a
  top-level expression (`Tree G .loosest`).
-/

namespace LambdaLab.Parser.Playground2

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

/-- The level condition is up-closed along `tighter`: if `a` satisfies level `l`
and `b` is tighter-or-equal to `a`, then `b` satisfies `l` too. -/
theorem Level.condition_trans {G : Grammar} {l : Level G} {a b : G.Op}
    (hc : Level.condition l a) (hab : TighterEq G.tighter a b) : Level.condition l b := by
  cases l with
  | tighter c   => exact Tighter.trans_tighterEq hc hab
  | tighterEq c => exact hc.trans hab
  | loosest     => obtain ⟨r, hr, hrc⟩ := hc; exact ⟨r, hr, hrc.trans hab⟩

/-- `o` is reachable from level `l`: some operator satisfying `l` reaches `o`. -/
def Level.reaches {G : Grammar} (l : Level G) (o : G.Op) : Prop :=
  ∃ a, Level.condition l a ∧ TighterEq G.tighter a o

mutual
  /-- An expression whose top operator satisfies level `l`. -/
  inductive Tree (G : Grammar) : Level G → Type where
    | op : (a : G.Op) → Level.condition l a → Children G a (G.operator a).fixity → Tree G l

  /-- The holes of operator `a`, with placement and level dictated by fixity.
  Every boundary operand is `Tree G (.tighter a)` (strictly tighter); chaining
  lives in the spine/stack inductives. -/
  inductive Children (G : Grammar) : G.Op → Fixity → Type where
    | closed  : Woven G (G.operator a).nameParts → Children G a .closed
    | prefix  : PrefixStack G a → Children G a .prefix
    | postfix : Tree G (.tighter a) → PostfixTail G a → Children G a .postfix
    | infixL  : Tree G (.tighter a) → InfixTail G a → Children G a (.infix .left)
    | infixR  : Tree G (.tighter a) → InfixTail G a → Children G a (.infix .right)
    | infixN  : Tree G (.tighter a) → Woven G (G.operator a).nameParts → Tree G (.tighter a) →
                Children G a (.infix .nonAssoc)

  /-- A non-empty stack of `a`-prefix applications: each layer is `a`'s prefix
  weave, wrapping either a strictly-tighter body (`last`) or another `a`-prefix
  layer (`more`) — encoding ` - - x `. The recursion is on the right, so the
  body is reached carrying the outer leftover. -/
  inductive PrefixStack (G : Grammar) : G.Op → Type where
    | last : Woven G (G.operator a).nameParts → Tree G (.tighter a) → PrefixStack G a
    | more : Woven G (G.operator a).nameParts → PrefixStack G a → PrefixStack G a

  /-- The trailing weaves of a postfix stack — the ` ! ! ` of ` x ! ! ` (the
  leading operand lives in `Children.postfix`). A non-empty right-nesting list,
  so the recursion always carries the outer leftover. -/
  inductive PostfixTail (G : Grammar) : G.Op → Type where
    | last : Woven G (G.operator a).nameParts → PostfixTail G a
    | cons : Woven G (G.operator a).nameParts → PostfixTail G a → PostfixTail G a

  /-- The associative tail shared by `infixL`/`infixR`: one-or-more
  `(separator-weave, tighter operand)` steps. With a leading `Tree G (.tighter a)`
  head (in `Children`) this represents `x + y + z` as the spine `x , (+ y) , (+ z)`.
  The two fixities produce the same token stream and differ only by their
  `Children` constructor (forced by the operator's fixity), so they share this
  tail and are never compared against each other. -/
  inductive InfixTail (G : Grammar) : G.Op → Type where
    | last : Woven G (G.operator a).nameParts → Tree G (.tighter a) → InfixTail G a
    | cons : Woven G (G.operator a).nameParts → Tree G (.tighter a) → InfixTail G a → InfixTail G a

  /-- The interior weave of a non-empty name-part list: a top-level expression
  sits between each pair of consecutive name-parts. -/
  inductive Woven (G : Grammar) : List Token → Type where
    | last : (tk : Token) → Woven G [tk]
    | cons : (tk : Token) → Tree G .loosest → Woven G rest → Woven G (tk :: rest)
end

mutual
  /-- Flatten a tree to its token stream. -/
  def Tree.flatten {G : Grammar} {l : Level G} : Tree G l → List Token
    | .op _ _ ch => ch.flatten

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
end

/-- Weaken the level of a tree along an implication of conditions. Since `op`
packs the operator it applies (not the level), this only adjusts the level
witness — the `Children` and hence the flattening are untouched. -/
def Tree.reindex {G : Grammar} {l l' : Level G}
    (h : ∀ b, Level.condition l b → Level.condition l' b) : Tree G l → Tree G l'
  | .op a hc ch => .op a (h a hc) ch

@[simp] theorem Tree.reindex_flatten {G : Grammar} {l l' : Level G}
    (h : ∀ b, Level.condition l b → Level.condition l' b) (t : Tree G l) :
    (t.reindex h).flatten = t.flatten := by
  cases t with | op _ _ ch => rfl

/-- The operator `a` applied to its `Children`, viewed at its own level
`.tighterEq a` (the witness is reflexivity). This is what the parser emits when
operator `a` matches; pinning the level lets `TighterEq.refl` elaborate. -/
def Tree.opSelf {G : Grammar} (a : G.Op) (ch : Children G a (G.operator a).fixity) :
    Tree G (.tighterEq a) :=
  Tree.op a TighterEq.refl ch

@[simp] theorem Tree.opSelf_flatten {G : Grammar} {a : G.Op}
    (ch : Children G a (G.operator a).fixity) : (Tree.opSelf a ch).flatten = ch.flatten := rfl

/-- Present a strictly-tighter tree at the tighter-or-equal level (the old
`TreeBelow.lift`/`next` fall-through: a `Tree G (.tighter a)` is in particular a
`Tree G (.tighterEq a)`). -/
def Tree.lift {G : Grammar} {a : G.Op} (t : Tree G (.tighter a)) : Tree G (.tighterEq a) :=
  Tree.reindex (l := Level.tighter a) (l' := Level.tighterEq a)
    (fun _ hb => (Tighter.toTighterEq hb : TighterEq G.tighter a _)) t

@[simp] theorem Tree.lift_flatten {G : Grammar} {a : G.Op} (t : Tree G (.tighter a)) :
    t.lift.flatten = t.flatten :=
  Tree.reindex_flatten _ t

/-- Re-root a tighter-or-equal tree at a looser node along a `tighter`-path. -/
def Tree.reindexEq {G : Grammar} {a b : G.Op} (hab : TighterEq G.tighter a b)
    (t : Tree G (.tighterEq b)) : Tree G (.tighterEq a) :=
  Tree.reindex (l := Level.tighterEq b) (l' := Level.tighterEq a)
    (fun _ hc => (TighterEq.trans hab hc : TighterEq G.tighter a _)) t

@[simp] theorem Tree.reindexEq_flatten {G : Grammar} {a b : G.Op}
    (hab : TighterEq G.tighter a b) (t : Tree G (.tighterEq b)) :
    (Tree.reindexEq hab t).flatten = t.flatten :=
  Tree.reindex_flatten _ t

end LambdaLab.Parser.Playground2
