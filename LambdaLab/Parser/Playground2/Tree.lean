import LambdaLab.Parser.Playground2.Basic

/-!
# Precedence-indexed parse trees (strictly-tighter operands)

Two inductive types carry the whole parse-tree family:

* `Tree G l` — an operator applied at a node satisfying the precedence
  constraint `l : Level G`.
* `Children G a s` — the body of operator `a`, at a structural position
  `s : Shape`.

Both follow the same idea: fold a whole family of former types into one, indexed
by a descriptor. `Tree` folds the old jump-tree / `TreeBelow` / `Expr` by the
*precedence constraint* `Level` (`.tighter`/`.tighterEq`/`.loosest`). `Children`
folds the old `Children` / `PrefixStack` / `PostfixTail` / `InfixTail` / `Woven`
by the *structural position* `Shape`:

* `.body f`     — a complete operator body of fixity `f` (was `Children`);
* `.prefix`     — a prefix stack `U⁺ T` (was `PrefixStack`);
* `.postTail`   — a postfix trailing `U⁺` (was `PostfixTail`);
* `.infixTail`  — an infix trailing `(U T)⁺` (was `InfixTail`);
* `.weave ps`   — one *unit* `U`: the name-parts `ps` interleaved with interior
  (loosest) operands (was `Woven`).

**Key design choice (unique-reading).** Every operand of an operator is
*strictly tighter* than that operator — there are **no same-level operands**.
Associativity is encoded by *iteration* (an explicit non-empty spine of
strictly-tighter operands), not by same-level nesting. This makes the operator's
separator token a reliable discriminator: it lives at the operator's own level,
strictly looser than every operand, so by acyclicity it can never sit at a
top-level operand boundary of any operand — exactly what unique decomposition
needs.
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

/-- A *structural position* within an operator's body: which of the former body
types a `Children` value represents. The only one carrying data is `.weave`,
holding the name-parts still to be emitted in the current unit. -/
inductive Shape where
  | body      : Fixity → Shape
  | «prefix»  : Shape
  | postTail  : Shape
  | infixTail : Shape
  | weave     : List Token → Shape

mutual
  /-- An expression whose top operator satisfies level `l`. -/
  inductive Tree (G : Grammar) : Level G → Type where
    | op : (a : G.Op) → Level.condition l a →
           Children G a (.body (G.operator a).fixity) → Tree G l

  /-- The body of operator `a` at structural position `s`. The constructors are
  the union of the five former body types, each pinned to its `Shape` so the
  fixity discipline is preserved (a closed body cannot sprout a boundary operand,
  `infixN` cannot repeat, etc.). -/
  inductive Children (G : Grammar) : G.Op → Shape → Type where
    -- one unit `U`: name-parts interleaved with interior (loosest) operands (was `Woven`)
    | wLast : (tk : Token) → Children G a (.weave [tk])
    | wCons : (tk : Token) → Tree G .loosest → Children G a (.weave rest) →
              Children G a (.weave (tk :: rest))
    -- complete bodies (was `Children`)
    | closed  : Children G a (.weave (G.operator a).nameParts) → Children G a (.body .closed)
    | «prefix» : Children G a .prefix → Children G a (.body .prefix)
    | «postfix» : Tree G (.tighter a) → Children G a .postTail → Children G a (.body .postfix)
    | infixL  : Tree G (.tighter a) → Children G a .infixTail → Children G a (.body (.infix .left))
    | infixR  : Tree G (.tighter a) → Children G a .infixTail → Children G a (.body (.infix .right))
    | infixN  : Tree G (.tighter a) → Children G a (.weave (G.operator a).nameParts) →
                Tree G (.tighter a) → Children G a (.body (.infix .nonAssoc))
    -- prefix stack `U⁺ T` (was `PrefixStack`)
    | psLast : Children G a (.weave (G.operator a).nameParts) → Tree G (.tighter a) →
               Children G a .prefix
    | psMore : Children G a (.weave (G.operator a).nameParts) → Children G a .prefix →
               Children G a .prefix
    -- postfix trailing `U⁺` (was `PostfixTail`)
    | ptLast : Children G a (.weave (G.operator a).nameParts) → Children G a .postTail
    | ptCons : Children G a (.weave (G.operator a).nameParts) → Children G a .postTail →
               Children G a .postTail
    -- infix trailing `(U T)⁺` (was `InfixTail`)
    | itLast : Children G a (.weave (G.operator a).nameParts) → Tree G (.tighter a) →
               Children G a .infixTail
    | itCons : Children G a (.weave (G.operator a).nameParts) → Tree G (.tighter a) →
               Children G a .infixTail → Children G a .infixTail
end

mutual
  /-- Flatten a tree to its token stream. -/
  def Tree.flatten {G : Grammar} {l : Level G} : Tree G l → List Token
    | .op _ _ ch => ch.flatten

  /-- Flatten a body to its token stream (one function for all positions). -/
  def Children.flatten {G : Grammar} {a : G.Op} {s : Shape} : Children G a s → List Token
    | .wLast tk      => [tk]
    | .wCons tk e w  => [tk] ++ e.flatten ++ w.flatten
    | .closed w      => w.flatten
    | .«prefix» ps   => ps.flatten
    | .«postfix» tb pt => tb.flatten ++ pt.flatten
    | .infixL hd tl  => hd.flatten ++ tl.flatten
    | .infixR hd tl  => hd.flatten ++ tl.flatten
    | .infixN l w r  => l.flatten ++ w.flatten ++ r.flatten
    | .psLast w tb   => w.flatten ++ tb.flatten
    | .psMore w ps   => w.flatten ++ ps.flatten
    | .ptLast w      => w.flatten
    | .ptCons w t    => w.flatten ++ t.flatten
    | .itLast w tb   => w.flatten ++ tb.flatten
    | .itCons w tb t => w.flatten ++ tb.flatten ++ t.flatten
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
def Tree.opSelf {G : Grammar} (a : G.Op) (ch : Children G a (.body (G.operator a).fixity)) :
    Tree G (.tighterEq a) :=
  Tree.op a TighterEq.refl ch

@[simp] theorem Tree.opSelf_flatten {G : Grammar} {a : G.Op}
    (ch : Children G a (.body (G.operator a).fixity)) :
    (Tree.opSelf a ch).flatten = ch.flatten := rfl

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
