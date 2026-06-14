import LambdaLab.Parser.Basic


namespace LambdaLab.Parser.Playground3



inductive NonEmptyList (α : Type) where
| last : α → NonEmptyList α
| cons : α → NonEmptyList α → NonEmptyList α

def NonEmptyList.toList : NonEmptyList α → List α
  | last x => [x]
  | cons x xs => x :: xs.toList

inductive Operator : Type where
| closed : NonEmptyList Token → Operator
| prefx : NonEmptyList Token → Operator
| infx : NonEmptyList Token → Operator
| postfx : NonEmptyList Token → Operator

/-- The name-part tokens of an operator, in body order. -/
def Operator.nameTokens : Operator → List Token
  | .closed tkns => tkns.toList
  | .prefx tkns => tkns.toList
  | .infx tkns => tkns.toList
  | .postfx tkns => tkns.toList


/-- Reachability through the `tighter` successor lists: `TighterEq t a b`
holds when `b` can be reached from `a` by repeatedly stepping into `t`, i.e.
"`b` binds at least as tightly as `a`". This is the precedence order induced by
a successor function `t : Op → List Op`. Defined over the raw `t` (not over a
`Grammar`) so it can appear in `Grammar`'s own well-formedness fields. -/
inductive TighterEq {Op : Type} (t : Op → List Op) : Op → Op → Prop where
  | refl {a} : TighterEq t a a
  | step {a b c} : b ∈ t a → TighterEq t b c → TighterEq t a c

/-- The **strict** version of `TighterEq`: the *transitive* (but not
reflexive) closure of `tighter`. `Tighter t a b` holds when `b` is
reached from `a` by **one or more** `tighter` steps — i.e. "`b` binds *strictly*
more tightly than `a`". Like `TighterEq`, defined over the raw successor
function `t` rather than a `Grammar`, so it can sit in `Grammar`'s
well-formedness fields and be reused (`Tighter G.tighter`). -/
inductive Tighter {Op : Type} (t : Op → List Op) : Op → Op → Prop where
  | base {a b} : b ∈ t a → Tighter t a b
  | step {a b c} : b ∈ t a → Tighter t b c → Tighter t a c

/-- A strictly-tighter path is in particular a (reflexive-transitive)
tighter-path. -/
theorem Tighter.toTighterEq {Op : Type} {t : Op → List Op} {a b : Op}
    (h : Tighter t a b) : TighterEq t a b := by
  induction h with
  | base hmem => exact TighterEq.step hmem TighterEq.refl
  | step hmem _ ih => exact TighterEq.step hmem ih

/-- A grammar: an (abstract) operator-name type `Op`, the declaration of each
operator, and the precedence structure.

**Precedence** is a successor graph — a DAG. `tighter o` lists the operators
*immediately* tighter than `o`; the full order is reachability
(`TighterEq tighter`). `loosest` lists the **source** operators (the loosest
ones, where the parser starts); a DAG may have several. One well-formedness
field pins it down:

* `tighter_wf` — going tighter is **well-founded** (no infinite ever-tighter
  chain). This is *both* the acyclicity guarantee *and* the termination measure
  for the parser *and* for the precedence-indexed `Tree` (see `Tree.lean`), so
  no separate finiteness witness is needed.

There is deliberately **no coverage/reachability field**. `Tree G` is indexed
by precedence node, so a tree rooted at a `loosest` operator can only mention
operators reachable from it — unreachable ("dead") operators are excluded
*structurally* rather than forbidden by an axiom, and the round-trip theorem is
stated for trees at a `loosest` node.

The order is left **partial** (a DAG): incomparable operators are allowed and
must be parenthesized relative to one another. Forcing it total — a single
chain, one operator per rung, no ties — would be an *extra* field, not a
missing one.

There is deliberately no token-`lookup` field: the parser keys on name-part
tokens directly, and the unique-reading condition (distinct leading tokens) is
*derived* from the user-facing `UniqueNameParts` certificate
(`Unambiguity.heads_distinct`), not assumed here. -/
structure Grammar where
  Op : Type
  operator : Op → Operator
  loosest : List Op
  tighter : Op → List Op
  tighter_wf : WellFounded (fun b a => b ∈ tighter a)

end LambdaLab.Parser.Playground3
