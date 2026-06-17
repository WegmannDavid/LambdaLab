import LambdaLab.Parser.Basic


namespace LambdaLab.Parser.Mixfix

/-! ## Operator names with configurable interior holes

An operator's name is a non-empty sequence of name tokens. Between each
consecutive pair of tokens sits an **interior hole**, which is either recursive
(`loosest`, parsing the host language — the previous, default behaviour) or
parsed by **another language**, a `VerifiedParser` (`LambdaLab/Parser/Basic.lean`).

`VerifiedParser` is grammar-agnostic (it mentions only `Token`, `RightSublist`,
and its own result type), so embedding one does **not** create a
`Grammar → Operator → … → Grammar` type cycle: `Grammar` stays a plain
`structure`, and `Expr` keeps `G` as a parameter (the sub-tree stored at such a
hole is the bundle's own `Result`, never `Expr G'`). A `Grammar` plugs in via a
`toVerifiedParser` adapter (in `Verified.lean`); a binder is an interior hole
`sub varParser` admitting exactly one variable. -/

/-- An interior hole of an operator name: recursive (`loosest`) or another
language (a `VerifiedParser.{u}`, whose result type lives in `Type u`). -/
inductive InnerHole.{u} where
  | loosest : InnerHole
  | sub : VerifiedParser.{u} → InnerHole

/-- An operator name: a non-empty token sequence with an `InnerHole` between each
consecutive pair of tokens. A plain operator uses `.loosest` for every interior
hole (the previous behaviour); a sub-parser hole uses `.sub`. -/
inductive Notation.{u} where
  | last : Token → Notation
  | cons : Token → InnerHole.{u} → Notation → Notation

/-- The name tokens of a `Notation`, in order. -/
def Notation.toTokens.{u} : Notation.{u} → List Token
  | .last t        => [t]
  | .cons t _ rest => t :: rest.toTokens

inductive Operator.{u} where
| closed : Notation.{u} → Operator
| prefx : Notation.{u} → Operator
/-- Non-associative infix: both operands strictly tighter, so it does not nest
unparenthesized. -/
| infx : Notation.{u} → Operator
/-- Left-associative infix (`a ∘ b ∘ c = (a ∘ b) ∘ c`): the left operand is at
`.tighterEq` (chains), the right is strictly tighter. Its body is left-recursive
(leading `.tighterEq` hole), so it is parsed by an iterative fold (like `juxt`),
not `parseParts`. -/
| infxl : Notation.{u} → Operator
/-- Right-associative infix (`a ∘ b ∘ c = a ∘ (b ∘ c)`): the right operand is at
`.tighterEq` (chains), the left is strictly tighter. The trailing recursion
consumes the operator token first, so the ordinary `parseParts` handles it. -/
| infxr : Notation.{u} → Operator
| postfx : Notation.{u} → Operator
/-- Juxtaposition (function application by adjacency): a tokenless,
left-associative, tightest-binding operator. A grammar has at most one (see
`Grammar.juxtUnique`). -/
| juxt : Operator

/-- The name-part tokens of an operator, in body order. -/
def Operator.nameTokens.{u} : Operator.{u} → List Token
  | .closed n => n.toTokens
  | .prefx n => n.toTokens
  | .infx n => n.toTokens
  | .infxl n => n.toTokens
  | .infxr n => n.toTokens
  | .postfx n => n.toTokens
  | .juxt => []


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
(`Unambiguity.heads_distinct`), not assumed here.

`isVar` recognizes *variable* (identifier) tokens — atoms that are not operator
name parts. The parser admits any `isVar` token as a leaf `Expr.var` at every
level. For unique parses, a separate certificate requires `isVar` tokens to be
disjoint from operator name parts (so a token can't be read as both a variable
and an operator), exactly as `UniqueNameParts` handles name-part collisions. -/
structure Grammar.{u} where
  Op : Type
  operator : Op → Operator.{u}
  loosest : List Op
  tighter : Op → List Op
  tighter_wf : WellFounded (fun b a => b ∈ tighter a)
  /-- Recognizes variable (identifier) tokens — leaf atoms, distinct from operator
  name parts. -/
  isVar : Token → Bool
  /-- At most one operator is juxtaposition. Being tokenless, two juxtaposition
  operators would be indistinguishable in the token stream; this pins it to one
  (vacuously satisfied by grammars without juxtaposition). -/
  juxtUnique : ∀ o₁ o₂ : Op, operator o₁ = Operator.juxt → operator o₂ = Operator.juxt → o₁ = o₂

end LambdaLab.Parser.Mixfix
