import LambdaLab.Parser.Basic


namespace LambdaLab.Parser.Playground


/-- How an operator associates when it chains with operators of equal
precedence. Only `infix` operators carry one. -/
inductive Associativity where
  | left
  | right
  | nonAssoc
deriving DecidableEq, Repr

/-- An operator's fixity — equivalently, whether its token shape begins
and/or ends with a recursive hole. Writing `nᵢ` for name-parts and `_` for
holes:

* `closed`  : `n₀ _ n₁ _ … _ nₖ`   — holes only *between* name-parts
* `prefix`  : `n₀ _ n₁ _ … _ nₖ _` — extra *trailing* hole
* `postfix` : `_ n₀ _ … _ nₖ`      — extra *leading* hole
* `infix`   : `_ n₀ _ … _ nₖ _`    — both boundary holes, plus an associativity
-/
inductive Fixity where
  | closed
  | prefix
  | postfix
  | infix (assoc : Associativity)
deriving DecidableEq, Repr

/-- The number of recursive holes a fixity contributes, given the number `k`
of name-parts. A `closed` operator has `k - 1` interior holes; `prefix` and
`postfix` add one boundary hole each; `infix` adds both. -/
def Fixity.arity : Fixity → Nat → Nat
  | .closed,  k => k - 1
  | .prefix,  k => k
  | .postfix, k => k
  | .infix _, k => k + 1

/-- A mixfix operator declaration: a fixity and a non-empty list of literal
name-parts. The recursive holes are *not* stored — their count and placement
follow from the fixity and `nameParts.length` (see `Fixity.arity`). An operator
describes token *shape* only; it carries no semantics, and crucially no
precedence — precedence is a *relative* ranking, so it lives on the `Grammar`
(see `Grammar.tighter`). Associativity, by contrast, is intrinsic to the
operator and rides along inside its `infix` `Fixity`. -/
structure Operator where
  fixity : Fixity
  nameParts : List Token
  nameParts_ne : nameParts ≠ []

/-- The number of recursive holes (child trees) of an operator. -/
def Operator.arity (o : Operator) : Nat :=
  o.fixity.arity o.nameParts.length

/-- The operator's leading name-part — the literal that identifies it. For
`closed`/`prefix` it is the operator's very first token; for `postfix`/`infix`
it is the first token *after* the leading operand. Either way it is the token a
parser keys on once it reaches an operand boundary, so it is what `lookup`
resolves. -/
def Operator.head (o : Operator) : Token :=
  o.nameParts.head o.nameParts_ne

/-- A nullary constant: a `closed` operator with a single name-part, hence
zero holes (e.g. `zero`, `true`). -/
def Operator.const (s : Token) : Operator where
  fixity := .closed
  nameParts := [s]
  nameParts_ne := by simp

@[simp] theorem Operator.const_arity (s : Token) : (Operator.const s).arity = 0 := rfl

@[simp] theorem Operator.const_head (s : Token) : (Operator.const s).head = s := rfl

/-- Reachability through the `tighter` successor lists: `ReachTighter t a b`
holds when `b` can be reached from `a` by repeatedly stepping into `t`, i.e.
"`b` binds at least as tightly as `a`". This is the precedence order induced by
a successor function `t : Op → List Op`. Defined over the raw `t` (not over a
`Grammar`) so it can appear in `Grammar`'s own well-formedness fields. -/
inductive ReachTighter {Op : Type} (t : Op → List Op) : Op → Op → Prop where
  | refl {a} : ReachTighter t a a
  | step {a b c} : b ∈ t a → ReachTighter t b c → ReachTighter t a c

/-- A grammar: an (abstract) operator-name type `Op`, the declaration of each
operator, the precedence structure, and a `lookup` resolving a token to the
operator it leads.

**Precedence** is a successor graph — a DAG. `tighter o` lists the operators
*immediately* tighter than `o`; the full order is reachability
(`ReachTighter tighter`). `loosest` lists the **source** operators (the loosest
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

`lookup_spec` is the well-formedness condition — `lookup` inverts
`Operator.head`: a token resolves to `o` exactly when it is `o`'s leading
name-part. Since `lookup` is a function, this also forces *distinct leading
tokens* across operators — the unique-reading condition that lets a parser
recover an operator from the token stream. -/
structure Grammar where
  Op : Type
  operator : Op → Operator
  loosest : List Op
  tighter : Op → List Op
  tighter_wf : WellFounded (fun b a => b ∈ tighter a)
  lookup : Token → Option Op
  lookup_spec : ∀ o tkn, (operator o).head = tkn ↔ lookup tkn = some o

/-- The fixity of a grammar operator. -/
def Grammar.fixity (G : Grammar) (o : G.Op) : Fixity := (G.operator o).fixity

/-- The arity (hole count) of a grammar operator. -/
def Grammar.arity (G : Grammar) (o : G.Op) : Nat := (G.operator o).arity

end LambdaLab.Parser.Playground
