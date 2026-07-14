

namespace LambdaLab.CBiparser.Mixfix

/-- A predicate-restricted string. -/
abbrev Restricted (P : String → Prop) : Type := { s : String // P s }

/-- A **token** for the separator predicate `sep`: a **nonempty** string containing
**no** separator character. Nonemptiness ensures a rendered token can't vanish, so a
rendered token stream always re-splits back into the same tokens (needed for
`parse_complete`). -/
abbrev Token (sep : Char → Bool) : Type :=
  Restricted (fun s => (∀ c ∈ s.toList, sep c = false) ∧ s.toList ≠ [])

/-! ## Operator names with configurable interior holes

An operator's name is a non-empty sequence of name tokens. Between each
consecutive pair of tokens sits an **interior hole**, which is either recursive
(`loosest`, parsing the host language — the previous, default behaviour) or
parsed by **another language** (an entry `Ent`).

The inner-hole type `Ent` is kept **abstract** (a plain parameter), so embedding
a sub-language does **not** create a `Grammar → Operator → … → Grammar` type
cycle: `Grammar` stays a plain `structure`, and any parser built from it keeps
`G` as a parameter (the sub-tree stored at such a hole is the sub-language's own
result, never a `Grammar`'s `Expr`). A binder is an interior hole admitting
exactly one variable. -/

/-- An operator name: a non-empty token sequence with an inner hole (an entry
`Ent`) between each consecutive pair of tokens. A plain operator uses the
recursive/loosest hole for every interior position (the previous behaviour); a
sub-parser hole references another entry. -/
inductive Notation (sep : Char → Bool) (Ent : Type) where
  | last : Token sep → Notation sep Ent
  | cons : Token sep → Ent → Notation sep Ent → Notation sep Ent

/-- The name tokens of a `Notation`, in order. -/
def Notation.toTokens {sep : Char → Bool} {Ent : Type} : Notation sep Ent → List (Token sep)
  | .last t        => [t]
  | .cons t _ rest => t :: rest.toTokens

inductive Operator (sep : Char → Bool) (Ent : Type) where
| closed : Notation sep Ent → Operator sep Ent
| prefx : Notation sep Ent → Operator sep Ent
/-- Non-associative infix: both operands strictly tighter, so it does not nest
unparenthesized. -/
| infx : Notation sep Ent → Operator sep Ent
/-- Left-associative infix (`a ∘ b ∘ c = (a ∘ b) ∘ c`): the left operand is at
`.tighterEq` (chains), the right is strictly tighter. Its body is left-recursive
(leading `.tighterEq` hole), so it is parsed by an iterative fold (like `juxt`),
not `parseParts`. -/
| infxl : Notation sep Ent → Operator sep Ent
/-- Right-associative infix (`a ∘ b ∘ c = a ∘ (b ∘ c)`): the right operand is at
`.tighterEq` (chains), the left is strictly tighter. The trailing recursion
consumes the operator token first, so the ordinary `parseParts` handles it. -/
| infxr : Notation sep Ent → Operator sep Ent
| postfx : Notation sep Ent → Operator sep Ent
/-- Juxtaposition (function application by adjacency): a tokenless,
left-associative, tightest-binding operator. A grammar has at most one (see
`Grammar.juxtUnique`). -/
| juxt : Operator sep Ent

/-- The name-part tokens of an operator, in body order. -/
def Operator.nameTokens {sep : Char → Bool} {Ent : Type} : Operator sep Ent → List (Token sep)
  | .closed n => n.toTokens
  | .prefx n => n.toTokens
  | .infx n => n.toTokens
  | .infxl n => n.toTokens
  | .infxr n => n.toTokens
  | .postfx n => n.toTokens
  | .juxt => []

/-- The **leading token** of an operator: its first name-part token, if any. This is
the token the deterministic parser dispatches on to choose an operator — a prefix or
closed operator is chosen by it before its operand, an infix/postfix one by it after
the left operand. Juxtaposition (no name parts) has none. -/
def Operator.headTok? {sep : Char → Bool} {Ent : Type} (o : Operator sep Ent) :
    Option (Token sep) :=
  o.nameTokens.head?


/-- The **first** token of a notation. Every notation has one (it is non-empty by
construction), which is what makes `holeFollowers` total. -/
def Notation.firstTok {sep : Char → Bool} {Ent : Type} : Notation sep Ent → Token sep
  | .last t     => t
  | .cons t _ _ => t

/-- The **interior seams** of a notation: for each interior hole, the entry it is parsed at
paired with the token that immediately follows it.

In `( _ )` the single seam is `(e', ")")`; in `if _ then _ else _` the seams are
`(e₁, "then")` and `(e₂, "else")`. These are exactly the places where one parser must hand
back to another, and exactly where FOLLOW has to be right. -/
def Notation.holeFollowers {sep : Char → Bool} {Ent : Type} :
    Notation sep Ent → List (Ent × Token sep)
  | .last _        => []
  | .cons _ e' rest => (e', rest.firstTok) :: rest.holeFollowers

/-- The interior seams of an operator. `juxt` has none (no tokens at all); every other fixity
inherits its notation's. The *outer* holes never appear here: they are at the host entry and are
bounded by the ambient FOLLOW, not by a token of this operator. -/
def Operator.holeFollowers {sep : Char → Bool} {Ent : Type} :
    Operator sep Ent → List (Ent × Token sep)
  | .closed n => n.holeFollowers
  | .prefx n  => n.holeFollowers
  | .infx n   => n.holeFollowers
  | .infxl n  => n.holeFollowers
  | .infxr n  => n.holeFollowers
  | .postfx n => n.holeFollowers
  | .juxt     => []

/-- Does this operator begin with a **hole** (i.e. take a left operand)?

This is the distinction FOLLOW turns on, and it is exactly the one `headTok?` alludes to. A
`closed`/`prefx` operator's leading token **starts** an operand (`f (x)` — the `(` continues a
juxtaposition), while an infix/postfix operator's leading token **continues** an expression
(`a + b` — the `+` arrives *after* the left operand). Same token, opposite roles.

Everything else — a name token that is *not* leading, such as the `)` of `( _ )` or the `then`
of `if _ then _ else _` — can only appear **after a hole inside** an operator. Such a token can
therefore legally *follow* an expression, and belongs in FOLLOW. -/
def Operator.startsWithHole {sep : Char → Bool} {Ent : Type} : Operator sep Ent → Bool
  | .closed _ => false
  | .prefx _  => false
  | .infx _   => true
  | .infxl _  => true
  | .infxr _  => true
  | .postfx _ => true
  | .juxt     => true

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
  for the parser *and* for the precedence-indexed `Tree`, so no separate
  finiteness witness is needed.

There is deliberately **no coverage/reachability field**. A `Tree` is indexed
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
*derived* from the user-facing `UniqueNameParts` certificate, not assumed here.

`isVar` recognizes *variable* (identifier) tokens — atoms that are not operator
name parts. The parser admits any `isVar` token as a leaf `Expr.var` at every
level. For unique parses, a separate certificate requires `isVar` tokens to be
disjoint from operator name parts (so a token can't be read as both a variable
and an operator), exactly as `UniqueNameParts` handles name-part collisions. -/
structure Entry (sep : Char → Bool) (Ent : Type) where
  Op : Type
  /-- The declaration of each operator (its fixity and name/notation). -/
  operator : Op → Operator sep Ent
  /-- **Every** operator of this entry, enumerated.

  Needed to *compute* FIRST/FOLLOW — any parser generator must be able to range over the
  operators. `ops_complete` is what makes the computation **sound**: an incomplete `ops` would
  under-approximate the set of tokens that can continue an expression, hence over-approximate
  FOLLOW, hence claim the parser stops at tokens where it actually keeps going — and the
  round-trip law would be false. A concrete grammar discharges it by `decide`. -/
  ops : List Op
  ops_complete : ∀ o : Op, o ∈ ops
  loosest : List Op
  tighter : Op → List Op
  tighter_wf : WellFounded (fun b a => b ∈ tighter a)
  /-- Recognizes variable (identifier) tokens — leaf atoms, distinct from operator
  name parts. -/
  isVar : Token sep → Bool
  /-- At most one operator is juxtaposition. Being tokenless, two juxtaposition
  operators would be indistinguishable in the token stream; this pins it to one
  (vacuously satisfied by grammars without juxtaposition). -/
  juxtUnique : ∀ o₁ o₂ : Op, operator o₁ = Operator.juxt → operator o₂ = Operator.juxt → o₁ = o₂
  /-- **Distinct leading tokens** — a *lexical* well-formedness requirement: operators
  must be tellable apart, so two operators sharing a leading token are the same operator.
  This makes the parser's dispatch deterministic. Juxtaposition (no leading token) is
  excluded by the `isSome` guard and pinned instead by `juxtUnique`.

  This is *not* the same as forcing the grammar to be unambiguous: a grammar with distinct
  heads can still be precedence-**incomplete** (incomparable operators), and such an input
  — e.g. `a + b * c` with `+`/`*` incomparable — simply doesn't parse (returns `none`,
  "add parentheses"). Only the lexical distinctness is required, not a complete DAG. -/
  headsDistinct : ∀ o₁ o₂ : Op, (operator o₁).headTok?.isSome →
    (operator o₁).headTok? = (operator o₂).headTok? → o₁ = o₂
  /-- **Variables are not operator tokens** — the variable side of the same lexical
  distinctness: no operator name part is an `isVar` token, so a token can't be read as
  both a variable leaf and (part of) an operator. Stated over the operator's *finite*
  name-part list, so a concrete grammar discharges it by `decide`. -/
  varDisjoint : ∀ (o : Op) (t : Token sep), t ∈ (operator o).nameTokens → isVar t = false

structure Grammar where
  Ent : Type
  /-- Which characters are **separators** (whitespace). A lexical, whole-grammar
  notion — every entry shares it. It defines: how the char stream tokenizes (split
  on maximal separator runs), what a valid inter-token separator is (a nonempty run
  of these), and hence the token alphabet (`Token isSep` — strings containing none
  of these). -/
  isSep : Char → Bool
  /-- A distinguished separator character, witnessing that the separator alphabet is
  **nonempty**. Any grammar that tokenizes owns a separator, so this costs nothing —
  and it makes `Sep G` canonically inhabited, so the render witness needs no external
  default (`dflt`) threaded through it. -/
  sepWitness : { c : Char // isSep c = true }
  entry : Ent → Entry isSep Ent
  -- no start symbol, the start symbol is choosen when deriving the parser
  /-- **Interior seams terminate** — the third and last piece of lexical distinctness, and the
  analogue of `headsDistinct` for the tokens that are *not* leading.

  Read it off an operator's shape. In `( _ )` the hole is parsed by entry `e'`'s parser, and the
  only thing that can stop that parser is the token that follows the hole — here `)`. So `)` must
  lie in **`e'`'s** FOLLOW: it may be neither an `e'`-variable nor the head of any `e'`-operator.

  This lives on `Grammar`, not on `Entry`, and it *has* to: the hole's entry `e'` is in general a
  **different** entry from the operator's host `e` (that is the whole point of `Notation.cons`
  carrying an `Ent`), and an `Entry` cannot see its siblings. A two-entry grammar — exactly what
  `Language1` is, with `Ty` and `Tm` — can satisfy every `Entry` field and still break the law.

  Without this the round-trip law is **FALSE**, not merely unproved: a grammar in which `)` heads
  an operator of the hole's entry gives `follow e' ")" = false`, the greedy `e'`-parser runs past
  the `)`, and the printed tree does not parse back. `varDisjoint` rules out the *variable* half of
  the hazard within one entry; this rules out both halves across all of them. Together with
  `headsDistinct` it says: **every token has exactly one lexical role at every seam it can reach.**

  Stated over the operator's finite seam list, so a concrete grammar discharges it by `decide`. -/
  interiorTerminates : ∀ (e : Ent) (o : (entry e).Op) (e' : Ent) (t : Token isSep),
    (e', t) ∈ ((entry e).operator o).holeFollowers →
      (entry e').isVar t = false ∧
        ∀ o' : (entry e').Op, ((entry e').operator o').headTok? ≠ some t

/-! **Note.** The char-level separator machinery (`Sep`, `NESep`, `mkNESep`, …) that used to
live here is gone: the mixfix biparser is **token-level**, so its alphabet is `Token isSep` and
nothing inside it ever sees a separator character. `isSep` survives only to *define* which
strings are valid tokens. Separators come back when a tokenizer is precomposed in front — and
that machinery is preserved in `LambdaLab/Biparser/Mixfix/Basic.lean` if it is wanted then. -/

end LambdaLab.CBiparser.Mixfix
