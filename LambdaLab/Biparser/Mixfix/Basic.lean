import LambdaLab.Biparser.Basic


namespace LambdaLab.Biparser.Mixfix

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

/-! ## Unambiguity — a *property*, not a requirement

Grammars are **not** forced to be unambiguous. The deterministic parser is total for
any grammar: at each dispatch it fails (`none`) the moment it detects an ambiguity
(two viable operators), so it simply succeeds only on the inputs that are
unambiguous. `headsDistinct`/`varDisjoint` are therefore **predicates** (theorem
hypotheses), not `Entry` fields: a *future* theorem will show that a grammar
satisfying them (a proper precedence DAG with distinct leading tokens) never triggers
the ambiguity failure, so its parser succeeds on every well-formed input. -/

/-- Distinct leading tokens: operators sharing a leading token are equal. -/
def Entry.HeadsDistinct {sep : Char → Bool} {Ent : Type} (E : Entry sep Ent) : Prop :=
  ∀ o₁ o₂ : E.Op, (E.operator o₁).headTok?.isSome →
    (E.operator o₁).headTok? = (E.operator o₂).headTok? → o₁ = o₂

/-- No operator name part is an `isVar` token. -/
def Entry.VarDisjoint {sep : Char → Bool} {Ent : Type} (E : Entry sep Ent) : Prop :=
  ∀ (o : E.Op) (t : Token sep), t ∈ (E.operator o).nameTokens → E.isVar t = false

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

/-- A character `G` treats as a **separator** (whitespace). -/
def Sep (G : Grammar) : Type := { c : Char // G.isSep c = true }

/-- A **nonempty separator run** for `G`: one or more separator characters — the
valid form of an inter-token gap, and what a rendering `Policy` emits between the
parts of an operator body.

Derived entirely from `G.isSep`: if a grammar declares *no* separator character
(`isSep = fun _ => false`), then `Sep G` — and hence `NESep G` — is empty, so the
grammar can't emit the separators its own tokens require and simply can't be
rendered. That's the policy author's problem to avoid, not something enforced. -/
structure NESep (G : Grammar) where
  head : Sep G
  tail : List (Sep G)

/-- A separator run as a plain (nonempty) list of separators. -/
def NESep.toList {G : Grammar} (s : NESep G) : List (Sep G) := s.head :: s.tail

/-- The characters of a separator run, in order. -/
def NESep.toChars {G : Grammar} (s : NESep G) : List Char :=
  s.head.val :: s.tail.map (·.val)

/-- Promote a possibly-empty separator run to a `NESep`, falling back to the
grammar's canonical `sepWitness` when empty. On valid input the fallback is dead
code (internal gaps always carry a separator); it makes the render witness a total
function with no threaded default. -/
def mkNESep {G : Grammar} : List (Sep G) → NESep G
  | []        => ⟨G.sepWitness, []⟩
  | c :: rest => ⟨c, rest⟩

/-- On a nonempty run, `mkNESep` is the identity (the fallback is untouched). -/
theorem mkNESep_toList_of_ne {G : Grammar} {l : List (Sep G)} (h : l ≠ []) :
    (mkNESep l).toList = l := by
  cases l with
  | nil => exact absurd rfl h
  | cons c rest => rfl

end LambdaLab.Biparser.Mixfix
