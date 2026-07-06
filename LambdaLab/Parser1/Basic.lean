/-!
# Proper right sublists

A `RightSublist l` is a strict suffix of `l`: the leftover after dropping a
non-empty prefix. Parsers return one to prove they made progress — the
non-empty prefix forces `list.length < l.length` (`RightSublist.length_lt`),
which is the well-founded measure a leftover-threading parser recurs on.
-/

namespace LambdaLab.Parser1

/-- A **proper right sublist** (strict suffix) of `l`: a list `list` together
with the non-empty prefix `pre` that was dropped, witnessed by `pre ++ list = l`.

The non-empty prefix is the whole point — it forces `list.length < l.length`
(`length_lt`), so returning one of these from a parser proves it made progress. -/
structure RightSublist (l : List α) where
  list : List α
  pre : List α
  pre_ne : pre ≠ []
  eq : pre ++ list = l

namespace RightSublist

/-- Dropping a single head element yields a proper right sublist. -/
def cons (a : α) (l : List α) : RightSublist (a :: l) where
  list := l
  pre := [a]
  pre_ne := by simp
  eq := rfl

/-- A proper right sublist of a proper right sublist is one of the original
list: suffixes compose, and the dropped prefixes concatenate. -/
def trans {l : List α} (s : RightSublist l) (r : RightSublist s.list) : RightSublist l where
  list := r.list
  pre := s.pre ++ r.pre
  pre_ne := by
    cases h : s.pre with
    | nil => exact absurd h s.pre_ne
    | cons _ _ => simp
  eq := by rw [List.append_assoc, r.eq, s.eq]

/-- The defining property: a proper right sublist is strictly shorter. -/
theorem length_lt {l : List α} (r : RightSublist l) : r.list.length < l.length := by
  have hlen : r.pre.length + r.list.length = l.length := by
    rw [← List.length_append, r.eq]
  have hpre : 0 < r.pre.length := by
    cases h : r.pre with
    | nil => exact absurd h r.pre_ne
    | cons _ _ => simp
  omega

end RightSublist

/-- An **all-parses** parser: every parse of a prefix of the input, each with the
strict suffix left over (an empty list means "no parse"). -/
abbrev Parser (α : Type u) (β : Type w) := (input : List α) → List (β × RightSublist input)

/-- A **policy-driven renderer**: turn a result `b` into tokens, with a `Policy`
choosing *which* of its many valid concrete renderings to emit — whitespace,
parenthesization, and any other surface styling. -/
abbrev Renderer (β : Type u) (Policy : Type v) (α : Type w) := β → Policy → List α

/-- A **biparser**: one object that runs both directions — a `parse` together with a
policy-driven `render`, certified to describe the *same* relation between results
and token strings. A
result has no single canonical serialization — it renders to a whole family of
strings indexed by `Policy` (whitespace, parenthesization, …) — so both laws are
stated against `render`, not a fixed `flatten`.

* `render_complete` (parser **soundness** = renderer **completeness**) — every parse
  consumed a genuine rendering: the tokens a parse ate, `s.pre`, are `render e p`
  for some policy `p`. The parser invents no structure the input didn't have, and
  `render` reaches every string the parser accepts.
* `parse_complete` (parser **completeness** = renderer **soundness**) — every
  rendering parses back: for any policy `p`, `render e p` (then any `rest`) parses
  to `e`, leaving exactly `rest`. The parser accepts every string `render` emits and
  misses no valid input.

Together they say `parse` and `render` are two views of one relation:
`{(e, s.pre) | (e, s) ∈ parse _} = {(e, render e p) | p : Policy}`. Universe-
polymorphic so a grammar's own parse trees (`Expr.{u}`, in `Type (u+1)`) can be
embedded as a `Biparser.{u+1}`. -/
structure Biparser (α : Type u) (Policy : Type v) (β : Type w) where
  /-- Render a result to tokens under a chosen `Policy` — one of its many valid
  concrete forms. -/
  render : Renderer β Policy α
  /-- All parses of a prefix of the input. -/
  parse : Parser α β
  /-- **Parser soundness / renderer completeness**: every parse consumed a genuine
  rendering. If `(e, s)` is a parse of `input`, then some policy renders `e` back to
  exactly the consumed tokens `s.pre` — so the parser invents nothing, and `render`
  surjects onto every concrete syntax the parser accepts for `e`. -/
  render_complete :
    ∀ (input : List α) (e : β) (s : RightSublist input),
      (e, s) ∈ parse input →
      ∃ p : Policy, render e p = s.pre
  /-- **Parser completeness / renderer soundness**: every rendering parses back. For
  any result `e`, policy `p`, and continuation `rest`, parsing `render e p ++ rest`
  finds `e`, leaving exactly `rest` — so the parser accepts every string `render`
  emits and misses no valid input. -/
  parse_complete :
    ∀ (e : β) (p : Policy) (rest : List α),
      ∃ s : RightSublist (render e p ++ rest),
        s.list = rest ∧ (e, s) ∈ parse (render e p ++ rest)

/-- **Print-then-parse recovers the value**: rendering `e` under any policy `p` and
parsing the result back yields `e` as a *full* parse (empty leftover). The headline
round-trip, a corollary of `parse_complete` at `rest = []`. -/
theorem Biparser.roundTrip {α : Type u} {Policy : Type v} {β : Type w}
    (bp : Biparser α Policy β) (e : β) (p : Policy) :
    ∃ s : RightSublist (bp.render e p), s.list = [] ∧ (e, s) ∈ bp.parse (bp.render e p) := by
  have heq : bp.render e p ++ [] = bp.render e p := List.append_nil _
  exact heq ▸ bp.parse_complete e p []

/-- A **truncating biparser**: like a `Biparser`, but the result `β` is a **lossy**
image of the surface syntax (parens dropped, annotations quotiented), so only *one*
of the two laws survives.

`render` still chooses a concrete surface form via a `Policy`, and `parse` recovers
`β`. `parse_complete` (renderer soundness) holds unconditionally — every rendering
parses back to its value, leaving exactly `rest`. But `render_complete` (parser
soundness) is **dropped**: the parser accepts strings — e.g. redundantly
parenthesized ones — that `render` never emits (`render` always produces the
minimally-parenthesized canonical form), so no policy reproduces the consumed tokens
`s.pre` in general. This is the print→parse direction only, and it is exactly what a
`Grammar` + `ReverseInterp` supplies: `render = renderExpr ∘ lift`,
`parse = truncate ∘ parseChars`, with the law from `truncate_lift` + the lossless
`Biparser.parse_complete`. -/
structure TruncatingBiparser (α : Type u) (Policy : Type v) (β : Type w) where
  /-- Render a value to its **minimally-parenthesized** concrete form under a policy. -/
  render : Renderer β Policy α
  /-- All parses of a prefix of the input, each truncated to a value. -/
  parse : Parser α β
  /-- **Renderer soundness**: every rendering parses back. For any value `b`, policy
  `p`, and continuation `rest`, parsing `render b p ++ rest` finds `b`, leaving
  exactly `rest`. (No `render_complete`: `render` reaches only the canonical form.) -/
  parse_complete :
    ∀ (b : β) (p : Policy) (rest : List α),
      ∃ s : RightSublist (render b p ++ rest),
        s.list = rest ∧ (b, s) ∈ parse (render b p ++ rest)

/-- **Print-then-parse recovers the value** for a truncating biparser: rendering `b`
and parsing back yields `b` as a full parse (empty leftover). -/
theorem TruncatingBiparser.roundTrip {α : Type u} {Policy : Type v} {β : Type w}
    (tp : TruncatingBiparser α Policy β) (b : β) (p : Policy) :
    ∃ s : RightSublist (tp.render b p), s.list = [] ∧ (b, s) ∈ tp.parse (tp.render b p) := by
  have heq : tp.render b p ++ [] = tp.render b p := List.append_nil _
  exact heq ▸ tp.parse_complete b p []

end LambdaLab.Parser1
