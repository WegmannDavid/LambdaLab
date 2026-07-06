import LambdaLab.Parser.Basic

/-!
# Biparsers

A `Biparser` runs both directions at once — a `parse` together with a policy-driven
`render`, certified to describe the *same* result↔string relation (both coherence
laws). It is built on the `RightSublist`/`Parser` primitives in `Parser.Basic`; its
lossy, policy-baked variant `TruncatingBiparser` lives there too (Language depends on
that one, so it stays in `Basic`).
-/

namespace LambdaLab.Parser

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

end LambdaLab.Parser
