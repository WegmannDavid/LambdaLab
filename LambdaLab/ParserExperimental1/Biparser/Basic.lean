import LambdaLab.ParserExperimental1.Basic

/-!
# Biparsers (weaker target: renderer soundness only)

A `Biparser` runs both directions at once — a `parse` together with a policy-driven
`render`. This variant keeps **only** `parse_complete` (renderer soundness): every
policy that exists round-trips (`render e p` parses back to `e`). It **drops**
`render_complete`: the parser may accept strings — e.g. formats with whitespace or
parens the policy set can't emit — for which *no* policy produces that exact rendering.

The payoff of the weaker target: `render_complete` was the sole reason for every
combinator side-condition (`[Subsingleton]` on `some`, `[Inhabited]` on `alt`,
surjectivity on `mapPolicy`, the left-inverse on `map`); dropping it removes them all.
-/

namespace LambdaLab.ParserExperimental1

/-- A **policy-driven renderer**: turn a result `b` into tokens, with a `Policy`
choosing *which* of its many valid concrete renderings to emit — whitespace,
parenthesization, and any other surface styling. -/
abbrev Renderer (β : Type u) (Policy : Type v) (α : Type w) := β → Policy → List α

/-- A **biparser** with the weaker (renderer-soundness-only) contract: a policy-driven
`render`, an all-parses `parse`, and the single law `parse_complete` — every policy
round-trips. `render_complete` (that every accepted string is reachable by some policy)
is deliberately **not** required, so a parser may accept concrete forms no policy emits;
the guarantee is only that whatever the policy set *does* produce parses back to the
same value. -/
structure Biparser (α : Type u) (Policy : Type v) (β : Type w) where
  /-- Render a result to tokens under a chosen `Policy` — one of its many valid
  concrete forms. -/
  render : Renderer β Policy α
  /-- All parses of a prefix of the input. -/
  parse : Parser α β
  /-- **Renderer soundness**: every rendering parses back. For any result `e`, policy
  `p`, and continuation `rest`, parsing `render e p ++ rest` finds `e`, leaving exactly
  `rest`. (No `render_complete`: the parser may accept forms no policy produces.) -/
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

end LambdaLab.ParserExperimental1
