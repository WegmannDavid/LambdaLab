import LambdaLab.Parser.Playground.Soundness

/-!
# Completeness / round-trip of the precedence parser

The converse of soundness: every top-level expression's flattening parses back
to it, `parse e.flatten = some e` (`parseAll_complete`). With soundness this
gives the full characterization `parse_iff` and unambiguity `flatten_injective`.

## Why this direction is hard (the greedy-tail-loop gap)

The infix/postfix parsers are **greedy** (maximal munch): `parseInfixLTail` /
`parsePostfixTail` fold in as many further occurrences of the operator as the
input allows. So the naive per-subtree round-trip

  `parseTree a (t.flatten ++ rest) = some (t, rest)`

is **false** for arbitrary `rest`: if `t` is a tighter expression (a `next …`)
and `rest` begins with `a`'s operator token, the loop greedily folds `rest` into
a *larger* tree instead of stopping. (E.g. at the `+` level, `n` followed by
`+ m` parses as `n + m`, not as `n` with leftover `+ m`.)

So the helper round-trips need a side condition — roughly "`rest` does not
continue a tail at level `a`" — and the genuinely hard lemma is the **tail-loop
inverse**: that re-parsing the flattening of a left-nested spine reconstructs
exactly that spine (and the postfix analogue). This is the same obstruction that
left Mixfix2's completeness unproved.

**Second obstruction — multi-root incompleteness.** `parseExprRoots` (and
`parseBelowList`) return the *first* root/node that yields `some`, with no
full-consumption check. With a single loosest root (both example grammars) this
is fine. With *several* loosest roots it breaks: e.g. `loosest = [add, sub]`
parsing `n - n` tries `add` first, gets a *partial* parse (`n`, leftover `- n`),
commits to it, and top-level `parse` then rejects the non-empty leftover —
though `n - n` is a valid `sub` tree. So `parseAll_complete` as stated is
**false** for multi-root grammars; it needs a single-root / unambiguity side
condition (or a longest-match/backtracking parser). For single-root grammars it
reduces to the first (tail-loop) obstruction.

This file currently: assembles the bijection from `parseAll_complete`, proving
the reductions; `parseAll_complete` itself is the isolated hard lemma (sorried),
blocked on the two obstructions above.
-/

namespace LambdaLab.Parser.Playground

open LambdaLab.Parser

variable {G : Grammar}

/-- **The hard direction (open).** Every top-level expression's flattening parses
fully back to it. Reduces to a greedy round-trip whose crux is the tail-loop
inverse (see the module docstring). -/
theorem parseAll_complete (e : Expr G) : parse e.flatten = some e := by
  sorry

/-- Unambiguity: `flatten` is injective on top-level expressions. Follows from
soundness + completeness. -/
theorem flatten_injective {e₁ e₂ : Expr G} (h : e₁.flatten = e₂.flatten) : e₁ = e₂ := by
  have h₁ := parseAll_complete e₁
  have h₂ := parseAll_complete e₂
  rw [h, h₂] at h₁
  exact (Option.some.inj h₁).symm

/-- Full characterization: `parse` accepts exactly the flattenings, returning the
unique expression that flattens to the input. -/
theorem parse_iff {tkns : List Token} {e : Expr G} :
    parse (G := G) tkns = some e ↔ e.flatten = tkns := by
  constructor
  · exact parse_sound
  · intro h; subst h; exact parseAll_complete e

end LambdaLab.Parser.Playground
