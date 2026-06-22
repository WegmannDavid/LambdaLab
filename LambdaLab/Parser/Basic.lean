/-!
# Proper right sublists

A `RightSublist l` is a strict suffix of `l`: the leftover after dropping a
non-empty prefix. Parsers return one to prove they made progress — the
non-empty prefix forces `list.length < l.length` (`RightSublist.length_lt`),
which is the well-founded measure a leftover-threading parser recurs on.
-/

namespace LambdaLab.Parser

/-- The default token alphabet (a thin string). `Parser`/`LosslessParser` are now
alphabet-general; `Token` is just the one the mixfix grammar and tokenizer use. -/
abbrev Token := String

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

/-- A **verified parser**: an all-parses `parse` bundled with its correctness, so
it can be embedded as a hole in another language (`Mixfix.InnerHole.sub`) without
that language having to know how it works — only that it is sound and complete.
Universe-polymorphic so a grammar's own parse trees (`Expr.{u}`, in `Type (u+1)`)
can themselves be embedded as a `LosslessParser.{u+1}` (`Grammar.toLosslessParser`).

* `sound` — every parse consumes exactly the tokens its result flattens to.
* `complete` — every result is found on its own flattening (for any right
  extension `rest`, leaving exactly `rest`).

These are the `mem_parse_iff` interface; any `Mixfix` grammar supplies them via a
`toLosslessParser` adapter, and a hand-written parser can too. -/
structure LosslessParser (α : Type u) (β : Type w) where
  /-- The token string a result flattens to. -/
  flatten : β → List α
  /-- All parses of a prefix of the input. -/
  parse : Parser α β
  sound : ∀ (input : List α) (x : β × RightSublist input),
            x ∈ parse input → flatten x.1 ++ x.2.list = input
  complete : ∀ (r : β) (input rest : List α), input = flatten r ++ rest →
               ∃ s : RightSublist input, s.list = rest ∧ (r, s) ∈ parse input

/-- A **truncating parser**: a (possibly lossy) parser paired with a canonical
`render` — a pretty-printer that re-serializes a result to tokens, *inserting
parentheses* so the output re-parses unambiguously to the same value.

Unlike `LosslessParser`, the result `β` may *forget* surface detail (parentheses,
sugar, annotations), so `render` is **not** a left inverse of `parse`: `parse`
accepts many token strings, `render` emits one canonical string. What it
guarantees is the **print→parse round-trip** — rendering a parse result and
parsing it back yields that same value. (A strict `render r ++ leftover = input`
soundness is *not* available: `( x )` and `x` both parse to the same value, but
`render` gives only one of them.)

The round-trip is restricted to *parse results*: `β` may be richer than the
surface (extra annotations, unrestricted identifiers), so `render` can only be a
right inverse on the terms the parser actually produces — the hypothesis
`(b, s) ∈ parse input` says exactly that. -/
structure TruncatingParser (α : Type u) (β : Type w) where
  /-- All parses of a prefix of the input. -/
  parse : Parser α β
  /-- Canonical token rendering of a result — adds parentheses so it re-parses. -/
  render : β → List α
  /-- Every term the parser *produces* re-parses from its own rendering: if `b`
  is a parse of some input, then `render b` parses back to `b` (leaving any
  appended `rest`). -/
  complete : ∀ (input : List α) (b : β) (s : RightSublist input), (b, s) ∈ parse input →
    ∀ (rest : List α), ∃ s' : RightSublist (render b ++ rest),
      s'.list = rest ∧ (b, s') ∈ parse (render b ++ rest)

end LambdaLab.Parser
