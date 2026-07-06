/-!
# Proper right sublists

A `RightSublist l` is a strict suffix of `l`: the leftover after dropping a
non-empty prefix. Parsers return one to prove they made progress — the
non-empty prefix forces `list.length < l.length` (`RightSublist.length_lt`),
which is the well-founded measure a leftover-threading parser recurs on.
-/

namespace LambdaLab.ParserExperimental

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

/-- A **truncating biparser**: a `parse` paired with a single concrete `render`, where
the result `β` is a **lossy** image of the surface syntax (parens dropped, annotations
quotiented), so only *one* coherence law survives.

The rendering **policy is packaged in** rather than exposed as a type parameter, so
`render : β → List α` is a single concrete printer (a policy was chosen when the
biparser was built) and the structure stays universe-flat — this is what lets it sit
as a field in a `Language` without bumping its universe. `parse` recovers `β`.
`parse_complete` (renderer soundness) holds unconditionally — every rendering parses
back to its value, leaving exactly `rest`. But `render_complete` (parser soundness) is
**dropped**: the parser accepts strings — e.g. redundantly parenthesized ones — that
`render` never emits (it produces only the minimally-parenthesized canonical form), so
the consumed tokens `s.pre` aren't reproduced in general. This is the print→parse
direction only, and it is exactly what a `Grammar` + `ReverseInterp` + a chosen policy
supplies (see `Parser.Mixfix.ReverseInterp.toTruncatingBiparser`). The lossless,
policy-indexed `Biparser` (both laws) lives in `Parser.Biparser`. -/
structure TruncatingBiparser (α : Type u) (β : Type w) where
  /-- Render a value to its **minimally-parenthesized** concrete form (fixed policy). -/
  render : β → List α
  /-- All parses of a prefix of the input, each truncated to a value. -/
  parse : Parser α β
  /-- **Renderer soundness**: every rendering parses back. For any value `b` and
  continuation `rest`, parsing `render b ++ rest` finds `b`, leaving exactly `rest`.
  (No `render_complete`: `render` reaches only the canonical form.) -/
  parse_complete :
    ∀ (b : β) (rest : List α),
      ∃ s : RightSublist (render b ++ rest),
        s.list = rest ∧ (b, s) ∈ parse (render b ++ rest)

/-- **Print-then-parse recovers the value** for a truncating biparser: rendering `b`
and parsing back yields `b` as a full parse (empty leftover). -/
theorem TruncatingBiparser.roundTrip {α : Type u} {β : Type w}
    (tp : TruncatingBiparser α β) (b : β) :
    ∃ s : RightSublist (tp.render b), s.list = [] ∧ (b, s) ∈ tp.parse (tp.render b) := by
  have heq : tp.render b ++ [] = tp.render b := List.append_nil _
  exact heq ▸ tp.parse_complete b []

end LambdaLab.ParserExperimental
