/-!
# Proper right sublists

A `RightSublist l` is a strict suffix of `l`: the leftover after dropping a
non-empty prefix. Parsers return one to prove they made progress — the
non-empty prefix forces `list.length < l.length` (`RightSublist.length_lt`),
which is the well-founded measure a leftover-threading parser recurs on.
-/

namespace LambdaLab.Parser


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

abbrev Parser (α : Type) := (tkn : List Token) → Option (List (α × RightSublist tkn))


end LambdaLab.Parser
