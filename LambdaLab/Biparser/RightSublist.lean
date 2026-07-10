/-!
# Proper right sublists

A `RightSublist l` is a strict suffix of `l`: the leftover after dropping a
non-empty prefix. A parser returns one to *prove it made progress* — the
non-empty prefix forces `list.length < l.length` (`length_lt`), the well-founded
measure a leftover-threading parser recurs on. It also pins the leftover to a
genuine tail of *this* input (`eq`), so it can be neither fabricated nor grown.
-/

namespace LambdaLab.Biparser

/-- A **proper right sublist** (strict suffix) of `l`: a list `list` together
with the non-empty prefix `pre` that was dropped, witnessed by `pre ++ list = l`. -/
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

/-- A proper right sublist of a proper right sublist is one of the original list. -/
def trans {l : List α} (s : RightSublist l) (r : RightSublist s.list) : RightSublist l where
  list := r.list
  pre := s.pre ++ r.pre
  pre_ne := by
    cases h : s.pre with
    | nil => exact absurd h s.pre_ne
    | cons _ _ => simp
  eq := by rw [List.append_assoc, r.eq, s.eq]

/-- Transport a right sublist along an equality of the underlying list. -/
def cast {l l' : List α} (h : l = l') (r : RightSublist l) : RightSublist l' := h ▸ r

@[simp] theorem cons_list (a : α) (l : List α) : (cons a l).list = l := rfl

@[simp] theorem trans_list {l : List α} (s : RightSublist l) (r : RightSublist s.list) :
    (s.trans r).list = r.list := rfl

@[simp] theorem cast_list {l l' : List α} (h : l = l') (r : RightSublist l) :
    (r.cast h).list = r.list := by subst h; rfl

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

end LambdaLab.Biparser
