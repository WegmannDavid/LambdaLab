/-!
# Proper right sublists — the mixfix parser's termination witness

A `RightSublist l` is a leftover strictly shorter than `l`. The mixfix parser
returns one so that its **leftover-threading recursion terminates** — `lt` is the
measure `parseAt` recurses on when it feeds a sub-parse's leftover back into itself
(e.g. an infix right operand).

Deliberately light: just the leftover `list` and `lt : list.length < l.length`.
The parser constructs the leftover directly (so no `cast` plumbing), and two
witnesses with equal `list` are *defeq* (proof irrelevance on `lt`), which keeps
the round-trip proof cheap.

Scoped to `Mixfix/`: the public `Biparser` (see `Biparser/Basic.lean`) keeps a
plain `List α` leftover so it stays a monad; only the hand-rolled mixfix spine
needs this progress witness, bridged back to `.list` at the `Biparser` boundary.
-/

namespace LambdaLab.Biparser.Mixfix

/-- A leftover of `l` that is **strictly shorter** — the parser's proof of progress. -/
structure RightSublist (l : List α) where
  list : List α
  lt   : list.length < l.length

namespace RightSublist

/-- Dropping the head yields a strictly shorter leftover. -/
def consTail (a : α) (l : List α) : RightSublist (a :: l) := ⟨l, by simp⟩

/-- Compose: a shorter-leftover of a shorter-leftover is a shorter-leftover. -/
def trans {l : List α} (s : RightSublist l) (r : RightSublist s.list) : RightSublist l :=
  ⟨r.list, Nat.lt_trans r.lt s.lt⟩

@[simp] theorem consTail_list (a : α) (l : List α) : (consTail a l).list = l := rfl

@[simp] theorem trans_list {l : List α} (s : RightSublist l) (r : RightSublist s.list) :
    (s.trans r).list = r.list := rfl

theorem length_lt {l : List α} (r : RightSublist l) : r.list.length < l.length := r.lt

end RightSublist

end LambdaLab.Biparser.Mixfix
