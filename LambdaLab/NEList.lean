/-!
# Non-empty lists

`NEList α` is a head plus a (possibly empty) tail — a list that is non-empty *by
construction*, so the emptiness case is unrepresentable rather than merely excluded.

It shows up wherever a one-or-more parser meets its source: `many1` never *parses* an empty
list, so a `List α` source would be wider than the printable set and would falsify any
round-trip law. `NEList` is exactly the source shape those combinators consume.

It is an `abbrev` (hence reducible), so `NEList α` and `α × List α` are interchangeable and
existing pattern matches `fun (x, xs) => …` keep working unchanged.
-/

/-- A non-empty list: a head, and the rest. -/
abbrev NEList (α : Type) := α × List α

namespace NEList

variable {α β : Type}

/-- The head — always present, which is the whole point. -/
abbrev head (l : NEList α) : α := l.1

/-- Everything after the head. -/
abbrev tail (l : NEList α) : List α := l.2

/-- Forget the non-emptiness. -/
def toList (l : NEList α) : List α := l.1 :: l.2

/-- A one-element non-empty list. -/
def singleton (a : α) : NEList α := (a, [])

@[simp] theorem toList_ne_nil (l : NEList α) : l.toList ≠ [] := by
  simp [toList]

@[simp] theorem toList_singleton (a : α) : (singleton a).toList = [a] := rfl

def map (f : α → β) (l : NEList α) : NEList β := (f l.1, l.2.map f)

@[simp] theorem toList_map (f : α → β) (l : NEList α) :
    (l.map f).toList = l.toList.map f := rfl

end NEList
