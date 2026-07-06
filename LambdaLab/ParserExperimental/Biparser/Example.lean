import LambdaLab.ParserExperimental.Biparser.Combinators

/-!
# Example: a space-separated sequence of unary naturals

Parses a **nonempty** sequence of unary numbers (`a` = 0, `aa` = 1, `aaa` = 2, …)
separated by single spaces, e.g. `"a aaa aa"` ↦ `(0, [2, 1])`. Built entirely from the
verified combinators, so it carries **both** coherence laws by construction.

Single-space separators keep every policy `Unit`, so the whole thing has the trivial
policy `NatsPolicy := Unit` — there is no formatting freedom to choose (the weaker
`ParserExperimental1` variant is what unlocks richer, variable-spacing policies).
-/

namespace LambdaLab.ParserExperimental

/-- A parsed number sequence: nonempty, as head + tail. -/
abbrev Nats := Nat × List Nat

/-- No formatting choice: single-space, canonical unary form. -/
abbrev NatsPolicy : Type := Unit

/-! ### Value subtypes for the two literal characters are subsingletons -/

instance : Subsingleton { c : Char // (c == 'a') = true } :=
  ⟨fun a b => Subtype.ext (by rw [eq_of_beq a.2, eq_of_beq b.2])⟩
instance : Subsingleton { c : Char // (c == ' ') = true } :=
  ⟨fun a b => Subtype.ext (by rw [eq_of_beq a.2, eq_of_beq b.2])⟩

/-- In a subsingleton element type, a list is its own length-many replicate. -/
theorem replicate_length_eq {β : Type} [Subsingleton β] (x : β) :
    ∀ l : List β, List.replicate l.length x = l
  | [] => rfl
  | a :: l => by rw [List.length_cons, List.replicate_succ, replicate_length_eq x l,
                    Subsingleton.elim x a]

/-! ### The combinator pipeline -/

def aTok : Biparser Char Unit { c : Char // (c == 'a') = true } := tok (· == 'a')
def spTok : Biparser Char Unit { c : Char // (c == ' ') = true } := tok (· == ' ')

/-- One unary number: a nonempty run of `a`, valued by its **tail** length. -/
def number : Biparser Char Unit Nat :=
  map («some» aTok)
    (fun v => v.2.length)
    (fun n => (⟨'a', by decide⟩, List.replicate n ⟨'a', by decide⟩))
    (fun v => by
      refine Prod.ext (Subsingleton.elim _ _) ?_
      exact replicate_length_eq _ v.2)
    (fun n => by simp)

/-- A separator + number: one space then a number, valued by the number. -/
def sepNumber : Biparser Char (Unit × Unit) Nat :=
  map (seq spTok number)
    (fun v => v.2)
    (fun n => (⟨' ', by decide⟩, n))
    (fun v => Prod.ext (Subsingleton.elim _ _) rfl)
    (fun _ => rfl)

/-- Raw ≥1-number sequence: either a number followed by ≥1 more `sep number`s, or a
single number. -/
def numbersRaw :
    Biparser Char ((Unit × (Unit × Unit)) × Unit) ((Nat × (Nat × List Nat)) ⊕ Nat) :=
  alt (seq number («some» sepNumber)) number

/-- Reshape the `⊕` into a single nonempty list `Nat × List Nat`. -/
def numbers : Biparser Char ((Unit × (Unit × Unit)) × Unit) Nats :=
  map numbersRaw
    (fun v => match v with
      | .inl (n, (m, ms)) => (n, m :: ms)
      | .inr n            => (n, []))
    (fun v => match v with
      | (n, [])      => .inr n
      | (n, m :: ms) => .inl (n, (m, ms)))
    (fun v => by rcases v with (⟨n, m, ms⟩) | n <;> rfl)
    (fun v => by obtain ⟨n, l⟩ := v; cases l <;> rfl)

/-- The parser, with the nested-`Unit` policy reshaped to a single `Unit`. -/
def parseNats : Biparser Char NatsPolicy Nats :=
  mapPolicy (fun _ : Unit => (((), ((), ())), ()))
    (fun _ => ⟨(), Subsingleton.elim _ _⟩)
    numbers

#eval (parseNats.parse "a aaa aa".toList).map (fun r => (r.1, r.2.list))  -- [((0,[2,1]), [])] (+ prefixes)
#eval parseNats.render (0, [2, 1]) ()                                     -- "a aaa aa" as chars
#eval String.ofList (parseNats.render (3, []) ())                        -- "aaaa"

end LambdaLab.ParserExperimental
