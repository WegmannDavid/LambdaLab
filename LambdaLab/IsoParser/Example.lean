import LambdaLab.IsoParser.Notation

/-!
# `IsoParser` demo — the split-model idioms

The three shapes a grammar is built from, each with its round-trip law arriving for free:

* a **product** node (`gdo` + `comap`): each field's sub-parser prints from its own slice of the
  shared source; keywords (`tok`) have a polymorphic source and need no adaptation;
* a **repetition** node (`many1`): source `NEList`, FOLLOW computes to "no further element";
* a **choice** node (`orElse`): source and value are sums, FIRST-disjointness is the one
  obligation.

(The previous whitespace example — spacing as an *annotation* — is not expressible in the split
model, which has no annotation family: only canonical-form languages are genuine isos here.)
-/

namespace LambdaLab.IsoParser.Example

open LambdaLab.IsoParser

abbrev Digit := { c : Char // c.isDigit = true }

def pDigit := sat Char.isDigit

/-! ## Product: `LHS = RHS` -/

structure Binding where
  lhs : Digit
  rhs : Digit
  deriving Repr

def binding : IsoParser Char (fun c => c.isDigit = true) (fun _ => True) Binding Binding := gdo
  let l ← comap Binding.lhs pDigit
  let _eq ← tok '='
  let r ← comap Binding.rhs pDigit
  return Binding.mk l r

#eval binding.run "1=2".toList                                  -- some (⟨'1', '2'⟩, [])
#eval (binding.print ⟨⟨'3', by decide⟩, ⟨'4', by decide⟩⟩).2    -- ['3', '=', '4']
#eval binding.run "1+2".toList                                  -- none

/-- The round-trip — free. -/
example (b : Binding) : binding.run (binding.print b).2 = some ((binding.print b).1, []) :=
  binding.roundtrip b

/-! ## Repetition: a digit run -/

def number := many1 pDigit (fun _ _ => trivial)

#eval number.run "123+4".toList   -- some ((⟨'1'⟩, ['2', '3']), ['+', '4'])  — stops at '+'
#eval (number.print (⟨'1', by decide⟩, [⟨'2', by decide⟩])).2   -- ['1', '2']

example (l : NEList Digit) : number.run (number.print l).2 = some ((number.print l).1, []) :=
  number.roundtrip l

/-! ## Choice: a bare digit or an `'='`-prefixed digit (disjoint FIRSTs) -/

def eqDigit : IsoParser Char (· = '=') (fun _ => True) Digit Digit := gdo
  let _eq ← tok '='
  let d ← comap id pDigit
  return d

def digitOrEq := orElse pDigit eqDigit
  (by intro c h hc; subst h; simp at hc)

#eval digitOrEq.run "7".toList    -- some (Sum.inl '7', [])
#eval digitOrEq.run "=7".toList   -- some (Sum.inr '7', [])
#eval digitOrEq.run "x".toList    -- none

example (v : Digit ⊕ Digit) :
    digitOrEq.run (digitOrEq.print v).2 = some ((digitOrEq.print v).1, []) :=
  digitOrEq.roundtrip v

end LambdaLab.IsoParser.Example
