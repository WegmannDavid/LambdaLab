
structure Biparser (α β : Type) where
  parse : List Char → Option (β × List Char)
  print : α → β × List Char

instance : Monad (Biparser α) where
  pure a := {
      parse := fun input => some (a, input),
      print := fun _ => (a, []) }
  bind p f := {
    parse := fun input => do
      let (a, rest) ← p.parse input
      (f a).parse rest,
    print := fun b =>
      let (a, rest) := p.print b
      let (c, rest') := (f a).print b
      (c, rest ++ rest')
  }

def pChar (c : Char) : Biparser α Unit := {
  parse := fun input =>
    match input with
    | [] => none
    | h :: t => if h = c then some ((), t) else none,
  print := fun _ => ((), [c])
}

def pAB : Biparser Unit Unit := do
  pChar 'A'
  pChar 'B'
  pure ()

#eval pAB.parse ['A', 'B', 'C'] -- some ((), ['C'])
#eval pAB.print () -- ((), ['A', 'B'])

abbrev Digit := {c : Char // c.isDigit}

def pDigit : Biparser Digit Digit := {
  parse := fun input =>
    match input with
    | [] => none
    | h :: t => if Heq : h.isDigit then some (⟨h, Heq⟩, t) else none,
  print := fun d => (d, [d.val])
}

def pADigitB : Biparser Digit Digit := do
  pChar 'A'
  let d ← pDigit
  pChar 'B'
  pure d

#eval pADigitB.parse ['A', '1', 'B', '2'] -- some (⟨'1', _⟩, ['2'])
#eval pADigitB.print ⟨'1', by decide⟩ -- (⟨'1', _⟩, ['A', '1'])

/-- Adapt the **source**: `comap g p` prints from `α'` by first projecting to `α`. Parse ignores
the source, so only `print` changes — this is what lets each sub-biparser of a product node print
from its own slice of the shared source. -/
def comap (g : α' → α) (p : Biparser α β) : Biparser α' β := {
  parse := p.parse,
  print := fun a' => p.print (g a')
}

def pADigitBDigit : Biparser (Digit × Digit) (Digit × Digit) := do
  pChar 'A'
  let d1 ← comap Prod.fst pDigit
  pChar 'B'
  let d2 ← comap Prod.snd pDigit
  pChar 'C'
  pure (d1, d2)

#eval pADigitBDigit.parse ['A', '5', 'B', '6', 'C', '3'] -- some ((⟨'1', _⟩, ⟨'2', _⟩), ['C'])
#eval pADigitBDigit.print (⟨'5', by decide⟩, ⟨'6', by decide⟩) -- ((⟨'5', _⟩, ⟨'6', _⟩), ['A', '5', 'B', '6', 'C'])

instance : HOrElse (Biparser α β) (Biparser γ δ) (Biparser (α ⊕ γ) (β ⊕ δ)) where
  hOrElse p1 p2 := {
    parse := fun input =>
      match p1.parse input with
      | some ⟨ b, rest ⟩  => some (Sum.inl b, rest)
      | none => match (p2 ()).parse input with
        | some ⟨ c, rest ⟩ => some (Sum.inr c, rest)
        | none => none,
    print := fun a =>
      match a with
      | Sum.inl a' => let (b, rest) := p1.print a'; (Sum.inl b, rest)
      | Sum.inr a' => let (c, rest) := (p2 ()).print a'; (Sum.inr c, rest)
  }

def pADigit : Biparser Digit Digit := do
  pChar 'A'
  let d ← pDigit
  pure d

def pDigitB : Biparser Digit Digit := do
  let d ← pDigit
  pChar 'B'
  pure d

def pAAOrDigitB : Biparser (Digit ⊕ Digit) (Digit ⊕ Digit) := pADigit <|> pDigitB

#eval pAAOrDigitB.parse ['A', '1', 'C'] -- some (⟨'1', _⟩, ['C'])
#eval pAAOrDigitB.parse ['3', 'B', 'C'] -- some (⟨'1', _⟩, ['C'])
#eval pAAOrDigitB.print (Sum.inl ⟨'1', by decide⟩) -- (Sum.inl ⟨'1', _⟩, ['A', '1'])
#eval pAAOrDigitB.print (Sum.inr ⟨'3', by decide⟩) -- (Sum.inr ⟨'2', _⟩, ['2', 'B'])
