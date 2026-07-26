
abbrev Parser α := List Char → Option (α × List Char)

instance : Monad Parser where
  pure a := fun input => some (a, input)
  bind p f := fun input => do
    let (a, rest) ← p input
    f a rest

def pChar (c : Char) : Parser Unit := fun input =>
  match input with
  | [] => none
  | h :: t => if h = c then some ((), t) else none

def pAB : Parser Unit := do
  pChar 'A'
  pChar 'B'
  pure ()

abbrev Digit := {c : Char // c.isDigit}

def pDigit : Parser Digit := fun input =>
  match input with
  | [] => none
  | h :: t => if Heq : h.isDigit then some (⟨h, Heq⟩, t) else none

instance : OrElse (Parser α) where
  orElse p1 p2 := fun input =>
    match p1 input with
    | some res => some res
    | none => p2 () input

def pADigit : Parser Digit := do
  pChar 'A'
  let d ← pDigit
  pure d

def pDigitB : Parser Digit := do
  let d ← pDigit
  pChar 'B'
  pure d

def pAAOrDigitB : Parser Digit := pADigit <|> pDigitB

#eval pAAOrDigitB ['A', '1', 'C'] -- some (⟨'1', _⟩, ['C'])
#eval pAAOrDigitB ['3', 'B', 'C'] -- some (⟨'1', _⟩, ['C'])
