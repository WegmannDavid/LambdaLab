
abbrev Parser (α : Type) := List Char → Option (α × List Char)

instance : Monad Parser where
  pure a input := some (a, input)
  bind p f input := do
    let (a, rest) ← p input
    f a rest

def pChar (c : Char) : Parser Char := fun input =>
  match input with
  | [] => none
  | hd :: tl => if hd = c then some (hd, tl) else none

instance : Alternative Parser where
  failure := fun _ => none
  orElse p1 p2 := λ input =>
    match p1 input with
    | some res => some res
    | none => p2 () input

mutual
partial def many (p : Parser α) : Parser (List α) := many1 p <|> (do return [])

partial def many1 (p : Parser α) : Parser (List α) := do
  let x ← p
  let xs ← many p
  pure (x :: xs)
end

def digit : Parser Char := fun input =>
  match input with
  | [] => none
  | hd :: tl => if hd.isDigit then some (hd, tl) else none

def pDigitList := many1 digit

def pDigitLists := many1 (do let l ← pDigitList; let _ ← pChar ';' ;  return l)

#eval digit "123".toList
#eval pDigitList "123".toList
#eval pDigitLists "123;45;6789;".toList
