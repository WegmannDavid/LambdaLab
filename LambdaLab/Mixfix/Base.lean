import Std.Internal.Parsec.String

open Std.Internal Parsec String

def lexeme (p : Parser α) : Parser α := p <* ws

def pSymbol (s : String) : Parser String := lexeme (pstring s)

def pAlpha (P : String → Bool) : Parser String := attempt do
  let name ← many1Chars (satisfy fun c => c.isAlpha || c == '_')
  if P name then
    fail s!"'{name}' is a reserved keyword and cannot be used as a variable name"
  else
    pure name

def pAlternatives (l : List (Parser A)) : Parser A :=
  match l with
  | []    => fail "No more alternatives"
  | p::ps => attempt p <|> pAlternatives ps
