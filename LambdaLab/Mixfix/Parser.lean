import LambdaLab.Mixfix.Open

open Std.Internal Parsec String

def Precedence A := List (OpenNotation A)

structure MixfixGrammar (A : Type) where
  precedence : List (OpenNotation A)
  closed : List (ClosedNotation A)
  juxta : Option (A → A → A)

def pAllClosed (pExpr : Parser A) (l : List (ClosedNotation A)) :=
  pAlternatives (l.map (pClosedNotation pExpr))

partial def juxta (t : A → A → A) (pC : Parser A) : Parser A :=
  let rec helper l :=
    (attempt (do let r ← pC
                 helper (t l r))) <|> return l
  do let l ← pC
     helper l

def pLevels (pExpr : Parser A) (g : MixfixGrammar A) (l : Precedence A) : Parser A :=
    match l with
    | [] => match g.juxta with
            | some t => juxta t (pAllClosed pExpr g.closed)
            | none   => pAllClosed pExpr g.closed
    | n::ns => do
      let pUp  := pLevels pExpr g ns
      let pNot := pOpenNotation pExpr pUp n
      attempt pNot <|> pUp




partial def pExpr (g : MixfixGrammar A) : Parser A := pLevels (pExpr g) g g.precedence

def parentheses : ClosedNotation A := {
  c:= .expr "(" (.last ")")
  term := id }
