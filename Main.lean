import LambdaLab

open LambdaLab.Parser.Mixfix

/-! ## Demo grammar

A toy mixfix grammar over `String`: parens and a list-pair operator,
with atoms identifying themselves. Demonstrates the parser running on
actual input. -/

def parens : Operator Unit String := {
  fixity := .closed
  nameParts := ["(", ")"]
  nameParts_ne_nil := by decide
  holes := [.recurse]
  holes_match_arity := by decide
  build := fun (a : String) => "(" ++ a ++ ")"
}

def pair : Operator Unit String := {
  fixity := .closed
  nameParts := ["[", ",", "]"]
  nameParts_ne_nil := by decide
  holes := [.recurse, .recurse]
  holes_match_arity := by decide
  build := fun (a b : String) => "[" ++ a ++ ", " ++ b ++ "]"
}

/-- Prefix unary `! _`. -/
def notOp : Operator Unit String := {
  fixity := .prefix
  nameParts := ["!"]
  nameParts_ne_nil := by decide
  holes := [.recurse]
  holes_match_arity := by decide
  build := fun (a : String) => "(!" ++ a ++ ")"
}

/-- Prefix lambda `λ _ . _`: takes a variable name (sub-parsed) and a
recursive body. -/
def lamOp : Operator Unit String := {
  fixity := .prefix
  nameParts := ["λ", "."]
  nameParts_ne_nil := by decide
  holes := [.sub stringParser, .recurse]
  holes_match_arity := by decide
  build := fun (x : String) (body : String) => "(λ" ++ x ++ "." ++ body ++ ")"
}

/-- Postfix unary `_ ?` (asks if). -/
def askOp : Operator Unit String := {
  fixity := .postfix
  nameParts := ["?"]
  nameParts_ne_nil := by decide
  holes := [.recurse]
  holes_match_arity := by decide
  build := fun (a : String) => "(" ++ a ++ "?)"
}

/-- Infix binary `_ + _`. -/
def plusOp : Operator Unit String := {
  fixity := .infix .left
  nameParts := ["+"]
  nameParts_ne_nil := by decide
  holes := [.recurse, .recurse]
  holes_match_arity := by decide
  build := fun (a b : String) => "(" ++ a ++ "+" ++ b ++ ")"
}

def demoGrammar : Grammar Unit String := {
  levels := [[parens, pair, notOp, lamOp, askOp, plusOp]]
  atomBuild := id
  juxtBuild := some (fun a b => "(" ++ a ++ " " ++ b ++ ")")
}

/-- Whitespace tokenizer: splits on spaces and drops empty pieces. -/
def tokenize (s : String) : List String :=
  s.splitOn " " |>.filter (· != "")

/-- Pretty-print a parse outcome. -/
def showResult : Option String → String
  | some s => s!"parsed:  {s}"
  | none   => "parse failed"

def runOne (s : String) : IO Unit := do
  let toks := tokenize s
  IO.println s!"input:   {s}"
  IO.println s!"tokens:  {toks}"
  IO.println (showResult ((parseAll demoGrammar () toks).map (·.snd)))
  IO.println ""

def main (args : List String) : IO Unit := do
  if args.isEmpty then
    -- No args: run a few canned examples.
    runOne "x"
    runOne "( x )"
    runOne "[ x , y ]"
    runOne "[ ( x ) , [ a , b ] ]"
    runOne "! x"
    runOne "! ( x )"
    runOne "λ x . x"
    runOne "λ f . λ x . f"
    runOne "[ ! x , λ y . y ]"
    runOne "x ?"
    runOne "x ? ?"
    runOne "x + y"
    runOne "x + y + z"
    runOne "( x + y ) ?"
    runOne "x y"
    runOne "f x y"
    runOne "( λ x . x ) y"
    runOne "f x + g y"
    runOne "[ x"
  else
    -- Parse each argument as a separate input.
    for s in args do
      runOne s
