import LambdaLab.Parser.Playground.Example

/-!
# Playground parser demo

A tiny CLI that runs the verified precedence-DAG mixfix parser
(`LambdaLab.Parser.Playground`) over the concrete `arith` and `mix` grammars
from `Example.lean`.

* `lake exe playground`            — run the built-in showcase
* `lake exe playground n + n * n`  — parse the given tokens with `arith`

Each line shows the input and the parser's output. Because both grammars are
unambiguous, an accepted input yields exactly one parse (printed as the
re-flattened token string) and a rejected input yields none.
-/

open LambdaLab.Parser (Token)
open LambdaLab.Parser.Playground

/-- Render a token list as a space-separated string. -/
def renderTokens (ts : List Token) : String := " ".intercalate ts

/-- Parse `input` in grammar `G` and describe the result on one line. -/
def report (G : Grammar) (input : List Token) : String :=
  let parses := (parse (G := G) input).map (·.flatten)
  let lhs := renderTokens input
  match parses with
  | []  => s!"  {lhs}  ⟹  (rejected)"
  | [p] => s!"  {lhs}  ⟹  {renderTokens p}"
  | _   => s!"  {lhs}  ⟹  {parses.length} parses: " ++
             ", ".intercalate (parses.map renderTokens)

def arithExamples : List (List Token) :=
  [ ["n"],
    ["n", "+", "n"],
    ["(", "n", ")"],
    ["n", "+", "n", "*", "n"],
    ["n", "*", "n", "+", "n"],
    ["n", "+", "n", "+", "n"],
    ["(", "n", "+", "n", ")", "*", "n"],
    ["+", "n"],
    ["n", "+"] ]

def mixExamples : List (List Token) :=
  [ ["-", "x"],
    ["-", "-", "x"],
    ["x", "!"],
    ["x", "!", "!"],
    ["x", "^", "x", "^", "x"],
    ["x", "=", "x"],
    ["x", "=", "x", "=", "x"],
    ["-", "x", "!"] ]

def main (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.println "arith  (precedence:  + < * < atoms/parens):"
    for e in arithExamples do IO.println (report arith e)
    IO.println ""
    IO.println "mix  (prefix -, postfix !, infix-right ^, non-assoc =):"
    for e in mixExamples do IO.println (report mix e)
    IO.println ""
    IO.println "Pass tokens as arguments to parse them with `arith`,"
    IO.println "e.g.  lake exe playground n + n '*' n"
  else
    IO.println (report arith args)
