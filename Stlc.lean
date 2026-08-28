import LambdaLab.Stlc.Named.Pipeline
import LambdaLab.Pipeline.Cli

/-!
# `stlc` — the simply-typed lambda calculus, as a command-line compiler

    lake exe stlc PATH...

Reads each file (or every `.stlc` file under a directory), parses it, elaborates it, evaluates it,
and writes the result back out with every metavariable solved and every redex gone.
`LambdaLab/Pipeline/Cli.lean` is the whole driver; this file only says which language and how far
to take it.
-/

open LambdaLab.Pipeline LambdaLab.Stlc.Named

def main (args : List String) : IO UInt32 :=
  cli "stlc" "stlc" stlcLanguage.compileEval args
