import LambdaLab.Stlc.Named.Pipeline
import LambdaLab.Pipeline.Cli

/-!
# `stlc` — the simply-typed lambda calculus, as a command-line compiler

    lake exe stlc FILE...

Reads each file, parses it, elaborates it, and writes the result back out with every metavariable
solved. `LambdaLab/Pipeline/Cli.lean` is the whole driver; this file only says which language and
how far to take it.
-/

open LambdaLab.Pipeline LambdaLab.Stlc.Named

def main (args : List String) : IO UInt32 :=
  cli "stlc" stlcLanguage.compileElab args
