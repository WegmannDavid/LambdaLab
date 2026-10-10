import LambdaLab.Languages.SystemF.Pipeline
import LambdaLab.Pipeline.Cli

/-!
# `systemf` — System F, as a command-line compiler

    lake exe systemf PATH...

Reads each file (or every `.sf` file under a directory), parses it, type-checks every definition
against its declared type, evaluates each to its normal form — total, by strong normalization —
and writes the result back out. `type` declarations are abbreviations; the evaluated terms are
printed with every abbreviation and earlier definition unfolded.
-/

open LambdaLab.Pipeline LambdaLab.Languages.SystemF

def main (args : List String) : IO UInt32 :=
  cli "systemf" "sf" (compile systemFChain) args
