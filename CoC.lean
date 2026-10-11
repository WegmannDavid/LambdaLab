import LambdaLab.Languages.CoC.Pipeline
import LambdaLab.Pipeline.Cli

/-!
# `coc` — the Calculus of Constructions, as a command-line compiler

    lake exe coc PATH...

Reads each file (or every `.coc` file under a directory), parses it, type-checks every definition
against its declared type, evaluates each to its normal form — total, by strong normalization —
and writes the result back out. Earlier definitions are transparent: a later one may use what they
*are*, and the evaluated terms are printed with every earlier definition unfolded.
-/

open LambdaLab.Pipeline LambdaLab.Languages.CoC

def main (args : List String) : IO UInt32 :=
  cli "coc" "coc" (compile cocChain) args
