import LambdaLab.Languages.CoIC.Pipeline
import LambdaLab.Pipeline.Cli

/-!
# `coic` — the Calculus of Constructions with inductive types, as a command-line compiler

    lake exe coic PATH...

Reads each file (or every `.coic` file under a directory), parses it, checks every declaration —
each definition against its declared type, each inductive type's constructors — evaluates each
definition to its normal form — total, by strong normalization — and writes the result back out.
-/

open LambdaLab.Pipeline LambdaLab.Languages.CoIC

def main (args : List String) : IO UInt32 :=
  cli "coic" "coic" (compile coicChain) args
