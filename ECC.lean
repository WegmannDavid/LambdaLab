import LambdaLab.Languages.ECC.Pipeline
import LambdaLab.Pipeline.Lsp

/-!
# `ecc` — the Extended Calculus of Constructions, as a command-line compiler

    lake exe ecc PATH...

Reads each file (or every `.ecc` file under a directory), parses it, type-checks every definition
against its declared type, evaluates each to its normal form, and writes the result back out.
Strong normalization is not proved for ECC with every universe, so checking and evaluation are
partial functions: sound whenever they return, and — if ECC normalizes, as it is believed to —
returning on every well-typed program.
-/

open LambdaLab.Pipeline LambdaLab.Languages.ECC

def main (args : List String) : IO UInt32 :=
  driver "ecc" "ecc" eccLanguage eccChain args
