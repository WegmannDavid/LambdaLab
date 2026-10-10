import LambdaLab.Languages.Float.Pipeline
import LambdaLab.Pipeline.Cli

/-!
# `float` — decimal sums and products, as a command-line compiler

    lake exe float PATH...

Reads each file (or every `.float` file under a directory), parses it, evaluates every
declaration in the light of the ones before it, and writes the result back out: each term replaced
by the exact decimal it denotes.

`float` has no type system and needs none. Its semantics is one walk — a map from names to values,
carried through the declarations — and `floatChain` is that walk after the parser, which is all
`cli` is handed.
-/

open LambdaLab.Pipeline LambdaLab.Languages.Float

def main (args : List String) : IO UInt32 :=
  cli "float" "float" (compile floatChain) args
