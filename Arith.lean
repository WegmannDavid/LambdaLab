import LambdaLab.Arith.Pipeline
import LambdaLab.Pipeline.Cli

/-!
# `arith` — the mixfix arithmetic vernacular, as a command-line compiler

    lake exe arith PATH...

Reads each file (or every `.arith` file under a directory), parses it, and writes it back out in canonical form: redundant parentheses
forgotten and re-inserted where the grammar needs them, spacing normalised.

It stops there, and that is not an omission — `Arith` has no type system, so it has no
`PrincipalElaborate` instance and no elaboration stage to run. `compileParse` rather than
`compileElab` is exactly that fact, in the type.
-/

open LambdaLab.Pipeline LambdaLab.Arith

def main (args : List String) : IO UInt32 :=
  cli "arith" "arith" arithLanguage.compileParse args
