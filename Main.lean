import LambdaLab

open LambdaLab.Stlc.DeBruijn LambdaLab.Stlc.DeBruijn.Examples

def main : IO Unit :=
  IO.println s!"app1 = {repr app1}"
