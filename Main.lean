import LambdaLab.Stlc.Compiler.Compile

open Std.Internal.Parsec

/-

def α : Ty := ? 3
def β : Ty := ? 2 ⟶ ? 4

def testUnification : IO Unit := do
  IO.println s!"α = {α}"
  IO.println s!"β = {β}"
  IO.println s!"{mgu? (unify α β)}"

def t : Tm := (ƛ "x" : ! "Int" => (ƛ "f" : ? 1 => # "f" ⬝ (# "f" ⬝ # "x")))
def s : Tm := (ƛ "x" : ?0 => # "x")
def y : Tm := (ƛ "f" : ?0 => # "f" ⬝ # "f")

-/
def testExcept {α} [ToString ε] [ToString α] (e : Except ε α) : IO Unit :=
  match e with
  | .ok r => IO.println s!"success: {r}"
  | .error msg => IO.println msg

def source1 := "\
def f := λ y : Int . y;\
def g : Int → Int := f;"
def main : IO Unit := testExcept (compile source1)
