import LambdaLab.Parser.Basic


namespace LambdaLab.Parser.Playground


inductive OpDesc : Nat → Type where
| part : Token → OpDesc n → OpDesc (.succ n)
| last : Token → OpDesc 0

def beginsWith (d : OpDesc n) (tkn : Token) : Bool :=
  match d with
  | .part t _ => t = tkn
  | .last t => t = tkn

structure Operator

structure Grammar where
  Op : Type
  arity : Op → Nat
  OpDescs : (o : Op) → OpDesc (arity o)
  lookup : Token → Option Op
  /-- Well-formedness: `lookup` is the inverse of "leading name-part". A token
  resolves to `o` iff it is the first token of `o`'s shape. Being a function,
  this also forces leading tokens to be distinct across operators — the
  unique-reading condition that makes parsing invert flattening. -/
  lookup_spec : ∀ o tkn, beginsWith (OpDescs o) tkn = true ↔ lookup tkn = some o

end LambdaLab.Parser.Playground
