import LambdaLab.Parser.Playground.Basic

namespace LambdaLab.Parser.Playground

mutual
  inductive Children (G : Grammar) : Nat → Type where
  | part : Tree G → Children G n → Children G (.succ n)
  | last : Children G 0

  inductive Tree (G : Grammar) : Type where
  | op : (o : G.Op) → Children G (G.arity o) → Tree G
end

mutual
  def Children.flatten (d : OpDesc n) (c : Children G n) : List Token :=
    match c, d with
    | .part t cs, .part tkn ds => [tkn] ++ t.flatten ++ Children.flatten ds cs
    | .last, .last tkn => [tkn]

  def Tree.flatten (t : Tree G) : List Token :=
    match t with
    | .op o cs => Children.flatten (G.OpDescs o) cs
end

end LambdaLab.Parser.Playground
