import LambdaLab.Parser.Playground3.Basic

namespace LambdaLab.Parser.Playground3

open LambdaLab.Parser

/-- A precedence *level*: the constraint placed on a tree's top operator. -/
inductive Level (G : Grammar) : Type where
| tighter   : G.Op → Level G
| tighterEq : G.Op → Level G
| loosest   : Level G

/-- The predicate a top operator `b` must satisfy to inhabit level `l`. -/
def Level.condition {G : Grammar} (l : Level G) : G.Op → Prop :=
  match l with
  | Level.tighter a   => fun b => Tighter G.tighter a b
  | Level.tighterEq a => fun b => TighterEq G.tighter a b
  | Level.loosest     => fun b => ∃ a, a ∈ G.loosest ∧ TighterEq G.tighter a b

inductive Part (G : Grammar) where
| hole     : Level G → Part G
| namePart : Token   → Part G

def Part.inner {G : Grammar} (parts : NonEmptyList Token) : List (Part G) :=
  match parts with
  | .last tkn        => [.namePart tkn]
  | .cons tkn parts' => [.namePart tkn, .hole Level.loosest] ++ inner parts'

def Part.parts {G : Grammar} (o : G.Op) : List (Part G) :=
  match G.operator o with
  | .closed tkns => Part.inner tkns
  | .prefx  tkns => Part.inner tkns ++ [.hole (.tighter o)]
  | .infx   tkns => [.hole (.tighter o)] ++ Part.inner tkns ++ [.hole (.tighter o)]

mutual
  inductive Expr (G : Grammar) : Level G → Type where
  | op : (o : G.Op) → Level.condition l o → Parts G (Part.parts o) → Expr G l

  inductive Parts (G : Grammar) : List (Part G) → Type where
  | nil : Parts G .nil
  | hole : Expr G l → Parts G ps → Parts G ((.hole l)::ps)
  | namePart : (tkn : Token) → Parts G ps → Parts G ((.namePart tkn)::ps)
end

mutual
  def Expr.flatten (e : Expr G l) : List Token :=
    match e with
    |.op _ _ l => l.flatten

  def Parts.flatten (l : Parts G shape) : List Token :=
    match l with
    | .nil => []
    | .hole e ps => e.flatten ++ ps.flatten
    | .namePart tkn ps => [tkn] ++ ps.flatten
end
