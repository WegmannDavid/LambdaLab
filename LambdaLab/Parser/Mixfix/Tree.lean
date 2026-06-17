import LambdaLab.Parser.Mixfix.Basic

namespace LambdaLab.Parser.Mixfix

open LambdaLab.Parser

/-- A precedence *level*: the constraint placed on a tree's top operator. -/
inductive Level.{u} (G : Grammar.{u}) : Type where
| tighter   : G.Op → Level G
| tighterEq : G.Op → Level G
| loosest   : Level G

/-- The predicate a top operator `b` must satisfy to inhabit level `l`. -/
def Level.condition.{u} {G : Grammar.{u}} (l : Level G) : G.Op → Prop :=
  match l with
  | Level.tighter a   => fun b => Tighter G.tighter a b
  | Level.tighterEq a => fun b => TighterEq G.tighter a b
  | Level.loosest     => fun b => ∃ a, a ∈ G.loosest ∧ TighterEq G.tighter a b

inductive Part.{u} (G : Grammar.{u}) where
| hole     : Level G → Part G
| namePart : Token   → Part G
/-- A hole parsed by another language (a `VerifiedParser`). -/
| subHole  : VerifiedParser.{u} → Part G

/-- An interior hole lowers to a recursive `loosest` hole or a `subHole`. -/
def InnerHole.toPart.{u} {G : Grammar.{u}} : InnerHole.{u} → Part G
  | .loosest => .hole Level.loosest
  | .sub sp  => .subHole sp

/-- Lower an operator `Notation` to its parts: a `namePart` per token, with each
interior hole lowered by `InnerHole.toPart` (recursive `loosest` or a `subHole`). -/
def Notation.toParts.{u} {G : Grammar.{u}} : Notation.{u} → List (Part G)
  | .last tkn        => [.namePart tkn]
  | .cons tkn h rest => [.namePart tkn, h.toPart] ++ rest.toParts

/-- The lowered body of operator `o`: the `Part` list its tree fills in. -/
def Operator.body.{u} {G : Grammar.{u}} (o : G.Op) : List (Part G) :=
  match G.operator o with
  | .closed n => Notation.toParts n
  | .prefx  n => Notation.toParts n ++ [.hole (.tighter o)]
  | .infx   n => [.hole (.tighter o)] ++ Notation.toParts n ++ [.hole (.tighter o)]
  -- left-assoc: the left operand chains (`.tighterEq`), right is strictly tighter.
  -- Left-recursive (leading `.tighterEq` hole) ⇒ parsed by a fold, like `juxt`.
  | .infxl  n => [.hole (.tighterEq o)] ++ Notation.toParts n ++ [.hole (.tighter o)]
  -- right-assoc: the right operand chains (`.tighterEq`), left is strictly tighter.
  | .infxr  n => [.hole (.tighter o)] ++ Notation.toParts n ++ [.hole (.tighterEq o)]
  | .postfx n => [.hole (.tighter o)] ++ Notation.toParts n
  -- juxtaposition `f x`: left operand at `.tighterEq o` (so application chains,
  -- left-associatively), right operand (argument) at `.tighter o`. No name tokens.
  | .juxt => [.hole (.tighterEq o), .hole (.tighter o)]

mutual
  -- `Type (u+1)`: a `subHole` stores the sub-parser's `Result : Type u`, so the
  -- tree family lives one universe up. `G` stays a *parameter* — the sub-tree is
  -- the bundle's own `Result`, never `Expr G'`, so no cross-grammar indexing.
  -- Universe-polymorphic so a grammar's own trees can be embedded as a
  -- `VerifiedParser.{u+1}` (`Grammar.toVerifiedParser`).
  inductive Expr.{u} (G : Grammar.{u}) : Level G → Type (u+1) where
  | op : (o : G.Op) → Level.condition l o → Parts G (Operator.body o) → Expr G l
  /-- A variable leaf: an identifier token (`G.isVar t`), valid at every level (a
  maximally-tight atom, so no `Level.condition`). The `isVar` proof keeps `var t`
  from masquerading as an operator atom (e.g. `var "n"` vs the `num` operator),
  which would otherwise break `flatten`-injectivity. -/
  | var : (t : Token) → G.isVar t = true → Expr G l

  inductive Parts.{u} (G : Grammar.{u}) : List (Part G) → Type (u+1) where
  | nil : Parts G .nil
  | hole : Expr G l → Parts G ps → Parts G ((.hole l)::ps)
  | namePart : (tkn : Token) → Parts G ps → Parts G ((.namePart tkn)::ps)
  /-- A sub-language hole: stores the sub-parser's own result. -/
  | subHole : (sp : VerifiedParser.{u}) → sp.Result → Parts G ps → Parts G ((.subHole sp)::ps)
end

mutual
  def Expr.flatten.{u} {G : Grammar.{u}} {l : Level G} (e : Expr G l) : List Token :=
    match e with
    |.op _ _ l => l.flatten
    | .var t _ => [t]

  def Parts.flatten.{u} {G : Grammar.{u}} {shape : List (Part G)} (l : Parts G shape) : List Token :=
    match l with
    | .nil => []
    | .hole e ps => e.flatten ++ ps.flatten
    | .namePart tkn ps => [tkn] ++ ps.flatten
    | .subHole sp res ps => sp.flatten res ++ ps.flatten
end
