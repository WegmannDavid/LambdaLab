import LambdaLab.Biparser.Mixfix.Basic

namespace LambdaLab.Biparser.Mixfix

/-- A precedence *level* within a single entry `E`: the constraint placed on a
tree's top operator. -/
inductive Level {sep : Char → Bool} {Ent : Type} (E : Entry sep Ent) : Type where
| tighter   : E.Op → Level E
| tighterEq : E.Op → Level E
| loosest   : Level E

/-- The predicate a top operator `b` must satisfy to inhabit level `l` of `E`. -/
def Level.condition {sep : Char → Bool} {Ent : Type} {E : Entry sep Ent} (l : Level E) :
    E.Op → Prop :=
  match l with
  | Level.tighter a   => fun b => Tighter E.tighter a b
  | Level.tighterEq a => fun b => TighterEq E.tighter a b
  | Level.loosest     => fun b => ∃ a, a ∈ E.loosest ∧ TighterEq E.tighter a b

/-- A piece of an operator's body: a literal name token, or a **hole** referencing
an entry `e` of the grammar at a precedence level within that entry. The hole is
filled by an `Expr` of entry `e` — recursive (`e` the host entry) or cross-entry
(`e` a different class of expressions) are the *same* construct. -/
inductive Part (G : Grammar) where
| namePart : Token G.isSep → Part G
| hole     : (e : G.Ent) → Level (G.entry e) → Part G

/-- Lower a `Notation` to its parts: a `namePart` per token; each interior hole
references its entry `e'` parsed at that entry's `loosest` level. -/
def Notation.toParts {G : Grammar} : Notation G.isSep G.Ent → List (Part G)
  | .last tkn         => [.namePart tkn]
  | .cons tkn e' rest => [.namePart tkn, .hole e' Level.loosest] ++ rest.toParts

/-- The lowered body of operator `o` of entry `e`: the notation's parts, wrapped
by the fixity's leading/trailing operand holes — which reference the **host**
entry `e` at strictly- or loosely-tighter levels (where precedence lives). -/
def Operator.body {G : Grammar} (e : G.Ent) (o : (G.entry e).Op) : List (Part G) :=
  match (G.entry e).operator o with
  | .closed n => Notation.toParts n
  | .prefx  n => Notation.toParts n ++ [.hole e (.tighter o)]
  | .infx   n => [.hole e (.tighter o)] ++ Notation.toParts n ++ [.hole e (.tighter o)]
  | .infxl  n => [.hole e (.tighterEq o)] ++ Notation.toParts n ++ [.hole e (.tighter o)]
  | .infxr  n => [.hole e (.tighter o)] ++ Notation.toParts n ++ [.hole e (.tighterEq o)]
  | .postfx n => [.hole e (.tighter o)] ++ Notation.toParts n
  | .juxt => [.hole e (.tighterEq o), .hole e (.tighter o)]

mutual
  /-- A parse tree of entry `e` at level `l`. No universe bump: a hole stores an
  `Expr` of the referenced entry, never a raw `Type`. -/
  inductive Expr (G : Grammar) : (e : G.Ent) → Level (G.entry e) → Type where
  | op {e : G.Ent} {l : Level (G.entry e)} (o : (G.entry e).Op) :
      Level.condition l o → Parts G (Operator.body e o) → Expr G e l
  /-- A variable leaf: an identifier token (`(G.entry e).isVar`), valid at every
  level of its entry. -/
  | var {e : G.Ent} {l : Level (G.entry e)} (t : Token G.isSep) :
      (G.entry e).isVar t = true → Expr G e l

  inductive Parts (G : Grammar) : List (Part G) → Type where
  | nil : Parts G []
  | namePart {ps} (tkn : Token G.isSep) : Parts G ps → Parts G ((.namePart tkn) :: ps)
  | hole {e : G.Ent} {l : Level (G.entry e)} {ps} :
      Expr G e l → Parts G ps → Parts G ((.hole e l) :: ps)
end

mutual
  def Expr.flatten {G : Grammar} {e : G.Ent} {l : Level (G.entry e)} :
      Expr G e l → List (Token G.isSep)
    | .op _ _ ps => ps.flatten
    | .var t _   => [t]

  def Parts.flatten {G : Grammar} {shape : List (Part G)} : Parts G shape → List (Token G.isSep)
    | .nil             => []
    | .namePart tkn ps => tkn :: ps.flatten
    | .hole ex ps      => ex.flatten ++ ps.flatten
end

end LambdaLab.Biparser.Mixfix
