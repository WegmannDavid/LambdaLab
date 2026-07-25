import LambdaLab.Parser.IsoParser.Mixfix.Basic

/-!
# Mixfix parse trees — precedence-indexed `Expr`, and `flatten`

`Expr G e l` is a tree of entry `e` whose top operator is constrained to level `l` (a precedence
node). `flatten` is the printer: it walks the tree back to its token list. Both are self-contained
over the abstract token alphabet `Tok`.
-/

namespace LambdaLab.Parser.IsoParser.Mixfix

variable {Tok : Type}

/-- A precedence *level* within one entry `E`: the constraint on a tree's top operator. -/
inductive Level {Tok Ent : Type} (E : Entry Tok Ent) : Type where
  | tighter   : E.Op → Level E
  | tighterEq : E.Op → Level E
  | loosest   : Level E

/-- The predicate a top operator `b` must satisfy to inhabit level `l` of `E`. -/
def Level.condition {Tok Ent : Type} {E : Entry Tok Ent} (l : Level E) : E.Op → Prop :=
  match l with
  | Level.tighter a   => fun b => Tighter E.tighter a b
  | Level.tighterEq a => fun b => TighterEq E.tighter a b
  | Level.loosest     => fun b => ∃ a, a ∈ E.loosest ∧ TighterEq E.tighter a b

/-- Level conditions are decidable (via the fuel-based reachability), so grammar-shaped side
conditions discharge `by decide`. -/
instance {Tok Ent : Type} {E : Entry Tok Ent} [DecidableEq E.Op] (l : Level E) (o : E.Op) :
    Decidable (l.condition o) :=
  match l with
  | Level.tighter _   => inferInstanceAs (Decidable (Tighter _ _ _))
  | Level.tighterEq _ => inferInstanceAs (Decidable (TighterEq _ _ _))
  | Level.loosest     => inferInstanceAs (Decidable (∃ a, a ∈ E.loosest ∧ TighterEq _ a o))

/-- A piece of an operator's body: a literal name token, or a **hole** referencing an entry `e` at a
precedence level within it (recursive or cross-entry — the same construct). -/
inductive Part (G : Grammar Tok) where
  | namePart : Tok → Part G
  | hole     : (e : G.Ent) → Level (G.entry e) → Part G

/-- Lower a notation to its parts: a `namePart` per token; each interior hole references its entry at
that entry's `loosest` level. -/
def Notation.toParts {G : Grammar Tok} : Notation Tok G.Ent → List (Part G)
  | .last tkn         => [.namePart tkn]
  | .cons tkn e' rest => [.namePart tkn, .hole e' Level.loosest] ++ rest.toParts

/-- The lowered body of operator `o` of entry `e`: the notation's parts wrapped by the fixity's
leading/trailing operand holes, which reference the **host** entry `e` at the precedence levels the
fixity dictates. -/
def Operator.body {G : Grammar Tok} (e : G.Ent) (o : (G.entry e).Op) : List (Part G) :=
  match (G.entry e).operator o with
  | .closed n => Notation.toParts n
  | .prefx  n => Notation.toParts n ++ [.hole e (.tighter o)]
  | .infx   n => [.hole e (.tighter o)] ++ Notation.toParts n ++ [.hole e (.tighter o)]
  | .infxl  n => [.hole e (.tighterEq o)] ++ Notation.toParts n ++ [.hole e (.tighter o)]
  | .infxr  n => [.hole e (.tighter o)] ++ Notation.toParts n ++ [.hole e (.tighterEq o)]
  | .postfx n => [.hole e (.tighter o)] ++ Notation.toParts n
  | .juxt => [.hole e (.tighterEq o), .hole e (.tighter o)]

mutual
  /-- A parse tree of entry `e` at level `l`. -/
  inductive Expr (G : Grammar Tok) : (e : G.Ent) → Level (G.entry e) → Type where
    | op {e : G.Ent} {l : Level (G.entry e)} (o : (G.entry e).Op) :
        Level.condition l o → Parts G (Operator.body e o) → Expr G e l
    /-- A variable leaf: an identifier token, valid at every level of its entry. -/
    | var {e : G.Ent} {l : Level (G.entry e)} (t : Tok) :
        (G.entry e).isVar t = true → Expr G e l

  inductive Parts (G : Grammar Tok) : List (Part G) → Type where
    | nil : Parts G []
    | namePart {ps} (tkn : Tok) : Parts G ps → Parts G ((.namePart tkn) :: ps)
    | hole {e : G.Ent} {l : Level (G.entry e)} {ps} :
        Expr G e l → Parts G ps → Parts G ((.hole e l) :: ps)
end

mutual
  def Expr.flatten {G : Grammar Tok} {e : G.Ent} {l : Level (G.entry e)} :
      Expr G e l → List Tok
    | .op _ _ ps => ps.flatten
    | .var t _   => [t]

  def Parts.flatten {G : Grammar Tok} {shape : List (Part G)} : Parts G shape → List Tok
    | .nil             => []
    | .namePart tkn ps => tkn :: ps.flatten
    | .hole ex ps      => ex.flatten ++ ps.flatten
end

mutual
  /-- A structural size, every constructor counting one — the termination measure for recursions
  over `Expr` (e.g. truncations): the auto-generated `sizeOf` of this mutual indexed family has
  no usable spec lemmas, and the padding makes subterm goals pure arithmetic. -/
  def Expr.size {G : Grammar Tok} {e : G.Ent} {l : Level (G.entry e)} : Expr G e l → Nat
    | .op _ _ ps => 1 + ps.size
    | .var _ _   => 1

  def Parts.size {G : Grammar Tok} {shape : List (Part G)} : Parts G shape → Nat
    | .nil             => 0
    | .namePart _ ps   => 1 + ps.size
    | .hole ex ps      => 1 + ex.size + ps.size
end

end LambdaLab.Parser.IsoParser.Mixfix
