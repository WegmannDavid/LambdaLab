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

/-! ### `flatten` stays inside the grammar's vocabulary

Every token a tree flattens to is a variable of some entry or a name token of some operator —
so any property of the whole vocabulary (e.g. "is not the hole token `_`") transfers to every
printed tree. -/

/-- A notation's parts spell only its tokens. -/
theorem Notation.namePart_mem_toParts {G : Grammar Tok} :
    ∀ {n : Notation Tok G.Ent} {tkn : Tok},
      Part.namePart tkn ∈ Notation.toParts (G := G) n → tkn ∈ n.toTokens
  | .last t, tkn, h => by
      rw [Notation.toParts] at h
      rw [Notation.toTokens]
      cases List.mem_cons.mp h with
      | inl heq => exact List.mem_cons.mpr (Or.inl (Part.namePart.inj heq))
      | inr hmem => cases hmem
  | .cons t e' rest, tkn, h => by
      rw [Notation.toParts] at h
      rw [Notation.toTokens]
      cases List.mem_cons.mp h with
      | inl heq => exact List.mem_cons.mpr (Or.inl (Part.namePart.inj heq))
      | inr hmem =>
          cases List.mem_cons.mp hmem with
          | inl heq => cases heq
          | inr hmem' =>
              exact List.mem_cons.mpr (Or.inr (Notation.namePart_mem_toParts hmem'))

/-- An operator's body spells only its name tokens — the fixity's operand holes add none. -/
theorem Operator.namePart_mem_body {G : Grammar Tok} {e : G.Ent} {o : (G.entry e).Op} {tkn : Tok}
    (h : Part.namePart tkn ∈ Operator.body e o) :
    tkn ∈ ((G.entry e).operator o).nameTokens := by
  have elim_hole : ∀ {e' : G.Ent} {l : Level (G.entry e')} {res : Prop},
      Part.namePart tkn ∈ [Part.hole e' l] → res := by
    intro e' l res hm
    cases List.mem_cons.mp hm with
    | inl heq => cases heq
    | inr hm' => cases hm'
  rw [Operator.body] at h
  cases hop : (G.entry e).operator o <;> rw [hop] at h <;> dsimp only at h <;>
    rw [Operator.nameTokens]
  case closed n => exact Notation.namePart_mem_toParts h
  case prefx n =>
    cases List.mem_append.mp h with
    | inl hm => exact Notation.namePart_mem_toParts hm
    | inr hm => exact elim_hole hm
  case infx n =>
    cases List.mem_append.mp h with
    | inl hm =>
        cases List.mem_append.mp hm with
        | inl hm' => exact elim_hole hm'
        | inr hm' => exact Notation.namePart_mem_toParts hm'
    | inr hm => exact elim_hole hm
  case infxl n =>
    cases List.mem_append.mp h with
    | inl hm =>
        cases List.mem_append.mp hm with
        | inl hm' => exact elim_hole hm'
        | inr hm' => exact Notation.namePart_mem_toParts hm'
    | inr hm => exact elim_hole hm
  case infxr n =>
    cases List.mem_append.mp h with
    | inl hm =>
        cases List.mem_append.mp hm with
        | inl hm' => exact elim_hole hm'
        | inr hm' => exact Notation.namePart_mem_toParts hm'
    | inr hm => exact elim_hole hm
  case postfx n =>
    cases List.mem_append.mp h with
    | inl hm => exact elim_hole hm
    | inr hm => exact Notation.namePart_mem_toParts hm
  case juxt =>
    cases List.mem_cons.mp h with
    | inl heq => cases heq
    | inr hm => exact elim_hole hm

mutual
  /-- Every token of a flattened tree satisfies any `P` that holds of all variables and all
  operator name tokens. -/
  theorem Expr.flatten_vocab {G : Grammar Tok} (P : Tok → Prop)
      (hvar : ∀ (e : G.Ent) (t : Tok), (G.entry e).isVar t = true → P t)
      (hname : ∀ (e : G.Ent) (o : (G.entry e).Op) (t : Tok),
        t ∈ ((G.entry e).operator o).nameTokens → P t) :
      ∀ {e : G.Ent} {l : Level (G.entry e)} (t : Expr G e l), ∀ tok ∈ t.flatten, P tok
    | _, _, .op o _ ps, tok, htok => by
        rw [Expr.flatten] at htok
        exact Parts.flatten_vocab P hvar hname ps
          (fun tkn hm => hname _ o tkn (Operator.namePart_mem_body hm)) tok htok
    | _, _, .var t ht, tok, htok => by
        rw [Expr.flatten] at htok
        cases List.mem_cons.mp htok with
        | inl heq => exact heq ▸ hvar _ t ht
        | inr hmem => cases hmem

  /-- The `Parts` half: the shape provides where its name-part tokens may come from. -/
  theorem Parts.flatten_vocab {G : Grammar Tok} (P : Tok → Prop)
      (hvar : ∀ (e : G.Ent) (t : Tok), (G.entry e).isVar t = true → P t)
      (hname : ∀ (e : G.Ent) (o : (G.entry e).Op) (t : Tok),
        t ∈ ((G.entry e).operator o).nameTokens → P t) :
      ∀ {shape : List (Part G)} (ps : Parts G shape),
        (∀ tkn, Part.namePart tkn ∈ shape → P tkn) → ∀ tok ∈ ps.flatten, P tok
    | _, .nil, _, tok, htok => by rw [Parts.flatten] at htok; cases htok
    | _, .namePart tkn ps, hsh, tok, htok => by
        rw [Parts.flatten] at htok
        cases List.mem_cons.mp htok with
        | inl heq => exact heq ▸ hsh tkn (List.mem_cons.mpr (Or.inl rfl))
        | inr hmem =>
            exact Parts.flatten_vocab P hvar hname ps
              (fun t' hm => hsh t' (List.mem_cons_of_mem _ hm)) tok hmem
    | _, .hole ex ps, hsh, tok, htok => by
        rw [Parts.flatten] at htok
        cases List.mem_append.mp htok with
        | inl hmem => exact Expr.flatten_vocab P hvar hname ex tok hmem
        | inr hmem =>
            exact Parts.flatten_vocab P hvar hname ps
              (fun t' hm => hsh t' (List.mem_cons_of_mem _ hm)) tok hmem
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
