import LambdaLab.IsoParser.Combinators

/-!
# General mixfix grammar — self-contained (independent of `CBiparser`)

A fresh rebuild of the mixfix grammar for the `IsoParser` stack, so the `IsoParser` folder does not
depend on `CBiparser`. Two deliberate simplifications versus the `CBiparser` original:

* **Abstract token alphabet.** The alphabet is an arbitrary `Tok` with `DecidableEq` — the mixfix
  layer is token-level, so the char-separator machinery (`sep`, `Token sep`) is a tokenizer concern
  it never needs. A concrete grammar instantiates `Tok` however it likes.
* **Explicit precedence rank.** Each operator carries a numeric `rank`; `tighter ⇒ strictly lower
  rank` is a grammar field. This gives the parser's lexicographic termination measure directly,
  without deriving ranks from a well-foundedness witness. Explicit numeric precedence is standard.

Precedence is a DAG: `tighter o` are the operators *immediately* tighter than `o`, `loosest` the
source operators where parsing starts; incomparable operators must be parenthesized.
-/

namespace LambdaLab.IsoParser.Mixfix

/-! ## Operator notations -/

/-- An operator name: a non-empty token sequence with an interior hole (an entry `Ent`) between each
consecutive pair of tokens (the `)` gap of `( _ )`, the `then`/`else` gaps of `if _ then _ else _`). -/
inductive Notation (Tok Ent : Type) where
  | last : Tok → Notation Tok Ent
  | cons : Tok → Ent → Notation Tok Ent → Notation Tok Ent

/-- The name tokens of a notation, in order. -/
def Notation.toTokens {Tok Ent : Type} : Notation Tok Ent → List Tok
  | .last t        => [t]
  | .cons t _ rest => t :: rest.toTokens

/-- The first token of a notation (it is non-empty by construction). -/
def Notation.firstTok {Tok Ent : Type} : Notation Tok Ent → Tok
  | .last t     => t
  | .cons t _ _ => t

/-- The interior seams: each interior hole's entry paired with the token that immediately follows it. -/
def Notation.holeFollowers {Tok Ent : Type} : Notation Tok Ent → List (Ent × Tok)
  | .last _         => []
  | .cons _ e' rest => (e', rest.firstTok) :: rest.holeFollowers

/-! ## Operators (the six fixities plus juxtaposition) -/

inductive Operator (Tok Ent : Type) where
  | closed : Notation Tok Ent → Operator Tok Ent
  | prefx  : Notation Tok Ent → Operator Tok Ent
  /-- Non-associative infix: both operands strictly tighter. -/
  | infx   : Notation Tok Ent → Operator Tok Ent
  /-- Left-associative infix (`a∘b∘c = (a∘b)∘c`): left operand chains (`tighterEq`), right strictly
  tighter. Left-recursive body ⇒ parsed by an iterative fold. -/
  | infxl  : Notation Tok Ent → Operator Tok Ent
  /-- Right-associative infix (`a∘b∘c = a∘(b∘c)`): right operand chains, left strictly tighter. -/
  | infxr  : Notation Tok Ent → Operator Tok Ent
  | postfx : Notation Tok Ent → Operator Tok Ent
  /-- Juxtaposition: a tokenless, left-associative, tightest-binding operator. -/
  | juxt   : Operator Tok Ent

/-- The name-part tokens of an operator, in body order (`juxt` has none). -/
def Operator.nameTokens {Tok Ent : Type} : Operator Tok Ent → List Tok
  | .closed n => n.toTokens
  | .prefx n  => n.toTokens
  | .infx n   => n.toTokens
  | .infxl n  => n.toTokens
  | .infxr n  => n.toTokens
  | .postfx n => n.toTokens
  | .juxt     => []

/-- The leading token the parser dispatches on: the operator's first name-part token, if any. -/
def Operator.headTok? {Tok Ent : Type} (o : Operator Tok Ent) : Option Tok :=
  o.nameTokens.head?

/-- Does this operator begin with a **hole** (take a left operand)? `closed`/`prefx` do not — their
leading token *starts* an operand; every other fixity's leading token *continues* an expression. -/
def Operator.startsWithHole {Tok Ent : Type} : Operator Tok Ent → Bool
  | .closed _ => false
  | .prefx _  => false
  | .infx _   => true
  | .infxl _  => true
  | .infxr _  => true
  | .postfx _ => true
  | .juxt     => true

/-- The interior seams of an operator (`juxt` has none). -/
def Operator.holeFollowers {Tok Ent : Type} : Operator Tok Ent → List (Ent × Tok)
  | .closed n => n.holeFollowers
  | .prefx n  => n.holeFollowers
  | .infx n   => n.holeFollowers
  | .infxl n  => n.holeFollowers
  | .infxr n  => n.holeFollowers
  | .postfx n => n.holeFollowers
  | .juxt     => []

/-! ## Precedence order (reachability through `tighter`) -/

/-- `b` binds at least as tightly as `a`: reachable from `a` by repeatedly stepping into `t`. -/
inductive TighterEq {Op : Type} (t : Op → List Op) : Op → Op → Prop where
  | refl {a} : TighterEq t a a
  | step {a b c} : b ∈ t a → TighterEq t b c → TighterEq t a c

/-- `b` binds *strictly* more tightly than `a`: one or more `tighter` steps. -/
inductive Tighter {Op : Type} (t : Op → List Op) : Op → Op → Prop where
  | base {a b} : b ∈ t a → Tighter t a b
  | step {a b c} : b ∈ t a → Tighter t b c → Tighter t a c

theorem Tighter.toTighterEq {Op : Type} {t : Op → List Op} {a b : Op}
    (h : Tighter t a b) : TighterEq t a b := by
  induction h with
  | base hmem => exact TighterEq.step hmem TighterEq.refl
  | step hmem _ ih => exact TighterEq.step hmem ih

theorem TighterEq.toTighterOrEq {Op : Type} {t : Op → List Op} {a b : Op}
    (h : TighterEq t a b) : a = b ∨ Tighter t a b := by
  induction h with
  | refl => exact Or.inl rfl
  | step hmem _ ih =>
      cases ih with
      | inl hEq => exact Or.inr (hEq ▸ Tighter.base hmem)
      | inr hT  => exact Or.inr (Tighter.step hmem hT)

theorem Tighter.ofMemTighterEq {Op : Type} {t : Op → List Op} {a b o : Op}
    (hmem : b ∈ t a) (h : TighterEq t b o) : Tighter t a o := by
  cases h.toTighterOrEq with
  | inl hEq => exact hEq ▸ Tighter.base hmem
  | inr hT  => exact Tighter.step hmem hT

/-! ## Entries and grammars -/

/-- One entry (one "syntactic category"): its operators, the precedence DAG with an explicit numeric
`rank`, and the variable-token recognizer. -/
structure Entry (Tok Ent : Type) where
  Op : Type
  operator : Op → Operator Tok Ent
  /-- Every operator, enumerated (needed to compute FIRST/FOLLOW). -/
  ops : List Op
  ops_complete : ∀ o : Op, o ∈ ops
  /-- The source (loosest) operators — where parsing an expression of this entry begins. -/
  loosest : List Op
  /-- Immediate-successor precedence graph: `tighter o` are the operators one step tighter. -/
  tighter : Op → List Op
  /-- Explicit precedence rank. Tighter ⇒ strictly lower rank (`rank_tighter`), and every rank is
  strictly below `topRank` (`rank_lt_topRank`), the rank of the loosest level. -/
  rank : Op → Nat
  topRank : Nat
  rank_tighter : ∀ a b : Op, b ∈ tighter a → rank b < rank a
  rank_lt_topRank : ∀ o : Op, rank o < topRank
  /-- Recognizes variable (identifier) leaf tokens. -/
  isVar : Tok → Bool

/-- A grammar: a family of entries over a shared token alphabet. -/
structure Grammar (Tok : Type) where
  Ent : Type
  entry : Ent → Entry Tok Ent

end LambdaLab.IsoParser.Mixfix
