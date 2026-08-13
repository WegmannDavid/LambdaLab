import LambdaLab.Parser.IsoParser.Combinators

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

namespace LambdaLab.Parser.IsoParser.Mixfix

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
  /-- **Distinct operators have distinct leading tokens.** Lexical determinism for the token the
  parser dispatches on. Without it a grammar can hold two operators with the *same* notation, and
  then two distinct trees flatten alike — a deterministic parser answers one and the round-trip
  law fails at the other. (A machine-checked counterexample lived in `Mixfix/Ambiguity.lean` at
  commit `ef5bd1b`, before this field made such a grammar unrepresentable.)

  Note this constrains only *lexical* distinctness. Heads may still be precedence-incomparable —
  `a + b * c` with `+`/`*` unrelated simply fails to parse ("add parentheses"), which is sound. -/
  headsDistinct : ∀ o₁ o₂ : Op, (operator o₁).headTok?.isSome = true →
    (operator o₁).headTok? = (operator o₂).headTok? → o₁ = o₂
  /-- **At most one operator is juxtaposition.** `headsDistinct`'s `isSome` guard deliberately
  exempts `juxt`, which has no leading token — so without this field two distinct juxtaposition
  operators are representable, and being tokenless they are *indistinguishable in the token
  stream*: they give distinct trees with equal flattenings, i.e. an ambiguous grammar.

  Nothing already proved is unsound without it (`mixfix` takes `Unambiguous` as a hypothesis, and
  such a grammar simply cannot supply one), but unambiguity cannot be *derived* without it —
  `not_continuesAt_tighter_juxt` needs exactly this to know that a juxt strictly tighter than `j`
  must be `j`. Vacuous for a grammar with no juxtaposition, and `decide`-discharged otherwise. -/
  juxtUnique : ∀ o₁ o₂ : Op, operator o₁ = Operator.juxt → operator o₂ = Operator.juxt → o₁ = o₂
  /-- **No operator name part is a variable token** — the variable half of the same lexical
  determinism, so a token cannot be read as both a leaf and (part of) an operator. Ranges over the
  operator's finite name-part list, so a concrete grammar discharges it by `decide`. -/
  varDisjoint : ∀ (o : Op) (t : Tok), t ∈ (operator o).nameTokens → isVar t = false

/-- A grammar: a family of entries over a shared token alphabet. -/
structure Grammar (Tok : Type) where
  Ent : Type
  entry : Ent → Entry Tok Ent
  /-- **Interior seams terminate** — `headsDistinct`'s analogue for the tokens that are not
  leading. In `( _ )` the hole is parsed by entry `e'`, and the only thing that can stop that
  parser is the token following the hole (here `)`), so that token must lie in **`e'`'s** FOLLOW:
  neither an `e'`-variable nor the head of any `e'`-operator.

  This lives on `Grammar`, not `Entry`, and it has to: a hole's entry is in general a *different*
  entry from the operator's host (that is what `Notation.cons` carrying an `Ent` is for), and an
  `Entry` cannot see its siblings. A two-entry grammar — exactly what a `Language` is, with types
  and terms — can satisfy every `Entry` field and still break the law.

  Without it the round-trip law is **false**: if `)` heads an operator of the hole's entry then
  `follow e' ")" = false`, the greedy parser runs past the `)`, and the printed tree does not
  parse back. Ranges over the operator's finite seam list, so `decide` discharges it. -/
  interiorTerminates : ∀ (e : Ent) (o : (entry e).Op) (e' : Ent) (t : Tok),
    (e', t) ∈ ((entry e).operator o).holeFollowers →
      (entry e').isVar t = false ∧
        ∀ o' : (entry e').Op, ((entry e').operator o').headTok? ≠ some t

/-! ## Decidability of the precedence relations

Reachability through `tighter`, decided by a **fuel-based** search (fuel = the rank, which
strictly decreases along `tighter`) — fuel rather than well-founded recursion so the kernel can
evaluate it, i.e. so grammar-shaped side conditions are dischargeable `by decide`. -/

/-- Fuel-bounded reachability: `a = b`, or a `tighter` step then recurse. -/
def teqFuel {Op : Type} [DecidableEq Op] (t : Op → List Op) : Nat → Op → Op → Bool
  | 0, a, b => a == b
  | n + 1, a, b => a == b || (t a).any fun c => teqFuel t n c b

theorem teqFuel_sound {Op : Type} [DecidableEq Op] {t : Op → List Op} :
    ∀ {n : Nat} {a b : Op}, teqFuel t n a b = true → TighterEq t a b := by
  intro n
  induction n with
  | zero =>
      intro a b h
      rw [teqFuel, beq_iff_eq] at h
      exact h ▸ .refl
  | succ n ih =>
      intro a b h
      rw [teqFuel, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
      rcases h with rfl | ⟨c, hc, hrec⟩
      · exact .refl
      · exact .step hc (ih hrec)

theorem teqFuel_complete {Ent : Type} (E : Entry Tok Ent) [DecidableEq E.Op] :
    ∀ {a b : E.Op}, TighterEq E.tighter a b →
      ∀ {n : Nat}, E.rank a ≤ n → teqFuel E.tighter n a b = true := by
  intro a b h
  induction h with
  | refl =>
      intro n _
      cases n <;> simp [teqFuel]
  | step hmem _ ih =>
      intro n hn
      cases n with
      | zero => exact absurd (E.rank_tighter _ _ hmem) (by omega)
      | succ n =>
          rw [teqFuel, Bool.or_eq_true, List.any_eq_true]
          exact Or.inr ⟨_, hmem, ih (by have := E.rank_tighter _ _ hmem; omega)⟩

instance {Ent : Type} (E : Entry Tok Ent) [DecidableEq E.Op] (a b : E.Op) :
    Decidable (TighterEq E.tighter a b) :=
  decidable_of_iff (teqFuel E.tighter (E.rank a) a b = true)
    ⟨teqFuel_sound, fun h => teqFuel_complete E h (Nat.le_refl _)⟩

theorem tighter_iff {Op : Type} {t : Op → List Op} {a b : Op} :
    Tighter t a b ↔ ∃ c ∈ t a, TighterEq t c b := by
  constructor
  · intro h
    cases h with
    | base hmem => exact ⟨b, hmem, .refl⟩
    | step hmem hrest => exact ⟨_, hmem, hrest.toTighterEq⟩
  · rintro ⟨c, hc, hrest⟩
    exact Tighter.ofMemTighterEq hc hrest

instance {Ent : Type} (E : Entry Tok Ent) [DecidableEq E.Op] (a b : E.Op) :
    Decidable (Tighter E.tighter a b) :=
  decidable_of_iff (∃ c ∈ E.tighter a, TighterEq E.tighter c b) tighter_iff.symm

end LambdaLab.Parser.IsoParser.Mixfix
