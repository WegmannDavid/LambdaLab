import LambdaLab.ParserExperimental1.Biparser.Combinators

/-!
# A generic, data-driven mixfix grammar — combinator weak-biparser

`Telescope.lean` verified *one* hardcoded grammar (parens + right-assoc `+`) from
combinators. This directory generalizes it to a **data-driven** grammar and grows toward
the full functionality of `Parser/Mixfix` (all fixities, notations, precedence), keeping
the weak target (`parse_complete` only) and the combinator style: every token/gap leaf is
a combinator, only the recursive skeleton is hand-rolled.

File layout:
* `Basic`    — the grammar data and the precedence-indexed `Tree`.
* `Leaves`   — the combinator leaves (`varTok`/`lpGap`/`gapRp`/`gapOpGap`, …).
* `Render`   — the telescope `render` (built from the leaves).
* `Parse`    — the char-level parser.
* `Complete` — `parse_complete` and the assembled `Biparser`.

This file: the grammar and the tree. Operators are a precedence-ordered table of
right-associative infix characters; brackets `(`/`)` and the space separator are built in.
The tree is **precedence-indexed** (`Tree G p` binds at least as tightly as level `p`), a
plain-`Nat` analogue of `Parser/Mixfix`'s `Level`-indexed `Expr G`, so `render` never has
to *decide* where to parenthesize.
-/

namespace LambdaLab.ParserExperimental1.Mixfix

open LambdaLab.ParserExperimental1

/-- The fixity of an operator. `infixr` is a right-associative binary infix `a ⊙ b`;
`infixl` is left-associative `a ⊙ b ⊙ c = (a ⊙ b) ⊙ c`; `prefix` is a unary leading
operator `⊙ a`; `postfix` is a unary trailing operator `a ⊙` (non-chaining — the operand
is strictly tighter, matching `Parser/Mixfix`). (Juxtaposition is added separately, being
tokenless.) -/
inductive Fixity where
  | infixr
  | infixl
  | prefix
  | postfix
deriving DecidableEq

/-- A generic grammar: `ops[k] = (name, fx)` is the operator whose **multi-character
name** is `name` (a nonempty char list, by `hopsNE`) at precedence level `k` (higher index
= binds tighter) with fixity `fx`. `isSep` marks separator characters (a `sepWitness`
witnesses the alphabet is nonempty); `isVar` recognizes variable words (char lists). `juxt`
enables tokenless **juxtaposition** (application by adjacency) — a tightest-binding,
left-associative operator at precedence `ops.length`. Brackets `(`/`)` are built in and
assumed disjoint from `isSep`, `ops` names, and `isVar`. -/
structure Grammar where
  isSep : Char → Bool
  sepWitness : {c : Char // isSep c = true}
  ops : List (List Char × Fixity)
  hopsNE : ∀ x ∈ ops, x.1 ≠ []
  isVar : List Char → Bool
  juxt : Bool := false

/-- The operator name (char list) at precedence `k`. -/
def Grammar.opName (G : Grammar) (k : Nat) (hk : k < G.ops.length) : List Char := (G.ops[k]'hk).1
/-- The fixity at precedence `k`. -/
def Grammar.opFixity (G : Grammar) (k : Nat) (hk : k < G.ops.length) : Fixity := (G.ops[k]'hk).2
/-- Operator names are nonempty. -/
theorem Grammar.opName_ne (G : Grammar) (k : Nat) (hk : k < G.ops.length) :
    G.opName k hk ≠ [] := G.hopsNE _ (List.getElem_mem hk)

/-- A **variable token**: a nonempty, separator-free char run that `isVar` accepts. -/
structure VarTok (G : Grammar) where
  chars : List Char
  hne : chars ≠ []
  hsf : ∀ c ∈ chars, G.isSep c = false
  hv : G.isVar chars = true

/-- Build a `VarTok` with the three well-formedness conditions discharged by `decide`. -/
def vtok {G : Grammar} (chars : List Char) (hne : chars ≠ [] := by decide)
    (hsf : ∀ c ∈ chars, G.isSep c = false := by decide) (hv : G.isVar chars = true := by decide) :
    VarTok G := ⟨chars, hne, hsf, hv⟩

/-! A precedence-indexed parse tree: an inhabitant of `Tree G p` is an expression whose
top operator binds **at least as tightly as** level `p`. A `var`/`paren` is an atom
(tighter than everything, so valid at any `p`); an operator node at precedence `k` is
valid at levels `p ≤ k` and carries a proof pinning it to its declared fixity.

* `op` — right-assoc infix: left operand one level tighter (`k+1`), right chains (`k`).
* `opl` — left-assoc infix: a `head` operand, a mandatory `chainHead` operand, and a
  (possibly empty) `TreeChain` of further operands — all one level tighter. The chain *is*
  the left-associated fold `((head ⊙ chainHead) ⊙ c₀) ⊙ …`, so no weakening is needed. The
  separate `chainHead` makes the chain nonempty (≥1 operator) by construction.
* `pre` — prefix: a single operand one level tighter (`k+1`).

`TreeChain G n` is a plain cons-list of `Tree G n`, defined mutually (a nested `List
(Tree G (k+1))` can't appear in `Tree` since its parameter mentions the local `k`). -/
mutual
inductive Tree (G : Grammar) : Nat → Type where
  | var   {p : Nat} : VarTok G → Tree G p
  | paren {p : Nat} : Tree G 0 → Tree G p
  | op    {p : Nat} (k : Nat) (hk : k < G.ops.length) (hfix : G.opFixity k hk = .infixr)
            (hp : p ≤ k) : Tree G (k + 1) → Tree G k → Tree G p
  | opl   {p : Nat} (k : Nat) (hk : k < G.ops.length) (hfix : G.opFixity k hk = .infixl)
            (hp : p ≤ k) : Tree G (k + 1) → Tree G (k + 1) → TreeChain G (k + 1) → Tree G p
  | pre   {p : Nat} (k : Nat) (hk : k < G.ops.length) (hfix : G.opFixity k hk = .prefix)
            (hp : p ≤ k) : Tree G (k + 1) → Tree G p
  | post  {p : Nat} (k : Nat) (hk : k < G.ops.length) (hfix : G.opFixity k hk = .postfix)
            (hp : p ≤ k) : Tree G (k + 1) → Tree G p
  /-- Juxtaposition (tokenless, left-assoc, tightest): like `opl` at precedence
  `G.ops.length` with empty operator — a head operand, a mandatory `chainHead`, and a
  chain of further operands, all at level `G.ops.length + 1` (atoms). -/
  | jux   {p : Nat} (hj : G.juxt = true) (hp : p ≤ G.ops.length) :
            Tree G (G.ops.length + 1) → Tree G (G.ops.length + 1) →
            TreeChain G (G.ops.length + 1) → Tree G p
inductive TreeChain (G : Grammar) : Nat → Type where
  | nil  {n : Nat} : TreeChain G n
  | cons {n : Nat} : Tree G n → TreeChain G n → TreeChain G n
end

/-! ### A sample grammar for `#eval` sanity checks. -/

/-- The common lexis for the samples: space separator, lowercase-letter variables. -/
def spaceSep : Char → Bool := fun c => c == ' '

/-- `+` (0, infix), `*` (1, infix), `-` (2, prefix), `!` (3, postfix); lowercase = vars. -/
def sample : Grammar where
  isSep := spaceSep
  sepWitness := ⟨' ', by decide⟩
  ops := [(['+'], .infixr), (['*'], .infixr), (['-'], .prefix), (['!'], .postfix)]
  hopsNE := by decide
  isVar := fun s => !s.isEmpty && s.all (fun c => 'a' ≤ c && c ≤ 'z')

/-- `a + b * c`. -/
def sampleTree : Tree sample 0 :=
  .op 0 (by decide) (by decide) (by decide)
    (.var (vtok ['a']))
    (.op 1 (by decide) (by decide) (by decide) (.var (vtok ['b'])) (.var (vtok ['c'])))

/-- `- a + b` (prefix `-` binds tighter than `+`): `(- a) + b`. -/
def sampleTree2 : Tree sample 0 :=
  .op 0 (by decide) (by decide) (by decide)
    (.pre 2 (by decide) (by decide) (by decide) (.var (vtok ['a'])))
    (.var (vtok ['b']))

/-- `a ! + b` (postfix `!` binds tighter than `+`): `(a !) + b`. -/
def sampleTree3 : Tree sample 0 :=
  .op 0 (by decide) (by decide) (by decide)
    (.post 3 (by decide) (by decide) (by decide) (.var (vtok ['a'])))
    (.var (vtok ['b']))

/-- A left-associative grammar with a **multi-character** operator name `+.` (prec 0). -/
def sampleL : Grammar where
  isSep := spaceSep
  sepWitness := ⟨' ', by decide⟩
  ops := [(['+', '.'], .infixl)]
  hopsNE := by decide
  isVar := fun s => !s.isEmpty && s.all (fun c => 'a' ≤ c && c ≤ 'z')

/-- `a +. b +. c` = `(a +. b) +. c` (left-assoc): head `a`, chain `b`, `c`. -/
def sampleLTree : Tree sampleL 0 :=
  .opl 0 (by decide) (by decide) (by decide)
    (.var (vtok ['a'])) (.var (vtok ['b'])) (.cons (.var (vtok ['c'])) .nil)

/-- A grammar with juxtaposition: `+` (prec 0, right-assoc) and application. -/
def sampleJ : Grammar where
  isSep := spaceSep
  sepWitness := ⟨' ', by decide⟩
  ops := [(['+'], .infixr)]
  hopsNE := by decide
  isVar := fun s => !s.isEmpty && s.all (fun c => 'a' ≤ c && c ≤ 'z')
  juxt := true

/-- `f x y` = `(f x) y` (application, left-assoc): head `f`, chain `x`, `y`. -/
def sampleJTree : Tree sampleJ 0 :=
  .jux (by decide) (by decide)
    (.var (vtok ['f'])) (.var (vtok ['x'])) (.cons (.var (vtok ['y'])) .nil)

end LambdaLab.ParserExperimental1.Mixfix
