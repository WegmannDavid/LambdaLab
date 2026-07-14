import LambdaLab.Language1.Biparser
import LambdaLab.CBiparser.Mixfix.Complete

/-!
# A real plug-in language: arithmetic

Types are the three number sets `N`, `Z`, `R`. Terms are the **mixfix** arithmetic grammar —
parentheses, application by juxtaposition, `*` binding tighter than `+`.

This is the first `Language` whose term parser is a genuine recursive mixfix parser rather than a
single token, and it is what the whole `Language`/`IBip`/`Mixfix` stack was built to support. What
a language author has to supply is exactly:

* a `Grammar` (operators, precedence DAG, and the three lexical conditions — all by `decide`);
* the two adapters at the plug-in boundary (`weakenFollow` / `enlargeFirst`).

Everything else — commands, programs, the file parser, the printer, and the source-text round
trip — is **derived**.

## ⚠ The round-trip law here is CONDITIONAL

`Mixfix.ibiparser` demands `Unambiguous G`, and the only proof of it available
(`Mixfix.unambiguous`) still rests on the three open kernel lemmas in `Unambiguity.lean` plus
`parseExpr_exact`. So `arithLanguage`'s `ok` fields — and hence `fileParser_roundtrip` *for this
language* — currently depend on `sorryAx`.

The parser itself does **not**: `Unambiguous` is a `Prop`, so it is erased, and everything below
`#eval`s and runs. What this file demonstrates is that the plumbing fits end to end; what it does
*not* yet demonstrate is a closed proof. Discharging the four lemmas turns this file's laws
unconditional with no change to the file.
-/

namespace LambdaLab.Language1

open LambdaLab.CBiparser LambdaLab.CBiparser.Mixfix

/-! ## The grammar

Note the separator: `Language1.isSep`, **not** a grammar-local one. That is what makes the
grammar's `Token G.isSep` literally the vernacular's `Token`, so the two compose with no lift. -/

/-- A token literal of the vernacular's alphabet. -/
def tkA (s : String) (h : isToken isSep s = true := by decide) : Token := ⟨s, h⟩

/-- Operators: parentheses, application (juxtaposition), `_ * _`, `_ + _`. -/
inductive ASym | paren | app | times | plus
  deriving DecidableEq, Repr

/-- The tokens `isVar` must reject. The **vernacular keywords are in here** — that is the one
thing a grammar must do to plug into `Language1`. Without it `def` would be a perfectly good
variable and juxtaposition would swallow the next command's keyword. With it,
`follow () (tkA "def") = true` becomes *derivable*, which is exactly the seam `pTm` needs. -/
def aReserved : List Token :=
  [tkA "(", tkA ")", tkA "+", tkA "*", tkA "def", tkA ":", tkA ":="]

def aTighter : ASym → List ASym
  | .plus  => [.times]
  | .times => [.app]
  | .app   => [.paren]
  | .paren => []

def aRank : ASym → Nat
  | .paren => 0 | .app => 1 | .times => 2 | .plus => 3

theorem aTighter_wf : WellFounded (fun b a => b ∈ aTighter a) :=
  Subrelation.wf
    (r := fun x y => aRank x < aRank y)
    (fun {x y} (h : x ∈ aTighter y) => by cases x <;> cases y <;> simp_all [aTighter, aRank])
    (measure aRank).wf

def aOp : ASym → Operator isSep Unit
  | .paren => .closed (.cons (tkA "(") () (.last (tkA ")")))
  | .app   => .juxt
  | .times => .infxl (.last (tkA "*"))
  | .plus  => .infxl (.last (tkA "+"))

def aEntry : Entry isSep Unit where
  Op := ASym
  operator := aOp
  ops := [.paren, .app, .times, .plus]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.plus]
  tighter := aTighter
  tighter_wf := aTighter_wf
  isVar := fun t => decide (t ∉ aReserved)
  juxtUnique := fun o₁ o₂ h₁ h₂ => by cases o₁ <;> cases o₂ <;> simp_all [aOp]
  headsDistinct := by
    intro o₁ o₂ _ _; cases o₁ <;> cases o₂ <;>
      simp_all [aOp, Operator.headTok?, Operator.nameTokens, Notation.toTokens, tkA]
  varDisjoint := by intro o; cases o <;> decide

/-- The grammar. Its separator is the vernacular's. -/
def aGrammar : Grammar where
  Ent := Unit
  isSep := isSep
  sepWitness := ⟨' ', by decide⟩
  entry := fun _ => aEntry
  interiorTerminates := by
    intro _ o _ t h
    cases o <;>
      simp [aEntry, aOp, Operator.holeFollowers, Notation.holeFollowers, Notation.firstTok] at h
    subst h
    exact ⟨by decide, by intro o'; cases o' <;> decide⟩

/-! ## Types: the three number sets -/

/-- `N`, `Z`, `R`. -/
def isNumSet (t : Token) : Bool :=
  t.val == "N" || t.val == "Z" || t.val == "R"

abbrev NumSet := { t : Token // isNumSet t = true }

/-! ## The language

The only real content is the two adapters, and the fact that `follow () (tkA "def") = true` —
which `decide` proves, because `isVar` rejects `def`. -/

/-- The term parser stops at a command boundary. **Derived**, not declared. -/
theorem follow_def : Mixfix.follow (G := aGrammar) () (tkA "def") = true := by decide

def arithLanguage : Language where
  Tm := Expr aGrammar () .loosest
  Ty := NumSet

  -- types: a single token drawn from {N, Z, R}. FOLLOW is ⊤, so `:=` may follow.
  pTy := ((iSat isNumSet).weakenFollow (fun _ _ => rfl)).enlargeFirst (fun _ hf => by simp at hf)

  -- terms: the mixfix parser. Its FIRST is already `anyTok`; its FOLLOW is the grammar's,
  -- narrowed to `def` -- which is sound exactly because `def` is in it (`follow_def`).
  pTm :=
    (Mixfix.ibiparser (Mixfix.unambiguous aGrammar) () .loosest).weakenFollow
      (by
        intro t ht
        have : t = kwDef := of_decide_eq_true ht
        subst this
        exact follow_def)

end LambdaLab.Language1
