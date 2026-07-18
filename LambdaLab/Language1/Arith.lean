import LambdaLab.Language1.Biparser
import LambdaLab.IsoParser.Mixfix.Biparser

/-!
# A real plug-in language: arithmetic (on the independent `IsoParser` mixfix)

Types are the three number sets `N`, `Z`, `R`. Terms are the **mixfix** arithmetic grammar —
parentheses, application by juxtaposition, `*` binding tighter than `+` — now built on the
self-contained `IsoParser.Mixfix` stack (abstract token alphabet, explicit `rank`), with no
`CBiparser` dependency.

A language author supplies exactly a `Grammar` (operators, precedence with explicit `rank`) plus the
two boundary adapters. The new grammar is *lighter* than the CBiparser one: no `tighter_wf`,
`juxtUnique`, `headsDistinct`, or `interiorTerminates` — the parser needs only the precedence rank.

## ⚠ The round-trip law here is CONDITIONAL

`Mixfix.mixfix`'s `parse_print` (the greedy left-associative round-trip) is still an open `sorry`, so
`arithLanguage`'s round-trip laws depend on `sorryAx`. The parser itself does not: it `#eval`s and
runs. Discharging that one lemma turns these laws unconditional with no change here.
-/

namespace LambdaLab.Language1

open LambdaLab.IsoParser LambdaLab.IsoParser.Mixfix

/-- A token literal of the vernacular's alphabet. -/
def tkA (s : String) (h : CBiparser.isToken isSep s = true := by decide) : Token := ⟨s, h⟩

/-- Operators: parentheses, application (juxtaposition), `_ * _`, `_ + _`. -/
inductive ASym | paren | app | times | plus
  deriving DecidableEq, Repr

/-- The tokens `isVar` must reject — including the vernacular keywords, so `def` is not a variable. -/
def aReserved : List Token :=
  [tkA "(", tkA ")", tkA "+", tkA "*", tkA "def", tkA ":", tkA ":="]

def aTighter : ASym → List ASym
  | .plus  => [.times]
  | .times => [.app]
  | .app   => [.paren]
  | .paren => []

def aRank : ASym → Nat
  | .paren => 0 | .app => 1 | .times => 2 | .plus => 3

def aOp : ASym → Operator Token Unit
  | .paren => .closed (.cons (tkA "(") () (.last (tkA ")")))
  | .app   => .juxt
  | .times => .infxl (.last (tkA "*"))
  | .plus  => .infxl (.last (tkA "+"))

def aEntry : Entry Token Unit where
  Op := ASym
  operator := aOp
  ops := [.paren, .app, .times, .plus]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.plus]
  tighter := aTighter
  rank := aRank
  topRank := 4
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all [aTighter, aRank]
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := fun t => decide (t ∉ aReserved)

/-- The grammar — much lighter than the CBiparser one: precedence `rank` and nothing else. -/
def aGrammar : Grammar Token where
  Ent := Unit
  entry := fun _ => aEntry

/-! ## Types: the three number sets -/

/-- `N`, `Z`, `R`. -/
def isNumSet (t : Token) : Bool :=
  t.val == "N" || t.val == "Z" || t.val == "R"

abbrev NumSet := { t : Token // isNumSet t = true }

/-! ## The language -/

/-- The term parser stops at a command boundary. **Derived**, not declared. -/
theorem follow_def : follow (G := aGrammar) () (tkA "def") = true := by decide

def arithLanguage : Language where
  Tm := Expr aGrammar () .loosest
  Ty := NumSet

  -- types: a single token drawn from {N, Z, R}. FOLLOW is ⊤, so `:=` may follow.
  pTy := ((sat isNumSet).weakenFollow (fun _ _ => rfl)).enlargeFirst (fun _ hf => by simp at hf)

  -- terms: the mixfix parser. Its FIRST is already `anyTok`; its FOLLOW is the grammar's,
  -- narrowed to `def` — sound exactly because `def` is in it (`follow_def`).
  pTm :=
    (mixfix (G := aGrammar) () .loosest).weakenFollow
      (by
        intro t ht
        have : t = kwDef := of_decide_eq_true ht
        subst this
        exact follow_def)

end LambdaLab.Language1
