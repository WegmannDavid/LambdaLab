import LambdaLab.Language1.Biparser
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.Truncation
import LambdaLab.Parser.Truncation.Mixfix
import LambdaLab.Parser.IsoParser.Adapters

/-!
# Arithmetic — the running example language

The mixfix arithmetic vernacular as a `Language1.Language`: two mixfix grammars (terms and
types), a truncated term AST via the generic `Rules` bundle, and the plug-in instance — from
which the framework derives the command parser, the file parser, the round-trip law, the `Abs`
morphism, and the `List Char ⇝ Program` pipeline (`Main.lean` runs it).

Historical layers this file once carried (a combinator-only grammar and a hand-proved recursive
parser — the unconditional round-trip proof whose mixfix analogue is still the one open `sorry`)
were superseded by the `Parser/` stack and live in git history; the combinator idioms are shown
in `Parser/IsoParser/Example.lean`.
-/

namespace LambdaLab.Arith

/-! ## The language: a real plug-in vernacular on the `IsoParser` mixfix

Both sides come from the mixfix engine, as trees. Terms are the arithmetic grammar —
parentheses, application by juxtaposition, `*` binding tighter than `+`. Types are their own
little grammar — atoms `N`, `Z`, `R`, a right-associative arrow `_ → _`, parentheses. Built on
the self-contained `IsoParser.Mixfix` stack (abstract token alphabet, explicit `rank`), with no
`CBiparser` dependency.

A language author supplies exactly a `Grammar` (operators, precedence with explicit `rank`) plus the
two boundary adapters. The grammar is *lighter* than the CBiparser one: no `tighter_wf`,
`juxtUnique`, `headsDistinct`, or `interiorTerminates` — the parser needs only the precedence rank.

### ⚠ The round-trip law here is CONDITIONAL

`Mixfix.mixfix`'s `ok` (the greedy left-associative round-trip) is still an open `sorry`, so
`arithLanguage`'s round-trip laws depend on `sorryAx`. The parser itself does not: it `#eval`s and
runs. Discharging that one lemma turns these laws unconditional with no change here.

Note the contrast with `Recursive` above: that section proves exactly this shape of greedy
left-associative reconstruction by hand, for a fixed grammar.
-/

open LambdaLab.Parser.IsoParser LambdaLab.Parser.IsoParser.Mixfix LambdaLab.Language1

/-- A token literal of the vernacular's alphabet. -/
def tkA (s : String) (h : isToken isSep s = true := by decide) : Token := ⟨s, h⟩

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

/-! ### Types: their own mixfix grammar

Types are trees too: atoms `N`, `Z`, `R`, a right-associative function arrow `_ → _`, and
parentheses. Same recipe as the term grammar, so `Ty` is an `Expr` and `pTy` is `mixfix` — both
sides of the language now come from the one engine. -/

/-- The type atoms: `N`, `Z`, `R` — the only tokens the type grammar treats as variables, so
keywords and operators are excluded for free. -/
def isNumSet (t : Token) : Bool :=
  t.val == "N" || t.val == "Z" || t.val == "R"

/-- Type operators: parentheses and the function arrow. -/
inductive TSym | paren | arrow
  deriving DecidableEq, Repr

def tTighter : TSym → List TSym
  | .arrow => [.paren]
  | .paren => []

def tRank : TSym → Nat
  | .paren => 0 | .arrow => 1

def tOp : TSym → Operator Token Unit
  | .paren => .closed (.cons (tkA "(") () (.last (tkA ")")))
  | .arrow => .infxr (.last (tkA "→"))

def tEntry : Entry Token Unit where
  Op := TSym
  operator := tOp
  ops := [.paren, .arrow]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.arrow]
  tighter := tTighter
  rank := tRank
  topRank := 2
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all [tTighter, tRank]
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := isNumSet

def tyGrammar : Grammar Token where
  Ent := Unit
  entry := fun _ => tEntry

/-! ### The truncated term AST — via the generic `Rules` bundle

The mixfix parser is an iso parser: its `Expr` trees still contain the parentheses. The type the
user actually wants has none. Everything below is *instructions*, not machinery: the `Rules`
bundle (`Parser/Truncation/Mixfix.lean`) states how each operator maps into `ATm` and how an
`ATm` canonically spells back; the fold, the paren-inserting injection, and the section theorem
are all derived generically. Every law here is `rfl`, `decide`, or `simp`-shaped. -/

section Truncation
open LambdaLab.Parser.Truncation.Mixfix

/-- Arithmetic terms, parens-free: what `Expr aGrammar` is *about*. -/
inductive ATm where
  | var : (t : Token) → aEntry.isVar t = true → ATm
  | app : ATm → ATm → ATm
  | mul : ATm → ATm → ATm
  | add : ATm → ATm → ATm

/-- TC will not unfold `aGrammar.entry e` to `aEntry` (nor `.Op` to `ASym`) by itself, so hand
it the instances in the exact projected forms the generic machinery asks for. -/
instance : DecidableEq aEntry.Op := inferInstanceAs (DecidableEq ASym)
instance : ∀ e : aGrammar.Ent, DecidableEq (aGrammar.entry e).Op :=
  fun _ => inferInstanceAs (DecidableEq ASym)

/-- A structural size (constructor counts one) — `omega`-friendly, unlike the opaque `sizeOf`. -/
def ATm.size : ATm → Nat
  | .var _ _ => 1
  | .app a b => a.size + b.size + 1
  | .mul a b => a.size + b.size + 1
  | .add a b => a.size + b.size + 1

/-- The truncation instructions: one clause per operator each way, plus the paren designation
and the bookkeeping laws — all discharged by `rfl`/`decide`/`simp`. -/
def aRules : Rules aGrammar (fun _ => ATm) where
  var t h := .var t h
  op o vs :=
    match o, vs with
    | .paren, (e, _)    => e
    | .app,   (a, b, _) => .app a b
    | .times, (a, b, _) => .mul a b
    | .plus,  (a, b, _) => .add a b
  dest x :=
    match x with
    | .var t h => .var t h
    | .app a b => .node .app (a, b, PUnit.unit)
    | .mul a b => .node .times (a, b, PUnit.unit)
    | .add a b => .node .plus (a, b, PUnit.unit)
  parenOp _ := .paren
  lp _ := tkA "("
  rp _ := tkA ")"
  paren_eq _ := rfl
  holesOk := by rintro ⟨⟩ o; cases o <;> decide
  topOk := by rintro ⟨⟩ o; cases o <;> decide
  alg_dest := by rintro _ (⟨t, h⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩) <;> rfl
  op_paren _ := rfl
  size := ATm.size
  dest_size := by
    rintro _ (⟨t, h⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩)
    · trivial
    all_goals exact ⟨by simp +arith [ATm.size], by simp +arith [ATm.size], trivial⟩

end Truncation

/-! ### The language -/

/-- The term parser stops at a command boundary. **Derived**, not declared. -/
theorem follow_def : follow (G := aGrammar) () (tkA "def") = true := by decide

/-- The type parser stops at the assignment. **Derived**, not declared. -/
theorem follow_assign : follow (G := tyGrammar) () (tkA ":=") = true := by decide

def arithLanguage : Language where
  Tm := ATm
  Ty := Expr tyGrammar () .loosest

  -- Types stay lossless (canonical-form only): trivial annotation via `toLossyParserUnit`.
  -- Terms are TRUNCATED: the value is the parens-free `ATm`, and the annotation over `x` is
  -- the fiber of `truncTm` — every tree spelling `x` — so `((((a))))` parses to `a` and any
  -- spelling round-trips.
  AnnTy := fun _ => Unit
  AnnTm := fun x => { t : Expr aGrammar () .loosest //
    LambdaLab.Parser.Truncation.Mixfix.truncExpr aRules t = x }

  -- types: the mixfix parser at the type grammar; FOLLOW narrowed to `:=` — sound exactly
  -- because `:=` is in it (`follow_assign`).
  pTy :=
    ((mixfix (G := tyGrammar) () .loosest).weakenFollow
      (by
        intro t ht
        have h : t = kwAssign := ht
        subst h
        exact follow_assign)).toLossyParserUnit (fun _ => rfl)

  -- terms: the mixfix parser chained with the truncation. FIRST is already `anyTok`; FOLLOW is
  -- the grammar's, narrowed to `def` — sound exactly because `def` is in it (`follow_def`).
  pTm :=
    ((mixfix (G := aGrammar) () .loosest).weakenFollow
      (by
        intro t ht
        have h : t = kwDef := ht
        subst h
        exact follow_def) |> aRules.truncateParser) (fun _ => rfl)

end LambdaLab.Arith
