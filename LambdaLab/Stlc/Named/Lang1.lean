import LambdaLab.Stlc.Named.Basic
import LambdaLab.Language1.Biparser
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Parser.Truncation.Mixfix

/-!
# STLC as a `Language1.Language` — derived from the mixfix engine

The lambda-calculus instance, built exactly like `Arith.lean`: grammars in, everything else
derived. The one genuinely new feature exercised here is a **multi-entry grammar**: the binder
`x` in `λ x . e` must parse as a single variable, not a term, so it is a cross-entry hole
into a second entry whose only operator is a paren (so `λ ( x ) . e` is legal surface
syntax — the harmless price of the generic `Rules` bundle wanting a paren per entry).

* terms — `paren`/`app` (juxtaposition)/`lam`, truncated by a `Rules` bundle into the
  parens-free surface AST `STm`. Inherited `prefx` limitation: a lambda body cannot be a *bare*
  lambda — write `λ x . ( λ y . e )`.
* types — `⋆`, right-associative `→`, parens; kept as trees (`Unit` annotation), as in Arith.

`STm` deliberately carries **no type annotations** (`Rules.alg_dest` — destruct-then-rebuild is
the identity — would force every annotation to a fixed value anyway). The bridge to the typed
`Stlc.Named.Term` is `STm.toTerm`, which annotates every binder with `Ty.mvar 0` for now; making
those mvars distinct (the old `Syntax/Truncate.lean` counter) is the elaborator boundary's job,
deferred.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Parser.IsoParser LambdaLab.Parser.IsoParser.Mixfix LambdaLab.Language1
open LambdaLab.Parser.Truncation.Mixfix

/-- A token literal of the vernacular's alphabet. -/
def tkS (s : String) (h : isToken isSep s = true := by decide) : Language1.Token := ⟨s, h⟩

/-- Tokens no variable may be: grammar name-parts and vernacular keywords. -/
def sReserved : List Language1.Token :=
  [tkS "(", tkS ")", tkS "λ", tkS ".", tkS "def", tkS ":", tkS ":="]

def isVarTok (t : Language1.Token) : Bool := decide (t ∉ sReserved)

/-! ## The term grammar: two entries -/

/-- The two syntactic categories: terms, and the binder sub-language. -/
inductive SEnt | tm | var
  deriving DecidableEq, Repr

/-- Term operators. -/
inductive SSym | paren | app | lam
  deriving DecidableEq, Repr

/-- Binder-entry operators: only grouping. -/
inductive BSym | paren
  deriving DecidableEq, Repr

def tmEntry : Entry Language1.Token SEnt where
  Op := SSym
  operator
    | .paren => .closed (.cons (tkS "(") .tm (.last (tkS ")")))
    | .app   => .juxt
    | .lam   => .prefx (.cons (tkS "λ") .var (.last (tkS ".")))
  ops := [.paren, .app, .lam]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.lam]
  tighter
    | .lam   => [.app]
    | .app   => [.paren]
    | .paren => []
  rank
    | .paren => 0 | .app => 1 | .lam => 2
  topRank := 3
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := isVarTok

def varEntry : Entry Language1.Token SEnt where
  Op := BSym
  operator
    | .paren => .closed (.cons (tkS "(") .var (.last (tkS ")")))
  ops := [.paren]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.paren]
  tighter | .paren => []
  rank | .paren => 0
  topRank := 1
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := isVarTok

def stlcGrammar : Grammar Language1.Token where
  Ent := SEnt
  entry | .tm => tmEntry | .var => varEntry

instance : DecidableEq tmEntry.Op := inferInstanceAs (DecidableEq SSym)
instance : DecidableEq varEntry.Op := inferInstanceAs (DecidableEq BSym)
instance : ∀ e : stlcGrammar.Ent, DecidableEq (stlcGrammar.entry e).Op
  | .tm => inferInstanceAs (DecidableEq SSym)
  | .var => inferInstanceAs (DecidableEq BSym)

/-! ## The surface AST and the truncation rules -/

/-- A binder name. -/
abbrev VName := { t : Language1.Token // isVarTok t = true }

/-- Surface terms, parens-free and annotation-free. -/
inductive STm where
  | var : (t : Language1.Token) → isVarTok t = true → STm
  | app : STm → STm → STm
  | lam : VName → STm → STm

def STm.size : STm → Nat
  | .var _ _ => 1
  | .app f a => f.size + a.size + 1
  | .lam _ b => b.size + 2

/-- The bridge to the typed calculus: every binder annotated `Ty.mvar 0` (all-zero for now;
distinct mvars are the elaborator boundary's job). -/
def STm.toTerm : STm → Term
  | .var t _ => .var t.val
  | .app f a => .app f.toTerm a.toTerm
  | .lam x b => .lam x.1.val (Ty.mvar 0) b.toTerm

/-- Target of the truncation, per entry. -/
def CS : SEnt → Type
  | .tm => STm
  | .var => VName

/-- The truncation instructions: `( e ) ↦ e` in both entries, `f a ↦ app`, `λ x . b ↦ lam`. -/
def sRules : Rules stlcGrammar CS where
  var {e} t h :=
    match e, h with
    | .tm, h => STm.var t h
    | .var, h => ⟨t, h⟩
  op {e} o vs :=
    match e, o, vs with
    | .tm, .paren, (t, _)    => t
    | .tm, .app,   (f, a, _) => .app f a
    | .tm, .lam,   (x, b, _) => .lam x b
    | .var, .paren, (x, _)   => x
  dest {e} x :=
    match e, x with
    | .tm, STm.var t h => .var t h
    | .tm, STm.app f a => .node .app (f, a, PUnit.unit)
    | .tm, STm.lam x b => .node .lam (x, b, PUnit.unit)
    | .var, x => .var x.1 x.2
  parenOp | .tm => SSym.paren | .var => BSym.paren
  lp _ := tkS "("
  rp _ := tkS ")"
  paren_eq | .tm => rfl | .var => rfl
  holesOk := by intro e o; cases e <;> cases o <;> decide
  topOk := by intro e o; cases e <;> cases o <;> decide
  alg_dest := by
    intro e x
    cases e
    · cases x <;> rfl
    · rfl
  op_paren := by intro e y; cases e <;> rfl
  size {e} :=
    match e with
    | .tm => STm.size
    | .var => fun _ => 1
  dest_size := by
    intro e x
    cases e
    · cases x with
      | var t h => trivial
      | app f a => exact ⟨by simp +arith [STm.size], by simp +arith [STm.size], trivial⟩
      | lam x b => exact ⟨by simp +arith [STm.size], by simp +arith [STm.size], trivial⟩
    · trivial

/-! ## The type grammar: `⋆`, right-associative `→`, parens -/

def isTyAtom (t : Language1.Token) : Bool := t.val == "⋆"

inductive TySym | paren | arrow
  deriving DecidableEq, Repr

def styEntry : Entry Language1.Token Unit where
  Op := TySym
  operator
    | .paren => .closed (.cons (tkS "(") () (.last (tkS ")")))
    | .arrow => .infxr (.last (tkS "→"))
  ops := [.paren, .arrow]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.arrow]
  tighter
    | .arrow => [.paren]
    | .paren => []
  rank | .paren => 0 | .arrow => 1
  topRank := 2
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := isTyAtom

def styGrammar : Grammar Language1.Token where
  Ent := Unit
  entry := fun _ => styEntry

/-! ## The language -/

/-- The term parser stops at a command boundary. **Derived**, not declared. -/
theorem sFollow_def : follow (G := stlcGrammar) SEnt.tm (tkS "def") = true := by decide

/-- The type parser stops at the assignment. **Derived**, not declared. -/
theorem tyFollow_assign : follow (G := styGrammar) () (tkS ":=") = true := by decide

def stlcLanguage : Language where
  Tm := STm
  Ty := Expr styGrammar () .loosest

  AnnTy := fun _ => Unit
  AnnTm := fun x => { t : Expr stlcGrammar SEnt.tm .loosest // truncExpr sRules t = x }

  pTy :=
    ((mixfix (G := styGrammar) () .loosest).weakenFollow
      (by
        intro t ht
        have h : t = kwAssign := ht
        subst h
        exact tyFollow_assign)).toLossyParserUnit (fun _ => rfl)

  pTm :=
    ((mixfix (G := stlcGrammar) SEnt.tm .loosest).weakenFollow
      (by
        intro t ht
        have h : t = kwDef := ht
        subst h
        exact sFollow_def) |> sRules.truncateParser) (fun _ => rfl)

end LambdaLab.Stlc.Named
