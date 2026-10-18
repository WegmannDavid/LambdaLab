import LambdaLab.Pipeline.Compose
import LambdaLab.Parser.Numeral
import LambdaLab.Languages.ECC.Named.Basic
import LambdaLab.TypeSystem.Named.FreeName
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.IsoParser.Mixfix.Unambiguity
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Parser.Truncation.Mixfix

/-!
# ECC — the surface language

What a programmer writes: a run of definitions,

    def NAME : TERM := TERM

    TERM ::= NAME | Prop | Type | Π NAME : TERM . TERM | λ NAME : TERM . TERM | TERM → TERM
           | TERM TERM | (TERM)

Types are terms, so one entry of the grammar covers both; a second entry holds binder names.

## Universes

`Prop` is a keyword, and so is `Type`. A universe is written as in Lean, `Type 0`, `Type 1`, …:
the grammar sees the application of `Type` to a name, and the elaborator (`Pipeline.lean`) reads
`Type` applied to a run of digits as that universe — so the grammar needs nothing special, and a
universe prints and parses back like any application. A bare `Type` is `Type 0`. `STm.toNamed`
embeds what was parsed into the named calculus (`Named/`) the same way.

## Precedence

Binders (`λ`, `Π`) are loosest, then `→` (associating to the right), then application, then
atoms. A binder's body runs as far right as it can and may be anything, another binder included.
A binder anywhere else is parenthesized.

## The arrow

`A → B` is a product whose binder `B` does not mention. The parser reads `A → B` as `Π z : A . B`
with `z` a name fresh for `B` — the name `freshFor B.fv`, deterministically — and the printer
writes a product as an arrow exactly when its binder is that name. So printing and parsing are
inverse on every term.
-/

namespace LambdaLab.Languages.ECC

open LambdaLab.Parser.IsoParser LambdaLab.Parser.IsoParser.Mixfix LambdaLab.Pipeline
open LambdaLab.Parser.LossyParser (LossyParser)
open LambdaLab.Parser.Truncation.Mixfix (Rules truncExpr)
open LambdaLab.Nominal (freshFor freshFor_not_in)
open LambdaLab.Languages.ECC.DeBruijn (Srt)
open LambdaLab.Parser.Numeral (isDigitChar charsNat)

/-! ## The lexicon

The parentheses, the binder symbols, `.` and `→` are self-delimiting: `λx : Prop. x→x` reads as
`λ x : Prop . x → x` does. The canonical printer hugs the parentheses and spaces
everything else. `:` is not self-delimiting, because `:=` is one token. -/

/-- What a token is, for ECC. -/
abbrev eccLex : Lexicon := Lexicon.make ['('] [')'] ['λ', 'Π', '.', '→']

abbrev CTok : Type := Token eccLex

/-! ## Tokens and names -/

/-- A token literal. -/
def tkC (s : String) (h : isToken eccLex s = true := by decide) : CTok := ⟨s, h⟩

def kwDefC : CTok := tkC "def"
def kwAssignC : CTok := tkC ":="

/-- Grammar name-parts and declaration keywords: never names. -/
def eccReserved : List CTok :=
  [tkC "(", tkC ")", tkC "λ", tkC "Π", tkC ".", tkC ":", tkC "→", tkC "Prop", tkC "Type", kwDefC,
    kwAssignC]

/-- A name is any token that is not reserved. -/
abbrev isCName (t : CTok) : Bool := isFree eccReserved t

abbrev SName : Type := FreeName eccReserved

/-! ## The grammar: terms, binder names -/

inductive CEnt | tm | var
  deriving DecidableEq, Repr

inductive TmSym | paren | prop | type | app | arrow | lam | pi
  deriving DecidableEq, Repr
inductive VarSym | paren
  deriving DecidableEq, Repr

def eccTmEntry : Entry CTok CEnt where
  Op := TmSym
  operator
    | .paren => .closed (.cons (tkC "(") .tm (.last (tkC ")")))
    | .prop  => .closed (.last (tkC "Prop"))
    | .type  => .closed (.last (tkC "Type"))
    | .app   => .juxt
    | .arrow => .infxr (.last (tkC "→"))
    | .lam   => .binder (.cons (tkC "λ") .var (.cons (tkC ":") .tm (.last (tkC "."))))
    | .pi    => .binder (.cons (tkC "Π") .var (.cons (tkC ":") .tm (.last (tkC "."))))
  ops := [.paren, .prop, .type, .app, .arrow, .lam, .pi]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.lam, .pi]
  tighter
    | .lam => [.arrow] | .pi => [.arrow] | .arrow => [.app]
    | .app => [.paren, .prop, .type] | .paren => [] | .prop => [] | .type => []
  rank
    | .paren => 0 | .prop => 0 | .type => 0 | .app => 1 | .arrow => 2 | .lam => 3 | .pi => 3
  topRank := 4
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := isCName
  headsDistinct := by
    intro o₁ o₂ h₁ h
    cases o₁ <;> cases o₂ <;>
      simp_all [Operator.headTok?, Operator.nameTokens, Notation.toTokens] <;>
      exact absurd h (by decide)
  juxtUnique := by
    intro o₁ o₂ h₁ h₂
    cases o₁ <;> cases o₂ <;> simp_all
  varDisjoint := by
    intro o t ht
    cases o <;>
      simp only [Operator.nameTokens, Notation.toTokens,
        List.mem_cons, List.not_mem_nil, or_false] at ht <;>
      first
        | (subst ht; decide)
        | (rcases ht with rfl | rfl <;> decide)
        | (rcases ht with rfl | rfl | rfl <;> decide)

def eccVarEntry : Entry CTok CEnt where
  Op := VarSym
  operator | .paren => .closed (.cons (tkC "(") .var (.last (tkC ")")))
  ops := [.paren]
  ops_complete := by intro o; cases o; decide
  loosest := [.paren]
  tighter | .paren => []
  rank | .paren => 0
  topRank := 1
  rank_tighter := by intro a b h; cases a; cases b; simp_all
  rank_lt_topRank := by intro o; cases o; decide
  isVar := isCName
  headsDistinct := by
    intro o₁ o₂ h₁ h
    cases o₁; cases o₂; rfl
  juxtUnique := by
    intro o₁ o₂ h₁ h₂
    cases o₁; cases o₂; simp_all
  varDisjoint := by
    intro o t ht
    cases o
    simp only [Operator.nameTokens, Notation.toTokens,
      List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> decide

def eccGrammar : Grammar CTok where
  Ent := CEnt
  entry | .tm => eccTmEntry | .var => eccVarEntry
  interiorTerminates := by
    intro e o e' t h
    cases e <;> cases e' <;> cases o <;>
      simp only [eccTmEntry, eccVarEntry, Operator.holeFollowers, Notation.holeFollowers,
        Notation.firstTok] at h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, reduceCtorEq,
        false_and, false_or, or_false, true_and] at h <;>
      first
        | exact h.elim
        | (subst h; exact ⟨by decide, by intro o'; cases o' <;> decide⟩)

instance : ∀ e : eccGrammar.Ent, DecidableEq (eccGrammar.entry e).Op
  | .tm => inferInstanceAs (DecidableEq TmSym)
  | .var => inferInstanceAs (DecidableEq VarSym)

/-- The grammar is unambiguous — derived from its lexical fields, not assumed. -/
theorem eccUnambiguous : Unambiguous eccGrammar := unambiguous eccGrammar

/-! ## The named syntax tree -/

/-- A term as written. `Type` on its own is a keyword; `Type 0` is its application to a name. -/
inductive STm where
  | var : SName → STm
  | prop : STm
  | typeKw : STm
  | pi : SName → STm → STm → STm
  | lam : SName → STm → STm → STm
  | app : STm → STm → STm

/-- Is this token a run of decimal digits? -/
def isDigitsTok (t : CTok) : Bool := t.val.toList.all isDigitChar

/-- The universe level a run of digits spells. -/
def levelOf (x : SName) : Nat := charsNat x.val.val.toList

/-- **What was written, in the named calculus**: `Type` applied to digits is that universe, a bare
`Type` is `Type 0`. -/
def STm.toNamed : STm → Named.Tm SName
  | .var x => .var x
  | .prop => .sort .prop
  | .typeKw => .sort (.type 0)
  | .pi x A B => .pi x A.toNamed B.toNamed
  | .lam x A b => .lam x A.toNamed b.toNamed
  | .app .typeKw (.var x) =>
      if isDigitsTok x.val then .sort (.type (levelOf x)) else .app (.sort (.type 0)) (.var x)
  | .app f a => .app f.toNamed a.toNamed

/-- The free names. -/
def STm.fv : STm → List SName
  | .var x => [x]
  | .prop => []
  | .typeKw => []
  | .pi x A B => A.fv ++ B.fv.filter (· ≠ x)
  | .lam x A b => A.fv ++ b.fv.filter (· ≠ x)
  | .app f a => f.fv ++ a.fv

/-- The size of a term as written, annotations counted — the measure the truncation needs. -/
def STm.size : STm → Nat
  | .var _ => 1
  | .prop => 1
  | .typeKw => 1
  | .pi _ A B => STm.size A + STm.size B + 2
  | .lam _ A b => STm.size A + STm.size b + 2
  | .app f a => STm.size f + STm.size a + 1

theorem STm.size_pos : ∀ t : STm, 0 < STm.size t
  | .var _ => by simp [STm.size]
  | .prop => by simp [STm.size]
  | .typeKw => by simp [STm.size]
  | .pi _ _ _ => by simp [STm.size]
  | .lam _ _ _ => by simp [STm.size]
  | .app _ _ => by simp [STm.size]

/-- The binder `A → B` stands for: a name fresh for `B`. -/
def arrowName (B : STm) : SName := freshFor B.fv

/-- What each entry parses into. -/
def CC : CEnt → Type
  | .tm => STm
  | .var => SName

/-- The truncation instructions: parentheses vanish, `A → B` is a product over a fresh name, and
a product over that name is printed as an arrow. -/
def eccRules : Rules eccGrammar CC where
  var {e} t h :=
    match e, h with
    | .tm, h => STm.var ⟨t, h⟩
    | .var, h => ⟨t, h⟩
  op {e} o vs :=
    match e, o, vs with
    | .tm, .paren, (t, _)       => t
    | .tm, .prop,  _            => .prop
    | .tm, .type,  _            => .typeKw
    | .tm, .app,   (f, a, _)    => .app f a
    | .tm, .arrow, (A, B, _)    => .pi (arrowName B) A B
    | .tm, .lam,   (x, A, b, _) => .lam x A b
    | .tm, .pi,    (x, A, B, _) => .pi x A B
    | .var, .paren, (x, _)      => x
  dest {e} x :=
    match e, x with
    | .tm, STm.var x       => .var x.1 x.2
    | .tm, STm.prop        => .node .prop PUnit.unit
    | .tm, STm.typeKw      => .node .type PUnit.unit
    | .tm, STm.app f a     => .node .app (f, a, PUnit.unit)
    | .tm, STm.lam x A b   => .node .lam (x, A, b, PUnit.unit)
    | .tm, STm.pi x A B    =>
        if x = arrowName B then .node .arrow (A, B, PUnit.unit) else .node .pi (x, A, B, PUnit.unit)
    | .var, x => .var x.1 x.2
  parenOp | .tm => TmSym.paren | .var => VarSym.paren
  lp _ := tkC "("
  rp _ := tkC ")"
  paren_eq | .tm => rfl | .var => rfl
  holesOk := by intro e o; cases e <;> cases o <;> decide
  topOk := by intro e o; cases e <;> cases o <;> decide
  alg_dest := by
    intro e x
    cases e
    · cases x with
      | var => rfl
      | prop => rfl
      | typeKw => rfl
      | app => rfl
      | lam => rfl
      | pi x A B =>
          dsimp only
          by_cases h : x = arrowName B
          · rw [if_pos h]; subst h; rfl
          · rw [if_neg h]
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
      | var x => trivial
      | prop => trivial
      | typeKw => trivial
      | app f a => exact ⟨by simp +arith [STm.size], by simp +arith [STm.size], trivial⟩
      | lam x A b =>
          refine ⟨?_, by simp +arith [STm.size], by simp +arith [STm.size], trivial⟩
          have := STm.size_pos A
          show 1 < STm.size (.lam x A b)
          simp only [STm.size]
          omega
      | pi x A B =>
          dsimp only
          by_cases h : x = arrowName B
          · rw [if_pos h]
            exact ⟨by simp +arith [STm.size], by simp +arith [STm.size], trivial⟩
          · rw [if_neg h]
            refine ⟨?_, by simp +arith [STm.size], by simp +arith [STm.size], trivial⟩
            have := STm.size_pos A
            show 1 < STm.size (.pi x A B)
            simp only [STm.size]
            omega
    · trivial

/-! ## The term parser -/

/-- A term must stop at `:=` (a declaration's type) and at the next declaration's keyword. -/
theorem eccFollow : ∀ t ∈ [kwAssignC, kwDefC], follow (G := eccGrammar) CEnt.tm t = true := by
  decide

/-- Every spelling of a term. -/
abbrev STm.Ann (x : STm) : Type :=
  { t : Expr eccGrammar CEnt.tm .loosest // truncExpr eccRules t = x }

def eccTm : LossyParser CTok anyTok (· ∈ [kwAssignC, kwDefC]) STm STm.Ann :=
  ((mixfix (G := eccGrammar) CEnt.tm .loosest).weakenFollow eccFollow
    |> eccRules.truncateParser) (fun _ => rfl)

theorem eccTm_exact : eccTm.Exact :=
  Rules.truncateParser_exact eccRules (fun _ => rfl)
    (IsoParser.weakenFollow_exact _ (mixfix_exact _ _))

/-! ## Declarations: `def NAME : TERM := TERM` -/

/-- A definition. -/
structure CDecl where
  name : SName
  ty : STm
  tm : STm

abbrev CDecl.Ann (d : CDecl) : Type := d.ty.Ann × d.tm.Ann

/-- What follows `def`. -/
def eccBodyIso : IsoParser CTok anyTok (· ∈ [kwDefC]) (Σ d : CDecl, d.Ann) CDecl :=
  IsoParser.enlargeFirst (fun _ h => absurd trivial h) <| gdo
    let n ← comap (fun s => s.1.name) (sat isCName)
    let _c ← tok (tkC ":")
    let A ← comap (fun s => ⟨s.1.ty, s.2.1⟩) eccTm.toIsoParser
    let _a ← tok kwAssignC
    let t ← comap (fun s => ⟨s.1.tm, s.2.2⟩)
      (eccTm.toIsoParser.weakenFollow (fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
        exact .inr hc))
    return CDecl.mk n A t

theorem eccBodyIso_echo : ∀ s : Σ d : CDecl, d.Ann, (eccBodyIso.print s).1 = s.1
  | ⟨⟨_, _, _⟩, _⟩ => rfl

def eccBody : LossyParser CTok anyTok (· ∈ [kwDefC]) CDecl CDecl.Ann :=
  eccBodyIso.toLossyParserSigma (fun {_} => (eccTm.default, eccTm.default)) eccBodyIso_echo

/-- **The ECC language**: one form, `def`. -/
def eccLanguage : Language where
  lex := eccLex
  Form := Unit
  forms := [()]
  forms_complete _ := List.mem_singleton.mpr rfl
  head _ := kwDefC
  head_injective _ _ _ := rfl
  Body _ := CDecl
  BodyAnn _ := CDecl.Ann
  body _ := eccBody
  Decl := CDecl
  decl := ⟨fun d => ⟨(), d⟩, fun s => s.2, fun _ => rfl, fun _ => rfl⟩

end LambdaLab.Languages.ECC
