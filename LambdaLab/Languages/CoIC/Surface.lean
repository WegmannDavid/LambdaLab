import LambdaLab.Pipeline.Compose
import LambdaLab.Parser.Numeral
import LambdaLab.Languages.CoIC.Named.Basic
import LambdaLab.TypeSystem.Named.FreeName
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.IsoParser.Mixfix.Unambiguity
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Parser.Truncation.Mixfix

/-!
# The Calculus of Constructions — the surface language

What a programmer writes: a run of definitions,

    def NAME : TERM := TERM

    TERM ::= NAME | * | □ | Π NAME : TERM . TERM | λ NAME : TERM . TERM | TERM → TERM
           | TERM TERM | (TERM)

Types are terms, so one entry of the grammar covers both; a second entry holds binder names. The
parser lands in the **named calculus** (`Named/`): `STm` is `Named.Tm SName`, parentheses truncated
away, so everything `Named/` proves is about what was parsed. `Pipeline.lean` translates it into
the de Bruijn core to check and run it.

## Precedence

Binders (`λ`, `Π`) are loosest, then `→` (associating to the right), then application, then
atoms. A binder's body runs as far right as it can and may be anything, another binder included:
`Π A : * . Π x : A . A`, `λ A : * . λ x : A . x`. A binder anywhere else is parenthesized — as an
applied function `(λ x : A . x) y`, as an argument `f (λ x : A . x)`, as an arrow's operand
`(Π A : * . A) → *`.

## The arrow

`A → B` is a product whose binder `B` does not mention. The named calculus has no arrow of its
own, so the parser reads `A → B` as `Π z : A . B` with `z` a name fresh for `B` — the name
`freshFor B.fv`, deterministically — and the printer writes a product as an arrow exactly when its
binder is that name. So printing and parsing are inverse on every term: a product the programmer
wrote as `Π y : A . B` with an unused `y` keeps its spelling and its name, and what evaluation
reads back as an arrow (`Pipeline.lean` names unused binders that way) prints as one.
-/

namespace LambdaLab.Languages.CoIC

open LambdaLab.Parser.IsoParser LambdaLab.Parser.IsoParser.Mixfix LambdaLab.Pipeline
open LambdaLab.Parser.LossyParser (LossyParser)
open LambdaLab.Parser.Truncation.Mixfix (Rules truncExpr)
open LambdaLab.Nominal (freshFor freshFor_not_in)
open LambdaLab.Languages.CoIC.DeBruijn (Srt)

/-! ## The lexicon

The parentheses, the binder symbols, `.`, `→` and the two sorts are self-delimiting:
`λx : *. x→x` reads as `λ x : * . x → x` does. The canonical printer hugs the parentheses and spaces
everything else. `:` is not self-delimiting, because `:=` is one token. -/

/-- What a token is, for CoC. -/
abbrev cocLex : Lexicon := Lexicon.make ['('] [')'] ['λ', 'Π', '.', '→', '*', '□']

abbrev CTok : Type := Token cocLex

/-! ## Tokens and names -/

/-- A token literal. -/
def tkC (s : String) (h : isToken cocLex s = true := by decide) : CTok := ⟨s, h⟩

def kwDefC : CTok := tkC "def"
def kwAssignC : CTok := tkC ":="

/-- Grammar name-parts and declaration keywords: never names. -/
def cocReserved : List CTok :=
  [tkC "(", tkC ")", tkC "λ", tkC "Π", tkC ".", tkC ":", tkC "→", tkC "*", tkC "□", kwDefC,
    kwAssignC]

/-- A name is any token that is not reserved. -/
abbrev isCName (t : CTok) : Bool := isFree cocReserved t

abbrev SName : Type := FreeName cocReserved

/-! ## The grammar: terms, binder names -/

inductive CEnt | tm | var
  deriving DecidableEq, Repr

inductive TmSym | paren | star | box | app | arrow | lam | pi
  deriving DecidableEq, Repr
inductive VarSym | paren
  deriving DecidableEq, Repr

def cocTmEntry : Entry CTok CEnt where
  Op := TmSym
  operator
    | .paren => .closed (.cons (tkC "(") .tm (.last (tkC ")")))
    | .star  => .closed (.last (tkC "*"))
    | .box   => .closed (.last (tkC "□"))
    | .app   => .juxt
    | .arrow => .infxr (.last (tkC "→"))
    | .lam   => .binder (.cons (tkC "λ") .var (.cons (tkC ":") .tm (.last (tkC "."))))
    | .pi    => .binder (.cons (tkC "Π") .var (.cons (tkC ":") .tm (.last (tkC "."))))
  ops := [.paren, .star, .box, .app, .arrow, .lam, .pi]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.lam, .pi]
  tighter
    | .lam => [.arrow] | .pi => [.arrow] | .arrow => [.app]
    | .app => [.paren, .star, .box] | .paren => [] | .star => [] | .box => []
  rank
    | .paren => 0 | .star => 0 | .box => 0 | .app => 1 | .arrow => 2 | .lam => 3 | .pi => 3
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

def cocVarEntry : Entry CTok CEnt where
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

def cocGrammar : Grammar CTok where
  Ent := CEnt
  entry | .tm => cocTmEntry | .var => cocVarEntry
  interiorTerminates := by
    intro e o e' t h
    cases e <;> cases e' <;> cases o <;>
      simp only [cocTmEntry, cocVarEntry, Operator.holeFollowers, Notation.holeFollowers,
        Notation.firstTok] at h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, reduceCtorEq,
        false_and, false_or, or_false, true_and] at h <;>
      first
        | exact h.elim
        | (subst h; exact ⟨by decide, by intro o'; cases o' <;> decide⟩)

instance : ∀ e : cocGrammar.Ent, DecidableEq (cocGrammar.entry e).Op
  | .tm => inferInstanceAs (DecidableEq TmSym)
  | .var => inferInstanceAs (DecidableEq VarSym)

/-- The grammar is unambiguous — derived from its lexical fields, not assumed. -/
theorem cocUnambiguous : Unambiguous cocGrammar := unambiguous cocGrammar

/-! ## The named syntax tree -/

/-- A term as written: a named CoC term. The parser lands in the named calculus itself. -/
abbrev STm : Type := Named.Tm SName

/-- The size of a term as written, annotations counted — the measure the truncation needs. -/
def STm.size : STm → Nat
  | .var _ => 1
  | .sort _ => 1
  | .pi _ A B => STm.size A + STm.size B + 2
  | .lam _ A b => STm.size A + STm.size b + 2
  | .app f a => STm.size f + STm.size a + 1

theorem STm.size_pos : ∀ t : STm, 0 < STm.size t
  | .var _ => by simp [STm.size]
  | .sort _ => by simp [STm.size]
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
def cocRules : Rules cocGrammar CC where
  var {e} t h :=
    match e, h with
    | .tm, h => Named.Tm.var ⟨t, h⟩
    | .var, h => ⟨t, h⟩
  op {e} o vs :=
    match e, o, vs with
    | .tm, .paren, (t, _)       => t
    | .tm, .star,  _            => .sort .star
    | .tm, .box,   _            => .sort .box
    | .tm, .app,   (f, a, _)    => .app f a
    | .tm, .arrow, (A, B, _)    => .pi (arrowName B) A B
    | .tm, .lam,   (x, A, b, _) => .lam x A b
    | .tm, .pi,    (x, A, B, _) => .pi x A B
    | .var, .paren, (x, _)      => x
  dest {e} x :=
    match e, x with
    | .tm, Named.Tm.var x       => .var x.1 x.2
    | .tm, Named.Tm.sort .star  => .node .star PUnit.unit
    | .tm, Named.Tm.sort .box   => .node .box PUnit.unit
    | .tm, Named.Tm.app f a     => .node .app (f, a, PUnit.unit)
    | .tm, Named.Tm.lam x A b   => .node .lam (x, A, b, PUnit.unit)
    | .tm, Named.Tm.pi x A B    =>
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
      | sort s => cases s <;> rfl
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
      | sort s => cases s <;> trivial
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
theorem cocFollow : ∀ t ∈ [kwAssignC, kwDefC], follow (G := cocGrammar) CEnt.tm t = true := by
  decide

/-- Every spelling of a term. -/
abbrev STm.Ann (x : STm) : Type :=
  { t : Expr cocGrammar CEnt.tm .loosest // truncExpr cocRules t = x }

def cocTm : LossyParser CTok anyTok (· ∈ [kwAssignC, kwDefC]) STm STm.Ann :=
  ((mixfix (G := cocGrammar) CEnt.tm .loosest).weakenFollow cocFollow
    |> cocRules.truncateParser) (fun _ => rfl)

theorem cocTm_exact : cocTm.Exact :=
  Rules.truncateParser_exact cocRules (fun _ => rfl)
    (IsoParser.weakenFollow_exact _ (mixfix_exact _ _))

/-! ## Declarations: `def NAME : TERM := TERM` -/

/-- A definition. -/
structure CDecl where
  name : SName
  ty : STm
  tm : STm

abbrev CDecl.Ann (d : CDecl) : Type := d.ty.Ann × d.tm.Ann

/-- What follows `def`. -/
def cocBodyIso : IsoParser CTok anyTok (· ∈ [kwDefC]) (Σ d : CDecl, d.Ann) CDecl :=
  IsoParser.enlargeFirst (fun _ h => absurd trivial h) <| gdo
    let n ← comap (fun s => s.1.name) (sat isCName)
    let _c ← tok (tkC ":")
    let A ← comap (fun s => ⟨s.1.ty, s.2.1⟩) cocTm.toIsoParser
    let _a ← tok kwAssignC
    let t ← comap (fun s => ⟨s.1.tm, s.2.2⟩)
      (cocTm.toIsoParser.weakenFollow (fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
        exact .inr hc))
    return CDecl.mk n A t

theorem cocBodyIso_echo : ∀ s : Σ d : CDecl, d.Ann, (cocBodyIso.print s).1 = s.1
  | ⟨⟨_, _, _⟩, _⟩ => rfl

def cocBody : LossyParser CTok anyTok (· ∈ [kwDefC]) CDecl CDecl.Ann :=
  cocBodyIso.toLossyParserSigma (fun {_} => (cocTm.default, cocTm.default)) cocBodyIso_echo

/-- **The CoC language**: one form, `def`. -/
def cocLanguage : Language where
  lex := cocLex
  Form := Unit
  forms := [()]
  forms_complete _ := List.mem_singleton.mpr rfl
  head _ := kwDefC
  head_injective _ _ _ := rfl
  Body _ := CDecl
  BodyAnn _ := CDecl.Ann
  body _ := cocBody
  Decl := CDecl
  decl := ⟨fun d => ⟨(), d⟩, fun s => s.2, fun _ => rfl, fun _ => rfl⟩

end LambdaLab.Languages.CoIC
