import LambdaLab.Pipeline.Compose
import LambdaLab.Parser.Numeral
import LambdaLab.Languages.CoIC.Named.Basic
import LambdaLab.TypeSystem.Named.FreeName
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.IsoParser.Mixfix.Unambiguity
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Parser.Truncation.Mixfix

/-!
# CoIC — the surface language

What a programmer writes: a run of declarations,

    def NAME : TERM := TERM
    inductive NAME := CTOR | CTOR | …          CTOR ::= NAME TERM*  (as an application)

    TERM ::= NAME | * | □ | Π NAME : TERM . TERM | λ NAME : TERM . TERM | TERM → TERM
           | TERM TERM | (TERM)

Types are terms, so one entry of the grammar covers both; a second entry holds binder names. A
constructor is written as the application of its name to its argument types —
`cons Nat List` — and parsed as a term; `Pipeline.lean` takes it apart.

The parser lands in `STm`, the CoC fragment of the named calculus (`STm.toNamed`): inductive types,
constructors and recursors are *names* here, and only the elaborator (`Pipeline.lean`) turns them
into the core's saturated nodes.

## Precedence

Binders (`λ`, `Π`) are loosest, then `→` (associating to the right), then application, then
atoms. A binder's body runs as far right as it can and may be anything, another binder included:
`Π A : * . Π x : A . A`, `λ A : * . λ x : A . x`. A binder anywhere else is parenthesized — as an
applied function `(λ x : A . x) y`, as an argument `f (λ x : A . x)`, as an arrow's operand
`(Π A : * . A) → *`.

## The arrow

`A → B` is a product whose binder `B` does not mention. The parser reads `A → B` as `Π z : A . B`
with `z` a name fresh for `B` — the name `freshFor B.fv`, deterministically — and the printer
writes a product as an arrow exactly when its binder is that name. So printing and parsing are
inverse on every term: a product the programmer wrote as `Π y : A . B` with an unused `y` keeps
its spelling and its name, and what evaluation reads back as an arrow (`Pipeline.lean` names unused
binders that way) prints as one.
-/

namespace LambdaLab.Languages.CoIC

open LambdaLab.Parser.IsoParser LambdaLab.Parser.IsoParser.Mixfix LambdaLab.Pipeline
open LambdaLab.Parser.LossyParser (LossyParser)
open LambdaLab.Parser.Truncation.Mixfix (Rules truncExpr)
open LambdaLab.Nominal (freshFor freshFor_not_in)
open LambdaLab.Languages.CoIC.DeBruijn (Srt)

/-! ## The lexicon

The parentheses, the binder symbols, `.`, `→`, `|` and the two sorts are self-delimiting:
`λx : *. x→x` reads as `λ x : * . x → x` does. The canonical printer hugs the parentheses and spaces
everything else. `:` is not self-delimiting, because `:=` is one token. -/

/-- What a token is, for CoIC. -/
abbrev coicLex : Lexicon := Lexicon.make ['('] [')'] ['λ', 'Π', '.', '→', '*', '□', '|']

abbrev CTok : Type := Token coicLex

/-! ## Tokens and names -/

/-- A token literal. -/
def tkC (s : String) (h : isToken coicLex s = true := by decide) : CTok := ⟨s, h⟩

def kwDefC : CTok := tkC "def"
def kwIndC : CTok := tkC "inductive"
def kwAssignC : CTok := tkC ":="
def barC : CTok := tkC "|"

/-- Grammar name-parts and declaration keywords: never names. -/
def coicReserved : List CTok :=
  [tkC "(", tkC ")", tkC "λ", tkC "Π", tkC ".", tkC ":", tkC "→", tkC "*", tkC "□", kwDefC,
    kwIndC, kwAssignC, barC]

/-- A name is any token that is not reserved. -/
abbrev isCName (t : CTok) : Bool := isFree coicReserved t

abbrev SName : Type := FreeName coicReserved

/-! ## The grammar: terms, binder names -/

inductive CEnt | tm | var
  deriving DecidableEq, Repr

inductive TmSym | paren | star | box | app | arrow | lam | pi
  deriving DecidableEq, Repr
inductive VarSym | paren
  deriving DecidableEq, Repr

def coicTmEntry : Entry CTok CEnt where
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

def coicVarEntry : Entry CTok CEnt where
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

def coicGrammar : Grammar CTok where
  Ent := CEnt
  entry | .tm => coicTmEntry | .var => coicVarEntry
  interiorTerminates := by
    intro e o e' t h
    cases e <;> cases e' <;> cases o <;>
      simp only [coicTmEntry, coicVarEntry, Operator.holeFollowers, Notation.holeFollowers,
        Notation.firstTok] at h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, reduceCtorEq,
        false_and, false_or, or_false, true_and] at h <;>
      first
        | exact h.elim
        | (subst h; exact ⟨by decide, by intro o'; cases o' <;> decide⟩)

instance : ∀ e : coicGrammar.Ent, DecidableEq (coicGrammar.entry e).Op
  | .tm => inferInstanceAs (DecidableEq TmSym)
  | .var => inferInstanceAs (DecidableEq VarSym)

/-- The grammar is unambiguous — derived from its lexical fields, not assumed. -/
theorem coicUnambiguous : Unambiguous coicGrammar := unambiguous coicGrammar

/-! ## The named syntax tree -/

/-- A term as written: the CoC fragment of the named calculus, over names. -/
inductive STm where
  | var : SName → STm
  | sort : Srt → STm
  | pi : SName → STm → STm → STm
  | lam : SName → STm → STm → STm
  | app : STm → STm → STm

/-- **What was written, in the named calculus.** -/
def STm.toNamed : STm → Named.Tm SName
  | .var x => .var x
  | .sort s => .sort s
  | .pi x A B => .pi x A.toNamed B.toNamed
  | .lam x A b => .lam x A.toNamed b.toNamed
  | .app f a => .app f.toNamed a.toNamed

/-- The free names. -/
def STm.fv : STm → List SName
  | .var x => [x]
  | .sort _ => []
  | .pi x A B => A.fv ++ B.fv.filter (· ≠ x)
  | .lam x A b => A.fv ++ b.fv.filter (· ≠ x)
  | .app f a => f.fv ++ a.fv

/-- Apply a term to arguments, left to right. -/
def STm.apps (h : STm) : List STm → STm
  | [] => h
  | a :: as => STm.apps (.app h a) as

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
def coicRules : Rules coicGrammar CC where
  var {e} t h :=
    match e, h with
    | .tm, h => STm.var ⟨t, h⟩
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
    | .tm, STm.var x       => .var x.1 x.2
    | .tm, STm.sort .star  => .node .star PUnit.unit
    | .tm, STm.sort .box   => .node .box PUnit.unit
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

/-- Where a term may stop: before `:=` (a definition's type), `|` (a constructor), or the next
declaration's keyword. -/
@[simp] def coicStops : List CTok := [kwAssignC, kwDefC, kwIndC, barC]

theorem coicFollow : ∀ t ∈ coicStops, follow (G := coicGrammar) CEnt.tm t = true := by
  decide

/-- Every spelling of a term. -/
abbrev STm.Ann (x : STm) : Type :=
  { t : Expr coicGrammar CEnt.tm .loosest // truncExpr coicRules t = x }

def coicTm : LossyParser CTok anyTok (· ∈ coicStops) STm STm.Ann :=
  ((mixfix (G := coicGrammar) CEnt.tm .loosest).weakenFollow coicFollow
    |> coicRules.truncateParser) (fun _ => rfl)

theorem coicTm_exact : coicTm.Exact :=
  Rules.truncateParser_exact coicRules (fun _ => rfl)
    (IsoParser.weakenFollow_exact _ (mixfix_exact _ _))

/-! ## Declarations -/

/-- The two declaration forms. -/
inductive CForm | defn | ind
  deriving DecidableEq, Repr

/-- `def NAME : TERM := TERM`. -/
structure DefBody where
  name : SName
  ty : STm
  tm : STm

/-- `inductive NAME := CTOR | … | CTOR`: at least one constructor, each an application of its
name to its argument types. -/
structure IndBody where
  name : SName
  first : STm
  rest : List STm

/-- The constructors, in order. -/
def IndBody.ctors (b : IndBody) : List STm := b.first :: b.rest

/-- A declaration. -/
inductive CDecl where
  | defn : DefBody → CDecl
  | ind : IndBody → CDecl

abbrev DefBody.Ann (b : DefBody) : Type := b.ty.Ann × b.tm.Ann

/-- A spelling for each term of a list. -/
def STm.AnnList : List STm → Type
  | [] => Unit
  | x :: xs => x.Ann × STm.AnnList xs

def STm.AnnList.default : (xs : List STm) → STm.AnnList xs
  | [] => ()
  | _ :: xs => (coicTm.default, STm.AnnList.default xs)

/-- The terms paired with their spellings. -/
def STm.AnnList.pairs : (xs : List STm) → STm.AnnList xs → List (Σ x : STm, x.Ann)
  | [], _ => []
  | x :: xs, (a, as) => ⟨x, a⟩ :: STm.AnnList.pairs xs as

abbrev IndBody.Ann (b : IndBody) : Type := b.first.Ann × STm.AnnList b.rest

/-- What follows `def`. -/
def defBodyIso :
    IsoParser CTok anyTok (· ∈ [kwDefC, kwIndC]) (Σ b : DefBody, b.Ann) DefBody :=
  IsoParser.enlargeFirst (fun _ h => absurd trivial h) <| gdo
    let n ← comap (fun s => s.1.name) (sat isCName)
    let _c ← tok (tkC ":")
    let A ← comap (fun s => ⟨s.1.ty, s.2.1⟩) coicTm.toIsoParser
    let _a ← tok kwAssignC
    let t ← comap (fun s => ⟨s.1.tm, s.2.2⟩)
      (coicTm.toIsoParser.weakenFollow (fun c hc => by
        simp only [coicStops, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
        rcases hc with rfl | rfl <;> simp))
    return DefBody.mk n A t

theorem defBodyIso_echo : ∀ s : Σ b : DefBody, b.Ann, (defBodyIso.print s).1 = s.1
  | ⟨⟨_, _, _⟩, _⟩ => rfl

def defBody : LossyParser CTok anyTok (· ∈ [kwDefC, kwIndC]) DefBody DefBody.Ann :=
  defBodyIso.toLossyParserSigma (fun {_} => (coicTm.default, coicTm.default)) defBodyIso_echo

/-- `| CTOR`. -/
def ctorStep : IsoParser CTok (· = barC) (· ∈ coicStops) (Σ x : STm, x.Ann) STm := gdo
  let _b ← tok barC
  let c ← coicTm.toIsoParser
  return c

/-- `CTOR | … | CTOR`. -/
def ctorsIso := chainl coicTm.toIsoParser ctorStep (fun c hc => by
  subst hc; decide)

theorem ctorsIso_rest : ∀ (xs : List STm) (as : STm.AnnList xs),
    many1PrintV ctorStep (STm.AnnList.pairs xs as) = xs
  | [], _ => rfl
  | _ :: xs, (_, as) => by
      show (ctorStep.print _).1 :: many1PrintV ctorStep (STm.AnnList.pairs xs as) = _
      rw [ctorsIso_rest xs as]
      rfl

/-- What follows `inductive`. -/
def indBodyIso :
    IsoParser CTok anyTok (· ∈ [kwDefC, kwIndC]) (Σ b : IndBody, b.Ann) IndBody :=
  IsoParser.enlargeFirst (fun _ h => absurd trivial h) <| gdo
    let n ← comap (fun s => s.1.name) (sat isCName)
    let _a ← tok kwAssignC
    let cs ← comap (fun s => (⟨s.1.first, s.2.1⟩, STm.AnnList.pairs s.1.rest s.2.2))
      (ctorsIso.weakenFollow (fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> decide))
    return IndBody.mk n cs.1 cs.2

theorem indBodyIso_echo : ∀ s : Σ b : IndBody, b.Ann, (indBodyIso.print s).1 = s.1
  | ⟨⟨n, f, rest⟩, (a, as)⟩ => by
      show IndBody.mk n f (many1PrintV ctorStep (STm.AnnList.pairs rest as)) = _
      rw [ctorsIso_rest]

def indBody : LossyParser CTok anyTok (· ∈ [kwDefC, kwIndC]) IndBody IndBody.Ann :=
  indBodyIso.toLossyParserSigma (fun {b} => (coicTm.default, STm.AnnList.default b.rest))
    indBodyIso_echo

def CForm.head : CForm → CTok
  | .defn => kwDefC
  | .ind => kwIndC

def CForm.Body : CForm → Type
  | .defn => DefBody
  | .ind => IndBody

def CForm.BodyAnn : (f : CForm) → f.Body → Type
  | .defn => DefBody.Ann
  | .ind => IndBody.Ann

def CForm.body : (f : CForm) →
    LossyParser CTok anyTok (· ∈ [kwDefC, kwIndC]) f.Body f.BodyAnn
  | .defn => defBody
  | .ind => indBody

def CDecl.toSigma : CDecl → Σ f : CForm, f.Body
  | .defn b => ⟨.defn, b⟩
  | .ind b => ⟨.ind, b⟩

def CDecl.ofSigma : (Σ f : CForm, f.Body) → CDecl
  | ⟨.defn, b⟩ => .defn b
  | ⟨.ind, b⟩ => .ind b

/-- **The CoIC language**: two forms, `def` and `inductive`. -/
def coicLanguage : Language where
  lex := coicLex
  Form := CForm
  forms := [.defn, .ind]
  forms_complete f := by cases f <;> decide
  head := CForm.head
  head_injective f g h := by
    cases f <;> cases g <;> first | rfl | exact absurd h (by decide)
  Body := CForm.Body
  BodyAnn := CForm.BodyAnn
  body := CForm.body
  Decl := CDecl
  decl := ⟨CDecl.toSigma, CDecl.ofSigma, by intro d; cases d <;> rfl,
    by rintro ⟨f, b⟩; cases f <;> rfl⟩

end LambdaLab.Languages.CoIC
