import LambdaLab.Pipeline.Compose
import LambdaLab.Parser.Numeral
import LambdaLab.Languages.SystemF.Named.Basic
import LambdaLab.TypeSystem.Named.FreeName
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.IsoParser.Mixfix.Unambiguity
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Parser.Truncation.Mixfix

/-!
# System F — the surface language

What a programmer writes: named variables, and two declaration forms.

    type NAME := TYPE
    def NAME : TYPE := TERM

    TYPE ::= NAME | TYPE → TYPE | ∀ NAME . TYPE | (TYPE)
    TERM ::= NAME | λ NAME : TYPE . TERM | TERM TERM | Λ NAME . TERM | TERM [TYPE] | (TERM)

A `type` declaration is an abbreviation: later types may name it, and it means its definition.
A `def` declaration names a term at a declared type; later terms may name it.

The grammar is the mixfix engine's, with three entries as in STLC — terms, binder names, types —
and parses straight into the **named calculus** (`Named/`): `STy` and `STm` are `Named.Ty SName`
and `Named.Tm SName`, parentheses truncated away. Everything `Named/` proves is about what was
parsed; `Pipeline.lean` translates it into the de Bruijn core to check and run it.

## Precedence

Binders (`λ`, `Λ`, `∀`) are loosest, then application, then type application, then parentheses:
`n [α] f x` is `((n [α]) f) x`. The engine parses a prefix operator's body, and a postfix
operator's operand, strictly tighter than the operator itself, so a binder directly inside a
binder's body, or a type application of a type application, needs parentheses:
`Λ α . (λ x : α . x)`, `(f [A]) [B]`. For the same reason a `∀` to the right of an arrow
does: `(∀ α . α) → (∀ α . α)`. The canonical print puts them back where needed.
-/

namespace LambdaLab.Languages.SystemF

open LambdaLab.Parser.IsoParser LambdaLab.Parser.IsoParser.Mixfix LambdaLab.Pipeline
open LambdaLab.Parser.LossyParser (LossyParser)
open LambdaLab.Parser.Truncation.Mixfix (Rules truncExpr)
open LambdaLab.Parser.Numeral (isDigitChar natTok natOfTok isNatTok)

/-! ## The lexicon

The brackets and the binder symbols are self-delimiting: `Λa. λx : a. f [a] x` reads as
`Λ a . λ x : a . f [ a ] x` does. The canonical printer hugs the brackets and spaces everything
else — `Λ a . λ x : a . f [a] x`. `:` is not self-delimiting, because `:=` is one token; so
`x : a` keeps its spaces. -/

/-- What a token is, for System F. -/
abbrev sfLex : Lexicon := Lexicon.make ['(', '['] [')', ']'] ['λ', 'Λ', '∀', '.', '→']

abbrev SFTok : Type := Token sfLex

/-! ## Tokens and names -/

/-- A token literal. -/
def tkSF (s : String) (h : isToken sfLex s = true := by decide) : SFTok := ⟨s, h⟩

def kwDefF : SFTok := tkSF "def"
def kwTypeF : SFTok := tkSF "type"
def kwAssignF : SFTok := tkSF ":="

/-- Grammar name-parts and declaration keywords: never names. -/
def sfReserved : List SFTok :=
  [tkSF "(", tkSF ")", tkSF "λ", tkSF "Λ", tkSF "∀", tkSF ".", tkSF ":", tkSF "→", tkSF "[",
    tkSF "]", kwDefF, kwTypeF, kwAssignF]

/-- A name is any token that is not reserved — type variables, term variables and declared names
alike. -/
abbrev isSFName (t : SFTok) : Bool := isFree sfReserved t

abbrev SName : Type := FreeName sfReserved

/-! ## The grammar: terms, binder names, types -/

inductive SFEnt | tm | var | ty
  deriving DecidableEq, Repr

inductive TmSym | paren | app | tapp | lam | tlam
  deriving DecidableEq, Repr
inductive VarSym | paren
  deriving DecidableEq, Repr
inductive TySym | paren | arrow | all
  deriving DecidableEq, Repr

def sfTmEntry : Entry SFTok SFEnt where
  Op := TmSym
  operator
    | .paren => .closed (.cons (tkSF "(") .tm (.last (tkSF ")")))
    | .app   => .juxt
    | .tapp  => .postfx (.cons (tkSF "[") .ty (.last (tkSF "]")))
    | .lam   => .prefx (.cons (tkSF "λ") .var (.cons (tkSF ":") .ty (.last (tkSF "."))))
    | .tlam  => .prefx (.cons (tkSF "Λ") .var (.last (tkSF ".")))
  ops := [.paren, .app, .tapp, .lam, .tlam]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.lam, .tlam]
  tighter | .lam => [.app] | .tlam => [.app] | .app => [.tapp] | .tapp => [.paren] | .paren => []
  rank | .paren => 0 | .tapp => 1 | .app => 2 | .lam => 3 | .tlam => 3
  topRank := 4
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := isSFName
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
        | (rcases ht with rfl | rfl <;> decide)
        | (rcases ht with rfl | rfl | rfl <;> decide)

def sfVarEntry : Entry SFTok SFEnt where
  Op := VarSym
  operator | .paren => .closed (.cons (tkSF "(") .var (.last (tkSF ")")))
  ops := [.paren]
  ops_complete := by intro o; cases o; decide
  loosest := [.paren]
  tighter | .paren => []
  rank | .paren => 0
  topRank := 1
  rank_tighter := by intro a b h; cases a; cases b; simp_all
  rank_lt_topRank := by intro o; cases o; decide
  isVar := isSFName
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

def sfTyEntry : Entry SFTok SFEnt where
  Op := TySym
  operator
    | .paren => .closed (.cons (tkSF "(") .ty (.last (tkSF ")")))
    | .arrow => .infxr (.last (tkSF "→"))
    | .all   => .prefx (.cons (tkSF "∀") .var (.last (tkSF ".")))
  ops := [.paren, .arrow, .all]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.all]
  tighter | .all => [.arrow] | .arrow => [.paren] | .paren => []
  rank | .paren => 0 | .arrow => 1 | .all => 2
  topRank := 3
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := isSFName
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
        | (rcases ht with rfl | rfl <;> decide)
        | (rcases ht with rfl | rfl | rfl <;> decide)

def sfGrammar : Grammar SFTok where
  Ent := SFEnt
  entry | .tm => sfTmEntry | .var => sfVarEntry | .ty => sfTyEntry
  interiorTerminates := by
    intro e o e' t h
    cases e <;> cases e' <;> cases o <;>
      simp only [sfTmEntry, sfVarEntry, sfTyEntry, Operator.holeFollowers, Notation.holeFollowers,
        Notation.firstTok] at h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, reduceCtorEq,
        false_and, false_or, or_false, true_and] at h <;>
      first
        | exact h.elim
        | (subst h; exact ⟨by decide, by intro o'; cases o' <;> decide⟩)

instance : ∀ e : sfGrammar.Ent, DecidableEq (sfGrammar.entry e).Op
  | .tm => inferInstanceAs (DecidableEq TmSym)
  | .var => inferInstanceAs (DecidableEq VarSym)
  | .ty => inferInstanceAs (DecidableEq TySym)

/-- The grammar is unambiguous — derived from its lexical fields, not assumed. -/
theorem sfUnambiguous : Unambiguous sfGrammar := unambiguous sfGrammar

/-! ## The named syntax tree -/

/-- A type as written: a named System F type, named by the grammar's names. -/
abbrev STy : Type := Named.Ty SName

/-- A term as written: a named System F term. The parser lands in the named calculus itself
(`Named/`), so everything proved there is about what was parsed. -/
abbrev STm : Type := Named.Tm SName

/-- The size of a type as written. -/
def STy.size : STy → Nat
  | .var _ => 1
  | .arr a b => STy.size a + STy.size b + 1
  | .all _ a => STy.size a + 2

/-- The size of a term as written, annotations counted — the measure the truncation needs. -/
def STm.size : STm → Nat
  | .var _ => 1
  | .lam _ A b => STy.size A + STm.size b + 2
  | .app f a => STm.size f + STm.size a + 1
  | .tlam _ b => STm.size b + 2
  | .tapp f A => STm.size f + STy.size A + 1

theorem STy.size_pos : ∀ A : STy, 0 < STy.size A
  | .var _ => by simp [STy.size]
  | .arr _ _ => by simp [STy.size]
  | .all _ _ => by simp [STy.size]

/-- What each entry parses into. -/
def SFC : SFEnt → Type
  | .tm => STm
  | .var => SName
  | .ty => STy

/-- The truncation instructions: parentheses vanish in all three entries. -/
def sfRules : Rules sfGrammar SFC where
  var {e} t h :=
    match e, h with
    | .tm, h => Named.Tm.var ⟨t, h⟩
    | .var, h => ⟨t, h⟩
    | .ty, h => Named.Ty.var ⟨t, h⟩
  op {e} o vs :=
    match e, o, vs with
    | .tm, .paren, (t, _)       => t
    | .tm, .app,   (f, a, _)    => .app f a
    | .tm, .tapp,  (f, A, _)    => .tapp f A
    | .tm, .lam,   (x, A, b, _) => .lam x A b
    | .tm, .tlam,  (α, b, _)    => .tlam α b
    | .var, .paren, (x, _)      => x
    | .ty, .paren, (A, _)       => A
    | .ty, .arrow, (a, b, _)    => .arr a b
    | .ty, .all,   (α, A, _)    => .all α A
  dest {e} x :=
    match e, x with
    | .tm, Named.Tm.var x     => .var x.1 x.2
    | .tm, Named.Tm.app f a   => .node .app (f, a, PUnit.unit)
    | .tm, Named.Tm.tapp f A  => .node .tapp (f, A, PUnit.unit)
    | .tm, Named.Tm.lam x A b => .node .lam (x, A, b, PUnit.unit)
    | .tm, Named.Tm.tlam α b  => .node .tlam (α, b, PUnit.unit)
    | .var, x => .var x.1 x.2
    | .ty, Named.Ty.var x     => .var x.1 x.2
    | .ty, Named.Ty.arr a b   => .node .arrow (a, b, PUnit.unit)
    | .ty, Named.Ty.all α A   => .node .all (α, A, PUnit.unit)
  parenOp | .tm => TmSym.paren | .var => VarSym.paren | .ty => TySym.paren
  lp _ := tkSF "("
  rp _ := tkSF ")"
  paren_eq | .tm => rfl | .var => rfl | .ty => rfl
  holesOk := by intro e o; cases e <;> cases o <;> decide
  topOk := by intro e o; cases e <;> cases o <;> decide
  alg_dest := by
    intro e x
    cases e
    · cases x <;> rfl
    · rfl
    · cases x <;> rfl
  op_paren := by intro e y; cases e <;> rfl
  size {e} :=
    match e with
    | .tm => STm.size
    | .var => fun _ => 1
    | .ty => STy.size
  dest_size := by
    intro e x
    cases e
    · cases x with
      | var x => trivial
      | app f a => exact ⟨by simp +arith [STm.size], by simp +arith [STm.size], trivial⟩
      | tapp f A => exact ⟨by simp +arith [STm.size], by simp +arith [STm.size], trivial⟩
      | lam x A b =>
          refine ⟨?_, by simp +arith [STm.size], by simp +arith [STm.size], trivial⟩
          have := STy.size_pos A
          show 1 < STm.size (.lam x A b)
          simp only [STm.size]
          omega
      | tlam α b =>
          refine ⟨?_, by simp +arith [STm.size], trivial⟩
          show 1 < STm.size (.tlam α b)
          simp only [STm.size]
          omega
    · trivial
    · cases x with
      | var x => trivial
      | arr a b => exact ⟨by simp +arith [STy.size], by simp +arith [STy.size], trivial⟩
      | all α A =>
          refine ⟨?_, by simp +arith [STy.size], trivial⟩
          have := STy.size_pos A
          show 1 < STy.size (.all α A)
          simp only [STy.size]
          omega

/-! ## Term and type parsers -/

/-- A type must stop at `:=` (in `def`) and at the next declaration's keyword (in `type`). -/
theorem sfFollow_ty : ∀ t ∈ [kwAssignF, kwDefF, kwTypeF], follow (G := sfGrammar) SFEnt.ty t = true := by
  decide

/-- A term must stop at the next declaration's keyword. -/
theorem sfFollow_tm : ∀ t ∈ [kwDefF, kwTypeF], follow (G := sfGrammar) SFEnt.tm t = true := by
  decide

/-- Every spelling of a type. -/
abbrev STy.Ann (x : STy) : Type := { t : Expr sfGrammar SFEnt.ty .loosest // truncExpr sfRules t = x }

/-- Every spelling of a term. -/
abbrev STm.Ann (x : STm) : Type := { t : Expr sfGrammar SFEnt.tm .loosest // truncExpr sfRules t = x }

def sfTy : LossyParser SFTok anyTok (· ∈ [kwAssignF, kwDefF, kwTypeF]) STy STy.Ann :=
  ((mixfix (G := sfGrammar) SFEnt.ty .loosest).weakenFollow sfFollow_ty
    |> sfRules.truncateParser) (fun _ => rfl)

def sfTm : LossyParser SFTok anyTok (· ∈ [kwDefF, kwTypeF]) STm STm.Ann :=
  ((mixfix (G := sfGrammar) SFEnt.tm .loosest).weakenFollow sfFollow_tm
    |> sfRules.truncateParser) (fun _ => rfl)

theorem sfTy_exact : sfTy.Exact :=
  Rules.truncateParser_exact sfRules (fun _ => rfl)
    (IsoParser.weakenFollow_exact _ (mixfix_exact _ _))

theorem sfTm_exact : sfTm.Exact :=
  Rules.truncateParser_exact sfRules (fun _ => rfl)
    (IsoParser.weakenFollow_exact _ (mixfix_exact _ _))

/-! ## Declarations -/

/-- The two declaration forms. -/
inductive SFForm | defn | tydef
  deriving DecidableEq, Repr

/-- `def NAME : TYPE := TERM`. -/
structure DefBody where
  name : SName
  ty : STy
  tm : STm

/-- `type NAME := TYPE`. -/
structure TypeBody where
  name : SName
  ty : STy

/-- A declaration. -/
inductive SDecl where
  | defn : SName → STy → STm → SDecl
  | tydef : SName → STy → SDecl

abbrev DefBody.Ann (b : DefBody) : Type := b.ty.Ann × b.tm.Ann
abbrev TypeBody.Ann (b : TypeBody) : Type := b.ty.Ann

/-- What follows `def`. -/
def defBodyIso :
    IsoParser SFTok anyTok (· ∈ [kwDefF, kwTypeF]) (Σ b : DefBody, b.Ann) DefBody :=
  IsoParser.enlargeFirst (fun _ h => absurd trivial h) <| gdo
    let n ← comap (fun s => s.1.name) (sat isSFName)
    let _c ← tok (tkSF ":")
    let A ← comap (fun s => ⟨s.1.ty, s.2.1⟩) sfTy.toIsoParser
    let _a ← tok kwAssignF
    let t ← comap (fun s => ⟨s.1.tm, s.2.2⟩) sfTm.toIsoParser
    return DefBody.mk n A t

theorem defBodyIso_echo : ∀ s : Σ b : DefBody, b.Ann, (defBodyIso.print s).1 = s.1
  | ⟨⟨_, _, _⟩, _⟩ => rfl

def defBody : LossyParser SFTok anyTok (· ∈ [kwDefF, kwTypeF]) DefBody DefBody.Ann :=
  defBodyIso.toLossyParserSigma (fun {_} => (sfTy.default, sfTm.default)) defBodyIso_echo

/-- What follows `type`. A type there ends the declaration, so its FOLLOW is narrowed to the
keywords. -/
def typeBodyIso :
    IsoParser SFTok anyTok (· ∈ [kwDefF, kwTypeF]) (Σ b : TypeBody, b.Ann) TypeBody :=
  IsoParser.enlargeFirst (fun _ h => absurd trivial h) <| gdo
    let n ← comap (fun s => s.1.name) (sat isSFName)
    let _a ← tok kwAssignF
    let A ← comap (fun s => ⟨s.1.ty, s.2⟩)
      (sfTy.toIsoParser.weakenFollow (fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
        rcases hc with rfl | rfl <;> simp))
    return TypeBody.mk n A

theorem typeBodyIso_echo : ∀ s : Σ b : TypeBody, b.Ann, (typeBodyIso.print s).1 = s.1
  | ⟨⟨_, _⟩, _⟩ => rfl

def typeBody : LossyParser SFTok anyTok (· ∈ [kwDefF, kwTypeF]) TypeBody TypeBody.Ann :=
  typeBodyIso.toLossyParserSigma (fun {_} => sfTy.default) typeBodyIso_echo

def SFForm.head : SFForm → SFTok
  | .defn => kwDefF
  | .tydef => kwTypeF

def SFForm.Body : SFForm → Type
  | .defn => DefBody
  | .tydef => TypeBody

def SFForm.BodyAnn : (f : SFForm) → f.Body → Type
  | .defn => DefBody.Ann
  | .tydef => TypeBody.Ann

def SFForm.body : (f : SFForm) →
    LossyParser SFTok anyTok (· ∈ [kwDefF, kwTypeF]) f.Body f.BodyAnn
  | .defn => defBody
  | .tydef => typeBody

def SDecl.toSigma : SDecl → Σ f : SFForm, f.Body
  | .defn x A t => ⟨.defn, ⟨x, A, t⟩⟩
  | .tydef α A => ⟨.tydef, ⟨α, A⟩⟩

def SDecl.ofSigma : (Σ f : SFForm, f.Body) → SDecl
  | ⟨.defn, b⟩ => .defn b.name b.ty b.tm
  | ⟨.tydef, b⟩ => .tydef b.name b.ty

/-- **The System F language**: two forms, `def` and `type`. -/
def systemFLanguage : Language where
  lex := sfLex
  Form := SFForm
  forms := [.defn, .tydef]
  forms_complete f := by cases f <;> decide
  head := SFForm.head
  head_injective f g h := by
    cases f <;> cases g <;> first | rfl | exact absurd h (by decide)
  Body := SFForm.Body
  BodyAnn := SFForm.BodyAnn
  body := SFForm.body
  Decl := SDecl
  decl := ⟨SDecl.toSigma, SDecl.ofSigma, by intro d; cases d <;> rfl,
    by rintro ⟨f, b⟩; cases f <;> rfl⟩

end LambdaLab.Languages.SystemF
