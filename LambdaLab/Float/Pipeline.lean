import LambdaLab.Pipeline.Compose
import LambdaLab.Float.Decimal
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.IsoParser.Mixfix.Unambiguity
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Parser.Truncation
import LambdaLab.Parser.Truncation.Mixfix

/-!
# `float` — numbers, and nothing else

A language with no type system: a file is a run of

    float NAME := TERM

where a term is decimal literals, `+` and `*`, and parentheses to group them. Running a program
replaces every term by its value:

    float c := ( 1 + 2 ) * 3        ⟹     float c := 9

It is a `Language` written directly — one declaration form, keyword `float` — and not a
`DefLanguage`: there is no type to declare, so there is no `: TYPE`, and nothing here mentions a
type system. Its semantics is one walk (`Semantics/Walk.lean`) whose state is a map from names to
values.

## The pieces

* **terms** come from the mixfix engine, as arithmetic does: literals are the grammar's atoms, `*`
  binds tighter than `+`, both associate to the left. The parse tree still holds the parentheses;
  the `Rules` bundle truncates it to `FTm`, which has none, so `( ( 7 ) )` is read as `7` and the
  parentheses come back only where the grammar needs them.
* **the declaration** is `NAME := TERM` after the keyword: a `gdo` block, like `def`'s body.
* **evaluation** computes each term exactly (`Decimal`), records the name's value in the state,
  and writes the value back as a literal. Its one law, idempotence, holds a step at a time: a
  literal evaluates to the value it spells (`Decimal.ofToken_toToken`), and every computed value is
  already normalized.

Terms have no variables, so nothing reads the map yet. It is the state the walk carries, and the
place a term referring to an earlier declaration would look its value up.
-/

namespace LambdaLab.Float

open LambdaLab.Parser.IsoParser LambdaLab.Parser.IsoParser.Mixfix LambdaLab.Pipeline
open LambdaLab.Parser.LossyParser (LossyParser)
open LambdaLab.Parser.Truncation.Mixfix (Rules truncExpr)
open LambdaLab.Semantics (Walk)

/-- A token literal of the shared alphabet. -/
def tkF (s : String) (h : isToken isSep s = true := by decide) : Token := ⟨s, h⟩

/-- The keyword that starts every declaration. -/
def kwFloat : Token := tkF "float"

/-- The assignment between a declaration's name and its term. -/
def assignTok : Token := tkF ":="

/-! ## Terms: literals, `+`, `*` -/

/-- Operators: parentheses, `_ * _`, `_ + _`. -/
inductive FSym | paren | times | plus
  deriving DecidableEq, Repr

def fTighter : FSym → List FSym
  | .plus  => [.times]
  | .times => [.paren]
  | .paren => []

def fRank : FSym → Nat
  | .paren => 0 | .times => 1 | .plus => 2

def fOp : FSym → Operator Token Unit
  | .paren => .closed (.cons (tkF "(") () (.last (tkF ")")))
  | .times => .infxl (.last (tkF "*"))
  | .plus  => .infxl (.last (tkF "+"))

/-- The term grammar's one entry. Its atoms are the decimal literals. -/
def fEntry : Entry Token Unit where
  Op := FSym
  operator := fOp
  ops := [.paren, .times, .plus]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.plus]
  tighter := fTighter
  rank := fRank
  topRank := 3
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all [fTighter, fRank]
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := Decimal.isDecimalTok
  headsDistinct := by
    intro o₁ o₂ h₁ h
    cases o₁ <;> cases o₂ <;>
      simp_all [fOp, Operator.headTok?, Operator.nameTokens, Notation.toTokens] <;>
      exact absurd h (by decide)
  juxtUnique := by
    intro o₁ o₂ h₁ h₂
    cases o₁ <;> cases o₂ <;> simp_all [fOp]
  varDisjoint := by
    intro o t ht
    cases o <;>
      simp only [fOp, Operator.nameTokens, Notation.toTokens,
        List.mem_cons, List.not_mem_nil, or_false] at ht <;>
      first
        | (rcases ht with rfl | rfl <;> decide)

def fGrammar : Grammar Token where
  Ent := Unit
  entry := fun _ => fEntry
  interiorTerminates := by
    intro e o e' t h
    cases e <;> cases e' <;> cases o <;>
      simp only [fEntry, fOp, Operator.holeFollowers, Notation.holeFollowers,
        Notation.firstTok] at h <;>
      cases h <;>
      first
        | (refine ⟨by decide, ?_⟩; intro o'; cases o' <;> decide)
        | (rename_i h'; cases h')

/-- The term grammar is unambiguous — derived from its lexical fields, not assumed. -/
theorem fUnambiguous : Unambiguous fGrammar := unambiguous fGrammar

/-- A term: what `Expr fGrammar` is *about*, with the parentheses gone. -/
inductive FTm where
  | lit : (t : Token) → Decimal.isDecimalTok t = true → FTm
  | add : FTm → FTm → FTm
  | mul : FTm → FTm → FTm

/-- TC will not unfold `fGrammar.entry e` to `fEntry` (nor `.Op` to `FSym`) by itself, so hand it
the instances in the exact projected forms the generic machinery asks for. -/
instance : DecidableEq fEntry.Op := inferInstanceAs (DecidableEq FSym)
instance : ∀ e : fGrammar.Ent, DecidableEq (fGrammar.entry e).Op :=
  fun _ => inferInstanceAs (DecidableEq FSym)

/-- A structural size (constructor counts one) — `omega`-friendly, unlike the opaque `sizeOf`. -/
def FTm.size : FTm → Nat
  | .lit _ _ => 1
  | .add a b => a.size + b.size + 1
  | .mul a b => a.size + b.size + 1

/-- The truncation instructions: one clause per operator each way, plus the paren designation and
the bookkeeping laws. -/
def fRules : Rules fGrammar (fun _ => FTm) where
  var t h := .lit t h
  op o vs :=
    match o, vs with
    | .paren, (e, _)    => e
    | .times, (a, b, _) => .mul a b
    | .plus,  (a, b, _) => .add a b
  dest x :=
    match x with
    | .lit t h => .var t h
    | .mul a b => .node .times (a, b, PUnit.unit)
    | .add a b => .node .plus (a, b, PUnit.unit)
  parenOp _ := .paren
  lp _ := tkF "("
  rp _ := tkF ")"
  paren_eq _ := rfl
  holesOk := by rintro ⟨⟩ o; cases o <;> decide
  topOk := by rintro ⟨⟩ o; cases o <;> decide
  alg_dest := by rintro _ (⟨t, h⟩ | ⟨a, b⟩ | ⟨a, b⟩) <;> rfl
  op_paren _ := rfl
  size := FTm.size
  dest_size := by
    rintro _ (⟨t, h⟩ | ⟨a, b⟩ | ⟨a, b⟩)
    · trivial
    all_goals exact ⟨by simp +arith [FTm.size], by simp +arith [FTm.size], trivial⟩

/-- The term parser stops at the next declaration's keyword. **Derived**, not declared. -/
theorem follow_float : follow (G := fGrammar) () kwFloat = true := by decide

/-- Every spelling of a term: the parse trees that truncate to it. -/
abbrev FTm.Ann (x : FTm) : Type := { t : Expr fGrammar () .loosest // truncExpr fRules t = x }

/-- **The term parser**: the mixfix parser truncated to `FTm`, its FOLLOW narrowed to the keyword
— sound exactly because the keyword is in it (`follow_float`). -/
def fTerm : LossyParser Token anyTok (· ∈ [kwFloat]) FTm FTm.Ann :=
  ((mixfix (G := fGrammar) () .loosest).weakenFollow
    (by
      intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      exact follow_float) |> fRules.truncateParser) (fun _ => rfl)

/-- The term parser accepts only what it prints. -/
theorem fTerm_exact : fTerm.Exact :=
  Rules.truncateParser_exact fRules (fun _ => rfl)
    (IsoParser.weakenFollow_exact _ (mixfix_exact _ _))

/-! ## The declaration: `float NAME := TERM` -/

/-- The tokens a name may not be. -/
def fReserved : List Token := [kwFloat, assignTok, tkF "(", tkF ")", tkF "+", tkF "*"]

/-- A name is any token that is neither reserved nor a number. -/
def isFName (t : Token) : Bool := isFree fReserved t && !Decimal.isDecimalTok t

abbrev FName : Type := { t : Token // isFName t = true }

/-- A declaration: a name and the term it is bound to. -/
structure FDecl where
  name : FName
  value : FTm

/-- A declaration's spellings are its term's: the name and the keywords have one each. -/
abbrev FDecl.Ann (d : FDecl) : Type := FTm.Ann d.value

/-- What follows `float`, at the `IsoParser` level: the **source is the annotated declaration**.
FIRST is widened to `anyTok` (a name is what really starts it), and FOLLOW is the term's. -/
def fBodyIso : IsoParser Token anyTok (· ∈ [kwFloat]) (Σ d : FDecl, d.Ann) FDecl :=
  IsoParser.enlargeFirst (fun _ h => absurd trivial h) <| gdo
    let n ← comap (fun s => s.1.name) (sat isFName)
    let _a ← tok assignTok
    let e ← comap (fun s => ⟨s.1.value, s.2⟩) fTerm.toIsoParser
    return FDecl.mk n e

/-- The body prints the declaration it is indexed by. -/
theorem fBodyIso_echo : ∀ s : Σ d : FDecl, d.Ann, (fBodyIso.print s).1 = s.1
  | ⟨⟨_, _⟩, _⟩ => rfl

/-- **The body, lossy**: value `FDecl`, annotation the term's spelling. -/
def fBody : LossyParser Token anyTok (· ∈ [kwFloat]) FDecl FDecl.Ann :=
  fBodyIso.toLossyParserSigma (fun {_} => fTerm.default) fBodyIso_echo

/-- **The `float` language**: one form, keyword `float`. -/
def floatLanguage : Language where
  Form := Unit
  forms := [()]
  forms_complete _ := List.mem_singleton.mpr rfl
  head _ := kwFloat
  head_injective _ _ _ := rfl
  Body _ := FDecl
  BodyAnn _ := FDecl.Ann
  body _ := fBody
  Decl := FDecl
  decl := ⟨fun d => ⟨(), d⟩, fun s => s.2, fun _ => rfl, fun _ => rfl⟩

/-! ## Evaluation -/

/-- A term's value. -/
def FTm.eval : FTm → Decimal
  | .lit t _ => Decimal.ofToken t
  | .add a b => a.eval.add b.eval
  | .mul a b => a.eval.mul b.eval

/-- Every value a term has is already normalized. -/
theorem FTm.eval_normalize : ∀ e : FTm, e.eval.normalize = e.eval
  | .lit _ _ => Decimal.normalize_normalize _
  | .add _ _ => Decimal.ofMS_normalize _ _
  | .mul _ _ => Decimal.ofMS_normalize _ _

/-- A value, written as a term: its literal. -/
def Decimal.toLit (d : Decimal) : FTm := .lit d.toToken (Decimal.isDecimalTok_toToken d)

/-- A value's literal evaluates to the value, normalized. -/
theorem Decimal.eval_toLit (d : Decimal) : d.toLit.eval = d.normalize := Decimal.ofToken_toToken d

/-- **The state**: the value of every name declared so far. -/
abbrev FState : Type := Std.HashMap String Decimal

/-- **Evaluate one declaration**: compute its term, record the value under its name, and write the
value back as a literal. It never rejects — there is nothing a term of literals, `+` and `*` can
get wrong. -/
def evalStep (s : FState) (d : FDecl) : Option (FDecl × FState) :=
  some (⟨d.name, d.value.eval.toLit⟩, s.insert d.name.val.val d.value.eval)

/-- **The evaluator**: the walk from the empty map. -/
def evalWalk : Walk FDecl where
  State := FState
  init := ∅
  step := evalStep

/-- **Idempotence, a step at a time.** A literal evaluates to the value it spells, so an evaluated
declaration evaluates to itself, and records the same value under the same name. -/
theorem evalWalk_stepIdempotent : evalWalk.StepIdempotent := by
  rintro s ⟨x, e⟩ d' s' h
  simp only [evalWalk, evalStep, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  show evalStep s ⟨x, e.eval.toLit⟩ = _
  simp only [evalStep, Decimal.eval_toLit, FTm.eval_normalize]
  rfl

theorem evalWalk_idempotent : evalWalk.Idempotent :=
  evalWalk.idempotent_of_step evalWalk_stepIdempotent

/-! ## The front end -/

/-- Read a file and evaluate it. -/
def evaluateFile (s : String) : Option evalWalk.Fixed :=
  floatLanguage.walkFile evalWalk evalWalk_idempotent s

/-- Render an evaluated program: every declaration on its own line, its term a literal. -/
def renderEvaluated (q : evalWalk.Fixed) : String :=
  floatLanguage.renderWalked evalWalk evalWalk_idempotent q

/-- **The front end round-trips.** Render an evaluated program and read it back, and evaluation
returns it. -/
theorem evaluateFile_renderEvaluated (q : evalWalk.Fixed) :
    evaluateFile (renderEvaluated q) = some q :=
  floatLanguage.walkFile_renderWalked _ _ q

/-- **The whole front end, stage by stage**: source, tokens, program, evaluated program. -/
def floatChain : Abstraction.Chain sourceStage
    (floatLanguage.walkStage "evaluated program" evalWalk) :=
  floatLanguage.walkChain evalWalk evalWalk_idempotent "evaluated program"

end LambdaLab.Float
