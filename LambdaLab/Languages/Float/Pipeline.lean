import LambdaLab.Pipeline.Compose
import LambdaLab.Languages.Float.Decimal
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.IsoParser.Mixfix.Unambiguity
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Parser.Truncation
import LambdaLab.Parser.Truncation.Mixfix

/-!
# `float` — numbers, named and combined

A language with no type system: a file is a run of

    float NAME := TERM

where a term is built from decimal literals and the names of **earlier** declarations with `+`
and `*`, and parentheses to group them. Running a program replaces every term by its value:

    float a := (1 + 2) * 3          ⟹     float a := 9
    float b := a + 0.5              ⟹     float b := 9.5

It is a `Language` written directly — one declaration form, keyword `float` — and not a
`DefLanguage`: there is no type to declare, so there is no `: TYPE`, and nothing here mentions a
type system. Its semantics is one walk (`Semantics/Walk.lean`) whose state is a map from names to
values.

## The pieces

* **terms** come from the mixfix engine, as arithmetic does. The grammar's atoms are the literals
  and the names, which cannot be confused: a name is never a number (`isFName`). `*` binds tighter
  than `+`, both associate to the left. The parse tree still holds the parentheses; the `Rules`
  bundle truncates it to `FTm`, which has none, so `((7))` is read as `7` and the parentheses
  come back only where the grammar needs them.
* **the declaration** is `NAME := TERM` after the keyword: a `gdo` block, like `def`'s body.
* **evaluation** computes each term exactly (`Decimal`) in the state, records the declaration's
  value under its name, and writes the value back as a literal.

## Only earlier declarations, never itself

A step evaluates its term in the state *as it was before the step*, and records the declaration's
own name only afterwards. So a name in a term means the most recent earlier declaration of that
name, and nothing else:

* `float x := x + 1`, with no earlier `x`, is rejected — the name is unknown, as it would be for
  any other undeclared name, or one declared only further down;
* after `float x := 1`, the same declaration is accepted and means `2`: its `x` is the earlier one.
  Redeclaring a name shadows it from then on.

There is no recursion to rule out, because nothing a step can see includes itself.

## The law

Evaluation is idempotent a step at a time. What a step writes is a literal, and a literal evaluates
to the value it spells (`Decimal.ofToken_toToken`) without consulting the state; every value a term
has is normalized (`FTm.eval_normalize`), so it is the very value the step recorded.
-/

namespace LambdaLab.Languages.Float

open LambdaLab.Parser.IsoParser LambdaLab.Parser.IsoParser.Mixfix LambdaLab.Pipeline
open LambdaLab.Parser.LossyParser (LossyParser)
open LambdaLab.Parser.Truncation.Mixfix (Rules truncExpr)
open LambdaLab.Semantics (Walk)

/-! ## The lexicon

Parentheses, `+` and `*` are self-delimiting, so `(1+2)*x` reads exactly as `( 1 + 2 ) * x` does,
and the canonical printer hugs the parentheses and spaces the operators: `(1 + 2) * x`. Every other
non-whitespace character is a word character — digits and `.` among them, so a literal is one token
(`floatWords`), and so is `:=`. -/

/-- What a token is, for `float`. -/
abbrev floatLex : Lexicon := Lexicon.make ['('] [')'] ['+', '*']

abbrev FTok : Type := Token floatLex

/-- A decimal literal is a single word. -/
theorem floatWords : Decimal.Words floatLex := ⟨Lexicon.make_digit_word, by decide⟩

/-- A token literal. -/
def tkF (s : String) (h : isToken floatLex s = true := by decide) : FTok := ⟨s, h⟩

/-- The keyword that starts every declaration. -/
def kwFloat : FTok := tkF "float"

/-- The assignment between a declaration's name and its term. -/
def assignTok : FTok := tkF ":="

/-! ## Names -/

/-- The tokens a name may not be. -/
def fReserved : List FTok := [kwFloat, assignTok, tkF "(", tkF ")", tkF "+", tkF "*"]

/-- A name is any token that is neither reserved nor a number. -/
def isFName (t : FTok) : Bool := isFree fReserved t && !Decimal.isDecimalTok t

abbrev FName : Type := { t : FTok // isFName t = true }

theorem not_decimal_of_name {t : FTok} (h : isFName t = true) :
    ¬ Decimal.isDecimalTok t = true := by
  simp only [isFName, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp [h.2]

/-- The grammar's atoms: literals and names. -/
def isAtom (t : FTok) : Bool := Decimal.isDecimalTok t || isFName t

theorem isAtom_of_decimal {t : FTok} (h : Decimal.isDecimalTok t = true) : isAtom t = true := by
  simp [isAtom, h]

theorem isAtom_of_name {t : FTok} (h : isFName t = true) : isAtom t = true := by
  simp [isAtom, h]

theorem isFName_of_atom {t : FTok} (h : isAtom t = true) (hd : ¬ Decimal.isDecimalTok t = true) :
    isFName t = true := by
  simp only [isAtom, Bool.or_eq_true] at h
  exact h.resolve_left hd

/-! ## Terms: literals, names, `+`, `*` -/

/-- Operators: parentheses, `_ * _`, `_ + _`. -/
inductive FSym | paren | times | plus
  deriving DecidableEq, Repr

def fTighter : FSym → List FSym
  | .plus  => [.times]
  | .times => [.paren]
  | .paren => []

def fRank : FSym → Nat
  | .paren => 0 | .times => 1 | .plus => 2

def fOp : FSym → Operator FTok Unit
  | .paren => .closed (.cons (tkF "(") () (.last (tkF ")")))
  | .times => .infxl (.last (tkF "*"))
  | .plus  => .infxl (.last (tkF "+"))

/-- The term grammar's one entry. Its atoms are the literals and the names. -/
def fEntry : Entry FTok Unit where
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
  isVar := isAtom
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

def fGrammar : Grammar FTok where
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
  | lit : (t : FTok) → Decimal.isDecimalTok t = true → FTm
  | ref : FName → FTm
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
  | .ref _ => 1
  | .add a b => a.size + b.size + 1
  | .mul a b => a.size + b.size + 1

/-- The truncation instructions: an atom is a literal if it is a number and a name otherwise, one
clause per operator each way, plus the paren designation and the bookkeeping laws. -/
def fRules : Rules fGrammar (fun _ => FTm) where
  var t h :=
    if hd : Decimal.isDecimalTok t = true then .lit t hd else .ref ⟨t, isFName_of_atom h hd⟩
  op o vs :=
    match o, vs with
    | .paren, (e, _)    => e
    | .times, (a, b, _) => .mul a b
    | .plus,  (a, b, _) => .add a b
  dest x :=
    match x with
    | .lit t h => .var t (isAtom_of_decimal h)
    | .ref x => .var x.val (isAtom_of_name x.property)
    | .mul a b => .node .times (a, b, PUnit.unit)
    | .add a b => .node .plus (a, b, PUnit.unit)
  parenOp _ := .paren
  lp _ := tkF "("
  rp _ := tkF ")"
  paren_eq _ := rfl
  holesOk := by rintro ⟨⟩ o; cases o <;> decide
  topOk := by rintro ⟨⟩ o; cases o <;> decide
  alg_dest := by
    rintro _ (⟨t, h⟩ | x | ⟨a, b⟩ | ⟨a, b⟩)
    · exact dif_pos h
    · exact dif_neg (not_decimal_of_name x.property)
    · rfl
    · rfl
  op_paren _ := rfl
  size := FTm.size
  dest_size := by
    rintro _ (⟨t, h⟩ | x | ⟨a, b⟩ | ⟨a, b⟩)
    · trivial
    · trivial
    all_goals exact ⟨by simp +arith [FTm.size], by simp +arith [FTm.size], trivial⟩

/-- The term parser stops at the next declaration's keyword. **Derived**, not declared. -/
theorem follow_float : follow (G := fGrammar) () kwFloat = true := by decide

/-- Every spelling of a term: the parse trees that truncate to it. -/
abbrev FTm.Ann (x : FTm) : Type := { t : Expr fGrammar () .loosest // truncExpr fRules t = x }

/-- **The term parser**: the mixfix parser truncated to `FTm`, its FOLLOW narrowed to the keyword
— sound exactly because the keyword is in it (`follow_float`). -/
def fTerm : LossyParser FTok anyTok (· ∈ [kwFloat]) FTm FTm.Ann :=
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

/-- A declaration: a name and the term it is bound to. -/
structure FDecl where
  name : FName
  value : FTm

/-- A declaration's spellings are its term's: the name and the keywords have one each. -/
abbrev FDecl.Ann (d : FDecl) : Type := FTm.Ann d.value

/-- What follows `float`, at the `IsoParser` level: the **source is the annotated declaration**.
FIRST is widened to `anyTok` (a name is what really starts it), and FOLLOW is the term's. -/
def fBodyIso : IsoParser FTok anyTok (· ∈ [kwFloat]) (Σ d : FDecl, d.Ann) FDecl :=
  IsoParser.enlargeFirst (fun _ h => absurd trivial h) <| gdo
    let n ← comap (fun s => s.1.name) (sat isFName)
    let _a ← tok assignTok
    let e ← comap (fun s => ⟨s.1.value, s.2⟩) fTerm.toIsoParser
    return FDecl.mk n e

/-- The body prints the declaration it is indexed by. -/
theorem fBodyIso_echo : ∀ s : Σ d : FDecl, d.Ann, (fBodyIso.print s).1 = s.1
  | ⟨⟨_, _⟩, _⟩ => rfl

/-- **The body, lossy**: value `FDecl`, annotation the term's spelling. -/
def fBody : LossyParser FTok anyTok (· ∈ [kwFloat]) FDecl FDecl.Ann :=
  fBodyIso.toLossyParserSigma (fun {_} => fTerm.default) fBodyIso_echo

/-- **The `float` language**: one form, keyword `float`. -/
def floatLanguage : Language where
  lex := floatLex
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

/-- **The state**: the value of every name declared so far. -/
abbrev FState : Type := Std.HashMap String Decimal

/-- A term's value in a state — `none` if it names something the state does not hold. -/
def FTm.eval (s : FState) : FTm → Option Decimal
  | .lit t _ => some (Decimal.ofToken t)
  | .ref x => (s.get? x.val.val).map Decimal.normalize
  | .add a b =>
      match a.eval s, b.eval s with
      | some u, some v => some (u.add v)
      | _, _ => none
  | .mul a b =>
      match a.eval s, b.eval s with
      | some u, some v => some (u.mul v)
      | _, _ => none

/-- Every value a term has is normalized — whatever the state holds. -/
theorem FTm.eval_normalize (s : FState) :
    ∀ {e : FTm} {v : Decimal}, e.eval s = some v → v.normalize = v
  | .lit _ _, _, h => by
      simp only [FTm.eval, Option.some.injEq] at h
      subst h
      exact Decimal.normalize_normalize _
  | .ref _, _, h => by
      simp only [FTm.eval, Option.map_eq_some_iff] at h
      obtain ⟨w, _, rfl⟩ := h
      exact Decimal.normalize_normalize w
  | .add _ _, _, h => by
      simp only [FTm.eval] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact Decimal.add_normalize _ _
      · exact absurd h (by simp)
  | .mul _ _, _, h => by
      simp only [FTm.eval] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact Decimal.mul_normalize _ _
      · exact absurd h (by simp)

/-- A value, written as a term: its literal. -/
def Decimal.toLit (d : Decimal) : FTm :=
  .lit (d.toToken floatWords) (Decimal.isDecimalTok_toToken floatWords d)

/-- A value's literal evaluates to the value, normalized, in any state. -/
theorem Decimal.eval_toLit (d : Decimal) (s : FState) : d.toLit.eval s = some d.normalize := by
  simp only [Decimal.toLit, FTm.eval, Decimal.ofToken_toToken]

/-- The first name a term mentions that the state does not hold — for a diagnostic. -/
def FTm.unknownName (s : FState) : FTm → Option String
  | .lit _ _ => none
  | .ref x => if s.contains x.val.val then none else some x.val.val
  | .add a b => (a.unknownName s).or (b.unknownName s)
  | .mul a b => (a.unknownName s).or (b.unknownName s)

/-- **Evaluate one declaration**: compute its term in the state as it stands — which holds only the
declarations before this one — record the value under the declaration's name, and write the value
back as a literal. A term naming anything the state does not hold is rejected. -/
def evalStep (s : FState) (d : FDecl) : Except String (FDecl × FState) :=
  match d.value.eval s with
  | some v => .ok (⟨d.name, v.toLit⟩, s.insert d.name.val.val v)
  | none =>
      .error <| match d.value.unknownName s with
        | some x => s!"unknown name `{x}`: it is not declared before this declaration"
        | none => "this declaration cannot be evaluated"

/-- **The evaluator**: the walk from the empty map. -/
def evalWalk : Walk FDecl where
  State := FState
  init := ∅
  step := evalStep

/-- **Idempotence, a step at a time.** An evaluated declaration's term is a literal, which
evaluates to the value it spells without consulting the state — so the declaration evaluates to
itself, and records the same value under the same name. -/
theorem evalWalk_stepIdempotent : evalWalk.StepIdempotent := by
  rintro s ⟨x, e⟩ d' s' h
  change evalStep s ⟨x, e⟩ = .ok (d', s') at h
  simp only [evalStep] at h
  split at h
  · rename_i v he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    have hv : v.normalize = v := FTm.eval_normalize s he
    show evalStep s ⟨x, v.toLit⟩ = .ok (⟨x, v.toLit⟩, s.insert x.val.val v)
    simp only [evalStep, Decimal.eval_toLit, hv]
  · cases h

theorem evalWalk_idempotent : evalWalk.Idempotent :=
  evalWalk.idempotent_of_step evalWalk_stepIdempotent

/-! ## The front end -/

/-- Read a file and evaluate it. -/
def evaluateFile (s : String) : Except Diag evalWalk.Fixed :=
  floatLanguage.walkFile evalWalk evalWalk_idempotent s

/-- Render an evaluated program: every declaration on its own line, its term a literal. -/
def renderEvaluated (q : evalWalk.Fixed) : String :=
  floatLanguage.renderWalked evalWalk evalWalk_idempotent q

/-- **The front end round-trips.** Render an evaluated program and read it back, and evaluation
returns it. -/
theorem evaluateFile_renderEvaluated (q : evalWalk.Fixed) :
    evaluateFile (renderEvaluated q) = .ok q :=
  floatLanguage.walkFile_renderWalked _ _ q

/-- **The whole front end, stage by stage**: source, tokens, program, evaluated program. -/
def floatChain : Abstraction.Chain sourceStage
    (floatLanguage.walkStage "evaluated program" evalWalk) :=
  floatLanguage.walkChain evalWalk evalWalk_idempotent "evaluated program"

end LambdaLab.Languages.Float
