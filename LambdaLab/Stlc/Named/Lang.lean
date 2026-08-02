import LambdaLab.Stlc.Named.Basic
import LambdaLab.Stlc.Named.Typing.Unification
import LambdaLab.Stlc.Named.Typing.Infer
import LambdaLab.Stlc.Named.Typing.Target
import LambdaLab.Language.ElabStage
import LambdaLab.Language.Biparser
import LambdaLab.Language.FreeName
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Parser.Truncation.Mixfix
import LambdaLab.Parser.Numeral

/-!
# STLC as a `Language.Language` — types land in `Stlc.Ty`

The lambda-calculus instance. Two things make the surface *complete* for the semantic types,
which is what lets the type parser produce `Stlc.Ty` itself rather than a syntax tree:

* **metavariables are writable** — `?0`, `?7` denote `Ty.mvar 0`, `Ty.mvar 7`. Together with `⋆`
  (`Ty.base`) and `→` (`Ty.arrow`) the surface reaches *every* constructor of `Ty`, which is
  exactly the condition `Rules.alg_dest` needs: destructing a value and rebuilding it from its
  spelling must be the identity, so no constructor may be unspellable.
* **binder annotations are mandatory** — `λ x : T . e`. The surface therefore determines the
  annotation, instead of the parser having to invent one.

Nobody writes `?7` by hand; the intended surface for "infer this" is `_`, which is deliberately
*not* here yet. `_` cannot join the lossless core — it does not determine an index — so it
belongs in a lossy layer above, whose annotation records which binders were elided — an
`annotated | infer` split, with the elision living in the annotation rather than the value.

## The parser lands in `Term` itself

There is no surface AST. `Term` is parametric in its name alphabet (`Stlc/Named/Basic.lean`), so
terms parse into `Term VName`, named by the non-reserved tokens — and `VName` is `FreeName
sReserved`, whose `NameAlphabet` instance `Language/FreeName.lean` proves once for every
language.

That closes the last gap. `Term String` would *not* work: `Term.var "def"` and `Term.var ""`
exist and have no spelling, so `Term String` is wider than the printable set. Restricting the
name type — rather than wrapping terms in a subtype or duplicating the AST — is what makes the
value type exactly what the token string determines.

The grammar is a single three-entry grammar — terms, binders, types — so `pTm` and `pTy` are the
same engine at different entries, and the binder's `: T` is an ordinary cross-entry hole.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Parser.IsoParser LambdaLab.Parser.IsoParser.Mixfix LambdaLab.Language
open LambdaLab.Parser.Truncation.Mixfix
open LambdaLab.Parser.Numeral (isDigitChar isNatTok natTok natOfTok)

/-! ## The token alphabet -/

def tkS (s : String) (h : isToken isSep s = true := by decide) : Language.Token := ⟨s, h⟩

/-- Grammar name-parts and vernacular keywords: never variables. -/
def sReserved : List Language.Token :=
  [tkS "(", tkS ")", tkS "λ", tkS ".", tkS ":", tkS "→", tkS "⋆", tkS "def", tkS ":="]

abbrev isVarTok (t : Language.Token) : Bool := isFree sReserved t

/-- Digits are separator-free for this vernacular (`isSep` is whitespace). -/
theorem digit_not_sep : ∀ c, isDigitChar c = true → isSep c = false :=
  fun _ h => LambdaLab.Parser.Numeral.isDigitChar_not_whitespace h

/-- `?` followed by at least one decimal digit. -/
def isMvarTok (t : Language.Token) : Bool := isNatTok '?' t

/-- Type atoms: the base type `⋆`, and metavariables `?n`. -/
def isTyAtom (t : Language.Token) : Bool := (t.val == "⋆") || isMvarTok t

/-- The token spelling `?n`. -/
def mvarTok (n : Nat) : Language.Token := natTok '?' (by decide) digit_not_sep n

/-- Read the index back out of a `?n` token. -/
def tokMvar (t : Language.Token) : Nat := natOfTok t

theorem tokMvar_mvarTok (n : Nat) : tokMvar (mvarTok n) = n :=
  LambdaLab.Parser.Numeral.natOfTok_natTok _ _ _ n

theorem isMvarTok_mvarTok (n : Nat) : isMvarTok (mvarTok n) = true :=
  LambdaLab.Parser.Numeral.isNatTok_natTok _ _ _ n

theorem isTyAtom_mvarTok (n : Nat) : isTyAtom (mvarTok n) = true := by
  simp [isTyAtom, isMvarTok_mvarTok n]

/-! ## The grammar: three entries — terms, binders, types -/

inductive SEnt | tm | var | ty
  deriving DecidableEq, Repr

inductive SSym | paren | app | lam
  deriving DecidableEq, Repr
inductive BSym | paren
  deriving DecidableEq, Repr
inductive TSym | paren | arrow
  deriving DecidableEq, Repr

def tmEntry : Entry Language.Token SEnt where
  Op := SSym
  operator
    | .paren => .closed (.cons (tkS "(") .tm (.last (tkS ")")))
    | .app   => .juxt
    | .lam   => .prefx (.cons (tkS "λ") .var (.cons (tkS ":") .ty (.last (tkS "."))))
  ops := [.paren, .app, .lam]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.lam]
  tighter | .lam => [.app] | .app => [.paren] | .paren => []
  rank | .paren => 0 | .app => 1 | .lam => 2
  topRank := 3
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := isVarTok
  headsDistinct := by
    intro o₁ o₂ h₁ h
    cases o₁ <;> cases o₂ <;>
      simp_all [Operator.headTok?, Operator.nameTokens, Notation.toTokens] <;>
      exact absurd h (by decide)
  varDisjoint := by
    intro o t ht
    cases o <;>
      simp only [Operator.nameTokens, Notation.toTokens,
        List.mem_cons, List.not_mem_nil, or_false] at ht <;>
      first
        | (rcases ht with rfl | rfl <;> decide)
        | (rcases ht with rfl | rfl | rfl <;> decide)
        | (subst ht; decide)
        | exact ht.elim

def varEntry : Entry Language.Token SEnt where
  Op := BSym
  operator | .paren => .closed (.cons (tkS "(") .var (.last (tkS ")")))
  ops := [.paren]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.paren]
  tighter | .paren => []
  rank | .paren => 0
  topRank := 1
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := isVarTok
  headsDistinct := by
    intro o₁ o₂ h₁ h
    cases o₁ <;> cases o₂ <;> rfl
  varDisjoint := by
    intro o t ht
    cases o <;>
      simp only [Operator.nameTokens, Notation.toTokens,
        List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> decide

def tyEntry : Entry Language.Token SEnt where
  Op := TSym
  operator
    | .paren => .closed (.cons (tkS "(") .ty (.last (tkS ")")))
    | .arrow => .infxr (.last (tkS "→"))
  ops := [.paren, .arrow]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.arrow]
  tighter | .arrow => [.paren] | .paren => []
  rank | .paren => 0 | .arrow => 1
  topRank := 2
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := isTyAtom
  headsDistinct := by
    intro o₁ o₂ h₁ h
    cases o₁ <;> cases o₂ <;>
      simp_all [Operator.headTok?, Operator.nameTokens, Notation.toTokens] <;>
      exact absurd h (by decide)
  varDisjoint := by
    intro o t ht
    cases o <;>
      simp only [Operator.nameTokens, Notation.toTokens,
        List.mem_cons, List.not_mem_nil, or_false] at ht <;>
      first
        | (rcases ht with rfl | rfl <;> decide)
        | (subst ht; decide)
        | exact ht.elim

def stlcGrammar : Grammar Language.Token where
  Ent := SEnt
  entry | .tm => tmEntry | .var => varEntry | .ty => tyEntry
  interiorTerminates := by
    intro e o e' t h
    cases e <;> cases e' <;> cases o <;>
      simp only [tmEntry, varEntry, tyEntry, Operator.holeFollowers, Notation.holeFollowers,
        Notation.firstTok] at h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, reduceCtorEq,
        false_and, and_false, false_or, or_false, true_and, and_true] at h <;>
      first
        | exact h.elim
        | (subst h; exact ⟨by decide, by intro o'; cases o' <;> decide⟩)

instance : ∀ e : stlcGrammar.Ent, DecidableEq (stlcGrammar.entry e).Op
  | .tm => inferInstanceAs (DecidableEq SSym)
  | .var => inferInstanceAs (DecidableEq BSym)
  | .ty => inferInstanceAs (DecidableEq TSym)

/-! ## Surface terms, and the truncation into them -/

/-- Binder names: any token the grammar has not reserved. Being a `FreeName`, this is a
`NameAlphabet` with no proof obligation here — `Language/FreeName.lean` discharges it once for
every language. -/
abbrev VName := FreeName sReserved

/-- So `Term VName` is `Repr`-able (the derived instance needs one for the name type). -/
instance : Repr VName := ⟨fun v _ => repr v.1.val⟩

/-! Terms parse **directly into `Term VName`** — the STLC term type, named by non-reserved
tokens. There is no surface AST: `?n` makes every `Ty` spellable and the mandatory binder
annotation means the parser invents nothing, so `Term` itself round-trips.

The measure below is the one `Rules.dest_size` needs and is *not* `Term.size`: the lam node's
operands now include the annotation `τ`, so the measure has to dominate `Ty.size τ` as well.
`Rules.size` is a field of the bundle, so this stays local. -/
def tmSize : Term VName → Nat
  | .var _ => 1
  | .app f a => tmSize f + tmSize a + 1
  | .lam _ τ b => τ.size + tmSize b + 2

def CS : SEnt → Type
  | .tm => Term VName
  | .var => VName
  | .ty => Ty

/-- The truncation instructions. Parentheses vanish in all three entries; `?n` and `⋆` decode to
`Ty.mvar`/`Ty.base`, and re-encode on the way out. -/
def sRules : Rules stlcGrammar CS where
  var {e} t h :=
    match e, h with
    | .tm, h => Term.var ⟨t, h⟩
    | .var, h => ⟨t, h⟩
    | .ty, _ => if isMvarTok t then Ty.mvar (tokMvar t) else Ty.base
  op {e} o vs :=
    match e, o, vs with
    | .tm, .paren, (t, _)       => t
    | .tm, .app,   (f, a, _)    => .app f a
    | .tm, .lam,   (x, τ, b, _) => .lam x τ b
    | .var, .paren, (x, _)      => x
    | .ty, .paren, (τ, _)       => τ
    | .ty, .arrow, (a, b, _)    => .arrow a b
  dest {e} x :=
    match e, x with
    | .tm, Term.var x    => .var x.1 x.2
    | .tm, Term.app f a  => .node .app (f, a, PUnit.unit)
    | .tm, Term.lam x τ b => .node .lam (x, τ, b, PUnit.unit)
    | .var, x => .var x.1 x.2
    | .ty, Ty.base      => .var (tkS "⋆") (by decide)
    | .ty, Ty.mvar n    => .var (mvarTok n) (isTyAtom_mvarTok n)
    | .ty, Ty.arrow a b => .node .arrow (a, b, PUnit.unit)
  parenOp | .tm => SSym.paren | .var => BSym.paren | .ty => TSym.paren
  lp _ := tkS "("
  rp _ := tkS ")"
  paren_eq | .tm => rfl | .var => rfl | .ty => rfl
  holesOk := by intro e o; cases e <;> cases o <;> decide
  topOk := by intro e o; cases e <;> cases o <;> decide
  alg_dest := by
    intro e x
    cases e
    · cases x <;> rfl
    · rfl
    · cases x with
      | base =>
          show (if isMvarTok (tkS "⋆") then Ty.mvar (tokMvar (tkS "⋆")) else Ty.base) = Ty.base
          rw [if_neg (by decide)]
      | mvar n =>
          show (if isMvarTok (mvarTok n) then Ty.mvar (tokMvar (mvarTok n)) else Ty.base)
            = Ty.mvar n
          rw [if_pos (isMvarTok_mvarTok n), tokMvar_mvarTok n]
      | arrow a b => rfl
  op_paren := by intro e y; cases e <;> rfl
  size {e} :=
    match e with
    | .tm => tmSize
    | .var => fun _ => 1
    | .ty => Ty.size
  dest_size := by
    intro e x
    cases e
    · cases x with
      | var x => trivial
      | app f a => exact ⟨by simp +arith [tmSize], by simp +arith [tmSize], trivial⟩
      | lam x τ b =>
          exact ⟨by simp +arith [tmSize], by simp +arith [tmSize],
                 by simp +arith [tmSize], trivial⟩
    · trivial
    · cases x with
      | base => trivial
      | mvar n => trivial
      | arrow a b => exact ⟨by simp +arith [Ty.size], by simp +arith [Ty.size], trivial⟩

/-! ## The language -/

theorem sFollow_def : follow (G := stlcGrammar) SEnt.tm (tkS "def") = true := by decide

theorem sFollow_assign : follow (G := stlcGrammar) SEnt.ty (tkS ":=") = true := by decide

/-- **Assumed**: the STLC grammar is unambiguous. Not decidable (it quantifies over all trees);
deriving it from the lexical fields is the open conjecture. -/
theorem stlcUnambiguous : Unambiguous stlcGrammar := by
  sorry

def stlcLanguage : Language where
  Tm := Term VName
  Ty := Ty
  AnnTy := fun x => { t : Expr stlcGrammar SEnt.ty .loosest // truncExpr sRules t = x }
  AnnTm := fun x => { t : Expr stlcGrammar SEnt.tm .loosest // truncExpr sRules t = x }

  pTy :=
    ((mixfix stlcUnambiguous (G := stlcGrammar) SEnt.ty .loosest).weakenFollow
      (by
        intro t ht
        have h : t = kwAssign := ht
        subst h
        exact sFollow_assign) |> sRules.truncateParser) (fun _ => rfl)

  isVarName := isVarTok
  varAlphabet := inferInstance
  keywords_excluded := by decide

  pTm :=
    ((mixfix stlcUnambiguous (G := stlcGrammar) SEnt.tm .loosest).weakenFollow
      (by
        intro t ht
        have h : t = kwDef := ht
        subst h
        exact sFollow_def) |> sRules.truncateParser) (fun _ => rfl)

/-! ## …and a semantics

Elaboration is `Typing/Target.lean`'s `elabSubst`: generate every constraint the term imposes,
then solve them in one `unify`. So `?0` is a genuine hole — `def id : ?0 → ?0 := λ x : ⋆ . x`
elaborates to `def id : ⋆ → ⋆ := λ x : ⋆ . x` — rather than the opaque atom the bare `HasType`
judgement treats it as. The distinction matters: `HasType` has no rule mentioning `Ty.mvar`, so to
the judgement `?0` is an atom equal to itself and nothing else — an extra base type, not a hole.
Solving is what the elaborator adds on top.

**No metavariable survives a declaration.** Solving is given its chance first, and what remains
unsolved is a mistake in the source rather than an inference request: `def poly : ?0 → ?0 :=
λ x : ?0 . x` still fails, because nothing determines `?0`. Since `Language/Typing.lean` puts the
*elaborated* type into the context, nothing downstream ever sees an unsolved metavariable. That is
imposed by restricting `Elaborates`, not by a field of `ElaboratableLanguage`, exactly as the
interface intends.

**What is and is not claimed.** `elabSubst_sound` is sorry-free, so a successful elaboration
carries a real `HasType` derivation. Most-generality is *not* claimed — that is
`Target.GenerationComplete`, still open. `stlcElaboratable` reports `sorryAx` only through
`toLanguage`, i.e. the assumed `stlcUnambiguous` above.

**Why `Elaborates` demands a stable answer.** `quote_elaborates` needs re-elaborating an output to
reproduce it, which is unproved; rather than assume it, the relation *requires* it. An answer that
were not a fixed point simply does not elaborate — conservative, never unsound, and no `sorry`.
-/

-- Terms compare, given comparable names — needed to *check* that an elaboration is stable.
deriving instance DecidableEq for Term

/-- Variable names carry no type metavariables. Needed for `Ctx VName` to be substitutable. -/
instance : HasVars VName where
  isFree _ _ := False
  fresh _ := 0
  fresh_gt_free := by intro _ _ h; cases h

/-- Infer, then apply — refusing to let a metavariable survive the declaration. -/
def solve (Γ : Ctx VName) (t : Term VName) (τ : Ty) : Option (Term VName × Ty) :=
  match elabSubst Γ t τ with
  | none => none
  | some σ =>
      if (HasSubst.pSubst τ σ : Ty).Ground ∧ (HasSubst.pSubst t σ : Term VName).AnnotsGround then
        some (HasSubst.pSubst t σ, HasSubst.pSubst τ σ)
      else none

/-- **Soundness**, straight from `elabSubst_sound`. -/
theorem solve_hasType {Γ : Ctx VName} {t : Term VName} {τ : Ty} {p : Term VName × Ty}
    (h : solve Γ t τ = some p) :
    ∃ σ, elabSubst Γ t τ = some σ ∧ HasType (HasSubst.pSubst Γ σ) p.1 p.2 := by
  rw [solve] at h
  split at h
  · exact absurd h (by simp)
  · rename_i σ hσ
    refine ⟨σ, hσ, ?_⟩
    split at h
    · cases h; exact elabSubst_sound hσ
    · exact absurd h (by simp)

/-- The answers that reproduce themselves. -/
def solveStable (Γ : Ctx VName) (t : Term VName) (τ : Ty) : Option (Term VName × Ty) :=
  match solve Γ t τ with
  | none => none
  | some p => if solve Γ p.1 p.2 = some p then some p else none

theorem solveStable_idem {Γ : Ctx VName} {t : Term VName} {τ : Ty} {p : Term VName × Ty}
    (h : solveStable Γ t τ = some p) : solveStable Γ p.1 p.2 = some p := by
  rw [solveStable] at h
  split at h
  · exact absurd h (by simp)
  · rename_i q hq
    split at h
    · rename_i hst
      cases h
      simp [solveStable, hst]
    · exact absurd h (by simp)

/-! Matching on `solveStable` directly would abstract it out of the subtype's property, so the
result is generalized with an equation first: `certAux` matches on a *copy* and carries the proof
that the copy is the real thing. -/

private def certAux (Γ : Ctx VName) (t : Term VName) (τ : Ty) :
    (o : Option (Term VName × Ty)) → solveStable Γ t τ = o →
    Option { p : Term VName × Ty // solveStable Γ t τ = some (p.1, p.2) }
  | none,   _ => none
  | some q, h => some ⟨q, by rw [h]⟩

def solveCert (Γ : Ctx VName) (t : Term VName) (τ : Ty) :
    Option { p : Term VName × Ty // solveStable Γ t τ = some (p.1, p.2) } :=
  certAux Γ t τ (solveStable Γ t τ) rfl

private theorem certAux_isSome (Γ : Ctx VName) (t : Term VName) (τ : Ty) :
    ∀ (o : Option (Term VName × Ty)) (h : solveStable Γ t τ = o),
      (certAux Γ t τ o h).isSome = o.isSome
  | none,   _ => rfl
  | some _, _ => rfl

theorem solveCert_isSome {Γ : Ctx VName} {t : Term VName} {τ : Ty}
    (h : (solveStable Γ t τ).isSome) : (solveCert Γ t τ).isSome := by
  rw [solveCert, certAux_isSome]; exact h

/-- **STLC as an elaboratable language**, elaborated by constraint generation. -/
def stlcElaboratable : Language.ElaboratableLanguage where
  toLanguage := stlcLanguage
  Elaborates Γ t t' τ τ' := solveStable Γ t τ = some (t', τ')
  elaborates_unique h₁ h₂ := by
    have h := Option.some.inj (h₁.symm.trans h₂)
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  elaborate := solveCert
  elaborate_complete h := solveCert_isSome (by rw [h]; rfl)
  quote t' τ' := (t', τ')
  quote_elaborates h := by
    obtain ⟨t, τ, hst⟩ := h
    exact solveStable_idem hst

/-- Parse a source file and elaborate it, rendering the result. -/
def elaborateSource (src : String) : Option String :=
  (stlcElaboratable.elaborateFile src).map stlcElaboratable.renderElaborated

end LambdaLab.Stlc.Named
