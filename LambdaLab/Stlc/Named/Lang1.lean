import LambdaLab.Stlc.Named.Basic
import LambdaLab.Language1.Biparser
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Parser.Truncation.Mixfix
import Mathlib.Data.Nat.Digits.Defs

/-!
# STLC as a `Language1.Language` — types land in `Stlc.Ty`

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
belongs in a lossy layer above, whose annotation records which binders were elided. That is the
`annotated | infer` split of `Abstraction2/Sketch.lean`.

## Why terms still go through `STm`

`Ty` can be a parser value type; `Term` cannot, for a reason unrelated to annotations:
`Term.var`/`Term.lam` take an arbitrary `String`, so `Term.var "def"` and `Term.var ""` exist and
have no printable spelling — `Term` is wider than the printable set. `STm` is `Term` with names
restricted to non-keyword tokens; `STm.toTerm` just forgets that restriction. (A subtype
`{t : Term // names are tokens}` would remove `STm` entirely; it is the natural next step.)

The grammar is a single three-entry grammar — terms, binders, types — so `pTm` and `pTy` are the
same engine at different entries, and the binder's `: T` is an ordinary cross-entry hole.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Parser.IsoParser LambdaLab.Parser.IsoParser.Mixfix LambdaLab.Language1
open LambdaLab.Parser.Truncation.Mixfix

/-! ## Metavariable tokens: `?n` -/

def digitChar (d : Nat) : Char := Char.ofNat (48 + d)
def charDigit (c : Char) : Nat := c.toNat - 48
def isDigitChar (c : Char) : Bool := decide (48 ≤ c.toNat ∧ c.toNat ≤ 57)

/-- Everything needed about a decimal digit's character, by exhaustion. -/
theorem digitChar_spec : ∀ {d : Nat}, d < 10 →
    charDigit (digitChar d) = d ∧ isSep (digitChar d) = false ∧ isDigitChar (digitChar d) = true
  | 0, _ => by decide | 1, _ => by decide | 2, _ => by decide | 3, _ => by decide
  | 4, _ => by decide | 5, _ => by decide | 6, _ => by decide | 7, _ => by decide
  | 8, _ => by decide | 9, _ => by decide

/-- Decimal characters of `n`, most significant first; never empty. -/
def natChars (n : Nat) : List Char :=
  if n = 0 then ['0'] else ((Nat.digits 10 n).map digitChar).reverse

def charsNat (cs : List Char) : Nat := Nat.ofDigits 10 ((cs.map charDigit).reverse)

theorem natChars_spec (n : Nat) :
    natChars n ≠ [] ∧ ∀ c ∈ natChars n, isSep c = false ∧ isDigitChar c = true := by
  unfold natChars
  split
  · exact ⟨by simp, by intro c hc; simp at hc; subst hc; exact ⟨by decide, by decide⟩⟩
  · next h =>
      refine ⟨?_, ?_⟩
      · simp only [ne_eq, List.reverse_eq_nil_iff, List.map_eq_nil_iff]
        exact Nat.digits_ne_nil_iff_ne_zero.mpr h
      · intro c hc
        simp only [List.mem_reverse, List.mem_map] at hc
        obtain ⟨d, hd, rfl⟩ := hc
        have := digitChar_spec (Nat.digits_lt_base (by norm_num) hd)
        exact ⟨this.2.1, this.2.2⟩

theorem charsNat_natChars (n : Nat) : charsNat (natChars n) = n := by
  unfold natChars charsNat
  split
  · next h => subst h; decide
  · next h =>
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      have hid : ∀ d ∈ Nat.digits 10 n, (charDigit ∘ digitChar) d = id d :=
        fun d hd => (digitChar_spec (Nat.digits_lt_base (by norm_num) hd)).1
      rw [List.map_congr_left hid, List.map_id]
      exact Nat.ofDigits_digits 10 n

/-! ## The token alphabet -/

def tkS (s : String) (h : isToken isSep s = true := by decide) : Language1.Token := ⟨s, h⟩

/-- Grammar name-parts and vernacular keywords: never variables. -/
def sReserved : List Language1.Token :=
  [tkS "(", tkS ")", tkS "λ", tkS ".", tkS ":", tkS "→", tkS "⋆", tkS "def", tkS ":="]

def isVarTok (t : Language1.Token) : Bool := decide (t ∉ sReserved)

/-- `?` followed by at least one decimal digit. -/
def isMvarTok (t : Language1.Token) : Bool :=
  match t.val.toList with
  | '?' :: ds => !ds.isEmpty && ds.all isDigitChar
  | _ => false

/-- Type atoms: the base type `⋆`, and metavariables `?n`. -/
def isTyAtom (t : Language1.Token) : Bool := (t.val == "⋆") || isMvarTok t

/-- The token spelling `?n`. -/
def mvarTok (n : Nat) : Language1.Token :=
  ⟨String.ofList ('?' :: natChars n), isToken_iff.mpr (by
    rw [String.toList_ofList]
    refine ⟨?_, by simp⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · decide
    · exact ((natChars_spec n).2 c hc').1)⟩

/-- Read the index back out of a `?n` token. -/
def tokMvar (t : Language1.Token) : Nat := charsNat t.val.toList.tail

theorem tokMvar_mvarTok (n : Nat) : tokMvar (mvarTok n) = n := by
  simp only [tokMvar, mvarTok, String.toList_ofList, List.tail_cons]
  exact charsNat_natChars n

theorem isMvarTok_mvarTok (n : Nat) : isMvarTok (mvarTok n) = true := by
  have hs := natChars_spec n
  simp only [isMvarTok, mvarTok, String.toList_ofList]
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨?_, fun c hc => (hs.2 c hc).2⟩
  cases hh : natChars n with
  | nil => exact absurd hh hs.1
  | cons a as => simp

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

def tmEntry : Entry Language1.Token SEnt where
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

def varEntry : Entry Language1.Token SEnt where
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

def tyEntry : Entry Language1.Token SEnt where
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

def stlcGrammar : Grammar Language1.Token where
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

abbrev VName := { t : Language1.Token // isVarTok t = true }

/-- Surface terms: `Term` with variable names restricted to non-keyword tokens. The binder's
annotation is a real `Ty`, taken from the source — there is nothing left for the parser to
invent. -/
inductive STm where
  | var : (t : Language1.Token) → isVarTok t = true → STm
  | app : STm → STm → STm
  | lam : VName → Ty → STm → STm

def Ty.size : Ty → Nat
  | .base => 1
  | .mvar _ => 1
  | .arrow a b => a.size + b.size + 1

def STm.size : STm → Nat
  | .var _ _ => 1
  | .app f a => f.size + a.size + 1
  | .lam _ τ b => τ.size + b.size + 2

/-- Forget the name restriction. No metavariables are invented: the source wrote them. -/
def STm.toTerm : STm → Term
  | .var t _ => .var t.val
  | .app f a => .app f.toTerm a.toTerm
  | .lam x τ b => .lam x.1.val τ b.toTerm

def CS : SEnt → Type
  | .tm => STm
  | .var => VName
  | .ty => Ty

/-- The truncation instructions. Parentheses vanish in all three entries; `?n` and `⋆` decode to
`Ty.mvar`/`Ty.base`, and re-encode on the way out. -/
def sRules : Rules stlcGrammar CS where
  var {e} t h :=
    match e, h with
    | .tm, h => STm.var t h
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
    | .tm, STm.var t h  => .var t h
    | .tm, STm.app f a  => .node .app (f, a, PUnit.unit)
    | .tm, STm.lam x τ b => .node .lam (x, τ, b, PUnit.unit)
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
    | .tm => STm.size
    | .var => fun _ => 1
    | .ty => Ty.size
  dest_size := by
    intro e x
    cases e
    · cases x with
      | var t h => trivial
      | app f a => exact ⟨by simp +arith [STm.size], by simp +arith [STm.size], trivial⟩
      | lam x τ b =>
          exact ⟨by simp +arith [STm.size], by simp +arith [STm.size],
                 by simp +arith [STm.size], trivial⟩
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
  Tm := STm
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

  pTm :=
    ((mixfix stlcUnambiguous (G := stlcGrammar) SEnt.tm .loosest).weakenFollow
      (by
        intro t ht
        have h : t = kwDef := ht
        subst h
        exact sFollow_def) |> sRules.truncateParser) (fun _ => rfl)

end LambdaLab.Stlc.Named
