import LambdaLab.Languages.SystemF.Surface
import LambdaLab.Languages.SystemF.DeBruijn.Check
import LambdaLab.Languages.SystemF.DeBruijn.Eval
import LambdaLab.Languages.SystemF.Named.Typing
import LambdaLab.Semantics.Walk

/-!
# System F — from what is written to what it means

The surface (`Surface.lean`) parses into the named calculus (`Named/`); the checker and the
evaluator run on the de Bruijn core (`DeBruijn/`). This file connects them, and runs programs.

## Translation

`elabTy`/`elabTm` are `Named.Ty.toDB`/`Named.Tm.toDB` extended to declarations
(`elabTm_eq_toDB`): they resolve every name: a bound variable becomes its de Bruijn index; a free type
name is a `type` abbreviation and is replaced by its definition (so the core never sees an
abbreviation, and type equality stays syntactic); a free term name is an earlier `def`, and becomes
a variable beyond the local ones — the term is checked in the context of the earlier definitions'
types. Anything else is an error.

## Readback

`rbTy`/`rbTm` print a core term back as a named one, naming each binder by its depth — `x0, x1, …`
for term binders, `a0, a1, …` for type binders — so that no binder shadows another on any path.
Reading the result back gives the term again (`elabTm_rbTm`), for every term whose variables are in
scope; that is what makes evaluation idempotent.

## Two walks

* **checking** (`checkWalk`): each `type` is translated and remembered; each `def` is translated
  and its term checked against its declared type, in the context of the earlier definitions. It
  rewrites nothing. A definition is accepted exactly when its translation is well typed
  (`checkStep_defn_iff`).
* **evaluation** (`evalWalk`), after checking: each `def`'s term has the earlier definitions'
  values substituted in, and is normalized — total, by strong normalization — and written back. The
  state carries each value with its typing and normality, which is what the next definition needs.

Evaluation is idempotent a step at a time: a written-back normal form reads back as itself, is
closed, so substitution leaves it alone, and is normal, so normalization does. And what evaluation
produces still checks (`evalRun_check`).
-/

namespace LambdaLab.Languages.SystemF

open LambdaLab.Pipeline
open LambdaLab.Parser.Numeral (isDigitChar natTok natOfTok isNatTok)
open LambdaLab.Semantics (Walk)
open LambdaLab.Languages.SystemF.DeBruijn

/-! ## Name lookup -/

/-- The position of a name in a binder list, innermost first. -/
def lookupIdx (n : SName) : List SName → Option Nat
  | [] => none
  | m :: ms => if m = n then some 0 else (lookupIdx n ms).map (· + 1)

/-! ## Translation -/

/-- Translate a type: bound variables to indices, abbreviations to their definitions. -/
def elabTy (tyB : List SName) (ab : List (SName × Ty)) : STy → Option Ty
  | .var n =>
      match lookupIdx n tyB with
      | some i => some (.var i)
      | none => (ab.find? (fun p => p.1 = n)).map (·.2)
  | .arr a b =>
      match elabTy tyB ab a, elabTy tyB ab b with
      | some a', some b' => some (.arr a' b')
      | _, _ => none
  | .all α A => (elabTy (α :: tyB) ab A).map .all

/-- Translate a term: bound variables to indices, earlier definitions to variables beyond the
local ones. -/
def elabTm (tyB tmB : List SName) (ab : List (SName × Ty)) (gl : List SName) : STm → Option Tm
  | .var x =>
      match lookupIdx x tmB with
      | some i => some (.var i)
      | none => (lookupIdx x gl).map (fun g => .var (tmB.length + g))
  | .lam x A b =>
      match elabTy tyB ab A, elabTm tyB (x :: tmB) ab gl b with
      | some A', some b' => some (.lam A' b')
      | _, _ => none
  | .app f a =>
      match elabTm tyB tmB ab gl f, elabTm tyB tmB ab gl a with
      | some f', some a' => some (.app f' a')
      | _, _ => none
  | .tlam α b => (elabTm (α :: tyB) tmB ab gl b).map .tlam
  | .tapp f A =>
      match elabTm tyB tmB ab gl f, elabTy tyB ab A with
      | some f', some A' => some (.tapp f' A')
      | _, _ => none

/-! ## With nothing declared, it is the named calculus's translation

The parser lands in `Named.Tm`, and `elabTy`/`elabTm` differ from `Named.Ty.toDB`/`Named.Tm.toDB`
only in what they do with a name no binder accounts for: the pipeline looks it up among the
declarations, the named calculus sends it past the end of the binder list. With nothing declared,
a translation that succeeds is the named calculus's. -/

theorem lookupIdx_eq_some {n : SName} : ∀ {l : List SName} {i : Nat},
    lookupIdx n l = some i → Named.lookupVar n l = i
  | [], _, h => by simp [lookupIdx] at h
  | m :: ms, i, h => by
      simp only [lookupIdx] at h
      by_cases hm : m = n
      · subst hm
        simp only [if_true, Option.some.injEq] at h
        subst h
        simp
      · rw [if_neg hm] at h
        cases hl : lookupIdx n ms with
        | none => simp [hl] at h
        | some j =>
            simp only [hl, Option.map_some, Option.some.injEq] at h
            subst h
            rw [Named.lookupVar_cons_ne _ (Ne.symm hm), lookupIdx_eq_some hl]

theorem elabTy_eq_toDB : ∀ (A : STy) (tyB : List SName) (A' : Ty),
    elabTy tyB [] A = some A' → A' = A.toDB tyB
  | .var n, tyB, A', h => by
      simp only [elabTy] at h
      split at h
      · rename_i i hi
        cases h
        simp only [Named.Ty.toDB, lookupIdx_eq_some hi]
      · simp at h
  | .arr a b, tyB, A', h => by
      simp only [elabTy] at h
      split at h
      · rename_i a' b' ha hb
        cases h
        simp only [Named.Ty.toDB, elabTy_eq_toDB a tyB a' ha, elabTy_eq_toDB b tyB b' hb]
      · cases h
  | .all α A, tyB, A', h => by
      simp only [elabTy, Option.map_eq_some_iff] at h
      obtain ⟨A₀, hA, rfl⟩ := h
      simp only [Named.Ty.toDB, elabTy_eq_toDB A (α :: tyB) A₀ hA]

theorem elabTm_eq_toDB : ∀ (t : STm) (tyB tmB : List SName) (t' : Tm),
    elabTm tyB tmB [] [] t = some t' → t' = t.toDB tyB tmB
  | .var x, tyB, tmB, t', h => by
      simp only [elabTm] at h
      split at h
      · rename_i i hi
        cases h
        simp only [Named.Tm.toDB, lookupIdx_eq_some hi]
      · simp [lookupIdx] at h
  | .lam x A b, tyB, tmB, t', h => by
      simp only [elabTm] at h
      split at h
      · rename_i A' b' hA hb
        cases h
        simp only [Named.Tm.toDB, elabTy_eq_toDB A tyB A' hA, elabTm_eq_toDB b tyB (x :: tmB) b' hb]
      · cases h
  | .app f a, tyB, tmB, t', h => by
      simp only [elabTm] at h
      split at h
      · rename_i f' a' hf ha
        cases h
        simp only [Named.Tm.toDB, elabTm_eq_toDB f tyB tmB f' hf, elabTm_eq_toDB a tyB tmB a' ha]
      · cases h
  | .tlam α b, tyB, tmB, t', h => by
      simp only [elabTm, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Named.Tm.toDB, elabTm_eq_toDB b (α :: tyB) tmB b' hb]
  | .tapp f A, tyB, tmB, t', h => by
      simp only [elabTm] at h
      split at h
      · rename_i f' A' hf hA
        cases h
        simp only [Named.Tm.toDB, elabTm_eq_toDB f tyB tmB f' hf, elabTy_eq_toDB A tyB A' hA]
      · cases h

/-! ## Canonical names -/

theorem sf_digit_word : ∀ c, isDigitChar c = true → sfLex.word c = true :=
  LambdaLab.Parser.IsoParser.Lexicon.make_digit_word

/-- A generated name: a prefix character and a number. Never reserved, because no reserved token
has that shape. -/
def genName (pre : Char) (hpre : sfLex.word pre = true)
    (hres : ∀ r ∈ sfReserved, isNatTok pre r = false) (k : Nat) : SName :=
  ⟨natTok pre hpre sf_digit_word k, by
    show decide (natTok pre hpre sf_digit_word k ∉ sfReserved) = true
    rw [decide_eq_true_eq]
    intro hmem
    have h1 := hres _ hmem
    rw [LambdaLab.Parser.Numeral.isNatTok_natTok] at h1
    cases h1⟩

theorem genName_inj {pre : Char} {hpre : sfLex.word pre = true}
    {hres : ∀ r ∈ sfReserved, isNatTok pre r = false} {j k : Nat}
    (h : genName pre hpre hres j = genName pre hpre hres k) : j = k := by
  have := congrArg (fun n : SName => natOfTok n.val) h
  simp only [genName, LambdaLab.Parser.Numeral.natOfTok_natTok] at this
  exact this

/-- The name of the term binder at depth `k`: `x0`, `x1`, … -/
def tmName (k : Nat) : SName := genName 'x' (by decide) (by decide) k

/-- The name of the type binder at depth `k`: `a0`, `a1`, … -/
def tyName (k : Nat) : SName := genName 'a' (by decide) (by decide) k

/-- The binders in scope at depth `n`, innermost first. -/
def depthNames (f : Nat → SName) : Nat → List SName
  | 0 => []
  | n + 1 => f n :: depthNames f n

theorem lookupIdx_depthNames {f : Nat → SName} (hf : ∀ j k, f j = f k → j = k) :
    ∀ {n k : Nat}, k < n → lookupIdx (f k) (depthNames f n) = some (n - 1 - k)
  | 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, hk => by
      simp only [depthNames, lookupIdx]
      by_cases hkn : k = n
      · subst hkn
        simp
      · have hne : f n ≠ f k := fun h => hkn (hf n k h).symm
        rw [if_neg hne, lookupIdx_depthNames hf (by omega : k < n)]
        simp only [Option.map_some, Option.some.injEq]
        omega

/-! ## Readback -/

/-- Print a type, naming each type binder by its depth. -/
def rbTy : Nat → Ty → STy
  | e, .var i => .var (tyName (e - 1 - i))
  | e, .arr a b => .arr (rbTy e a) (rbTy e b)
  | e, .all A => .all (tyName e) (rbTy (e + 1) A)

/-- Print a term, naming each binder by its depth. -/
def rbTm : Nat → Nat → Tm → STm
  | d, _, .var i => .var (tmName (d - 1 - i))
  | d, e, .lam A b => .lam (tmName d) (rbTy e A) (rbTm (d + 1) e b)
  | d, e, .app f a => .app (rbTm d e f) (rbTm d e a)
  | d, e, .tlam b => .tlam (tyName e) (rbTm d (e + 1) b)
  | d, e, .tapp f A => .tapp (rbTm d e f) (rbTy e A)

/-- **Reading a printed type back gives the type.** -/
theorem elabTy_rbTy : ∀ (A : Ty) (e : Nat) (ab : List (SName × Ty)),
    A.wf e = true → elabTy (depthNames tyName e) ab (rbTy e A) = some A
  | .var i, e, _, h => by
      simp only [Ty.wf, decide_eq_true_eq] at h
      have hl := lookupIdx_depthNames (f := tyName) (fun _ _ => genName_inj)
        (n := e) (k := e - 1 - i) (by omega)
      simp only [rbTy, elabTy, hl]
      congr 2
      omega
  | .arr a b, e, ab, h => by
      simp only [Ty.wf, Bool.and_eq_true] at h
      simp only [rbTy, elabTy, elabTy_rbTy a e ab h.1, elabTy_rbTy b e ab h.2]
  | .all A, e, ab, h => by
      simp only [Ty.wf] at h
      have := elabTy_rbTy A (e + 1) ab h
      simp only [depthNames] at this
      simp only [rbTy, elabTy, this, Option.map_some]

/-- **Reading a printed term back gives the term**, whatever abbreviations and definitions are in
scope — none of them is ever consulted, because every name is bound. -/
theorem elabTm_rbTm : ∀ (t : Tm) (d e : Nat) (ab : List (SName × Ty)) (gl : List SName),
    t.scoped d e = true →
      elabTm (depthNames tyName e) (depthNames tmName d) ab gl (rbTm d e t) = some t
  | .var i, d, e, _, _, h => by
      simp only [Tm.scoped, decide_eq_true_eq] at h
      have hl := lookupIdx_depthNames (f := tmName) (fun _ _ => genName_inj)
        (n := d) (k := d - 1 - i) (by omega)
      simp only [rbTm, elabTm, hl]
      congr 2
      omega
  | .lam A b, d, e, ab, gl, h => by
      simp only [Tm.scoped, Bool.and_eq_true] at h
      have hb := elabTm_rbTm b (d + 1) e ab gl h.2
      simp only [depthNames] at hb
      simp only [rbTm, elabTm, elabTy_rbTy A e ab h.1, hb]
  | .app f a, d, e, ab, gl, h => by
      simp only [Tm.scoped, Bool.and_eq_true] at h
      simp only [rbTm, elabTm, elabTm_rbTm f d e ab gl h.1, elabTm_rbTm a d e ab gl h.2]
  | .tlam b, d, e, ab, gl, h => by
      simp only [Tm.scoped] at h
      have hb := elabTm_rbTm b d (e + 1) ab gl h
      simp only [depthNames] at hb
      simp only [rbTm, elabTm, hb, Option.map_some]
  | .tapp f A, d, e, ab, gl, h => by
      simp only [Tm.scoped, Bool.and_eq_true] at h
      simp only [rbTm, elabTm, elabTm_rbTm f d e ab gl h.1, elabTy_rbTy A e ab h.2]

/-! ## Checking -/

/-- What checking carries: the abbreviations so far, and the earlier definitions' types. -/
structure CState where
  abbrevs : List (SName × Ty)
  globals : List (SName × Ty)

/-- The diagnostic for a type that does not translate. -/
def unknownTyMsg : String := "this type mentions a name that is neither bound nor an earlier `type`"

/-- The diagnostic for a term that does not translate. -/
def unknownTmMsg : String := "this term mentions a name that is neither bound nor an earlier `def`"

/-- **Check one declaration.** It rewrites nothing. -/
def checkStep (s : CState) : SDecl → Except String (SDecl × CState)
  | .tydef α A =>
      match elabTy [] s.abbrevs A with
      | some A' => .ok (.tydef α A, { s with abbrevs := (α, A') :: s.abbrevs })
      | none => .error unknownTyMsg
  | .defn x A t =>
      match elabTy [] s.abbrevs A, elabTm [] [] s.abbrevs (s.globals.map (·.1)) t with
      | some A', some t' =>
          if infer 0 (s.globals.map (·.2)) t' = some A' then
            .ok (.defn x A t, { s with globals := (x, A') :: s.globals })
          else .error "this definition does not have its declared type"
      | A', _ => .error (if A'.isNone then unknownTyMsg else unknownTmMsg)

/-- **The checker**, as a walk. -/
def checkWalk : Walk SDecl where
  State := CState
  init := ⟨[], []⟩
  step := checkStep

theorem checkStep_out {s : CState} {d d' : SDecl} {s' : CState}
    (h : checkStep s d = .ok (d', s')) : d' = d := by
  cases d with
  | tydef α A =>
      simp only [checkStep] at h
      split at h
      · cases h; rfl
      · cases h
  | defn x A t =>
      simp only [checkStep] at h
      split at h
      · split at h
        · cases h; rfl
        · cases h
      · cases h

theorem checkWalk_stepIdempotent : checkWalk.StepIdempotent := by
  intro s d d' s' h
  have h' : checkStep s d = .ok (d', s') := h
  have := checkStep_out h'
  subst this
  exact h

theorem checkWalk_idempotent : checkWalk.Idempotent :=
  checkWalk.idempotent_of_step checkWalk_stepIdempotent

/-- **A definition is accepted exactly when its translation is well typed** — against the
declarative judgement, in the context of the earlier definitions. -/
theorem checkStep_defn_iff (s : CState) (x : SName) (A : STy) (t : STm) :
    (∃ r, checkStep s (.defn x A t) = .ok r) ↔
      ∃ A' t', elabTy [] s.abbrevs A = some A' ∧
        elabTm [] [] s.abbrevs (s.globals.map (·.1)) t = some t' ∧
        HasType 0 (s.globals.map (·.2)) t' A' := by
  simp only [checkStep]
  constructor
  · rintro ⟨r, h⟩
    split at h
    · rename_i A' t' hA ht
      split at h
      · rename_i hi
        exact ⟨A', t', hA, ht, infer_sound hi⟩
      · cases h
    · cases h
  · rintro ⟨A', t', hA, ht, hty⟩
    simp only [hA, ht, infer_complete hty, if_true]
    exact ⟨_, rfl⟩

/-- **With nothing declared before it, a definition the checker accepts is well typed in the named
calculus** — the parsed term at the parsed type, no translation in sight. -/
theorem checkStep_named {x : SName} {A : STy} {t : STm}
    (h : ∃ r, checkStep ⟨[], []⟩ (.defn x A t) = .ok r) : Named.HasType [] [] t A := by
  obtain ⟨A', t', hA, ht, hty⟩ := (checkStep_defn_iff _ x A t).mp h
  have e₁ := elabTy_eq_toDB A [] A' hA
  have e₂ := elabTm_eq_toDB t [] [] t' ht
  subst e₁ e₂
  exact Named.hasType_iff_toDB.mpr hty

/-! ## Evaluation -/

/-- An earlier definition, evaluated: its value, closed, typed and normal. -/
structure EEntry where
  name : SName
  ty : Ty
  val : Tm
  typed : HasType 0 [] val ty
  normal : val.Normal

theorem EEntry.ext {a b : EEntry} (hn : a.name = b.name) (ht : a.ty = b.ty) (hv : a.val = b.val) :
    a = b := by
  cases a; cases b
  simp only at hn ht hv
  subst hn ht hv
  rfl

/-- What evaluation carries: the abbreviations so far, and the earlier definitions' values. -/
structure EState where
  abbrevs : List (SName × Ty)
  globals : List EEntry

/-- The context the earlier definitions stand for. -/
def EState.ctx (s : EState) : List Ty := s.globals.map (·.ty)

/-- Substitute each earlier definition's value for its variable. -/
def EState.env (s : EState) (i : Nat) : Tm :=
  match s.globals[i]? with
  | some e => e.val
  | none => .var i

theorem EState.env_typed (s : EState) :
    ∀ n B, s.ctx[n]? = some B → HasType 0 [] (s.env n) B := by
  intro n B hn
  simp only [EState.ctx, List.getElem?_map] at hn
  cases hg : s.globals[n]? with
  | none => rw [hg] at hn; cases hn
  | some e =>
      rw [hg] at hn
      cases hn
      simp only [EState.env, hg]
      exact e.typed

/-- **Evaluate one declaration.** A `type` is remembered as checking remembers it. A `def` is
translated and checked; the earlier definitions' values are substituted in, which closes it; it is
normalized — total, the closed term being well typed — and written back with generated names. -/
def evalStep (s : EState) : SDecl → Except String (SDecl × EState)
  | .tydef α A =>
      match elabTy [] s.abbrevs A with
      | some A' => .ok (.tydef α A, { s with abbrevs := (α, A') :: s.abbrevs })
      | none => .error unknownTyMsg
  | .defn x A t =>
      match elabTy [] s.abbrevs A, elabTm [] [] s.abbrevs (s.globals.map (·.name)) t with
      | some A', some t' =>
          if h : infer 0 s.ctx t' = some A' then
            .ok (.defn x A (rbTm 0 0 ((infer_sound h).subst s.env_typed).eval),
              { s with globals :=
                  ⟨x, A', ((infer_sound h).subst s.env_typed).eval,
                    ((infer_sound h).subst s.env_typed).eval_typed,
                    (Tm.eval_spec ((infer_sound h).subst s.env_typed).sn).2⟩ :: s.globals })
          else .error "this definition does not have its declared type"
      | A', _ => .error (if A'.isNone then unknownTyMsg else unknownTmMsg)

/-- **The evaluator**, as a walk. -/
def evalWalk : Walk SDecl where
  State := EState
  init := ⟨[], []⟩
  step := evalStep

/-- What one evaluation step does: a `type` passes through; a `def` comes out as its value's
readback, the value pushed with its typing. -/
theorem evalStep_sound {s : EState} {d d' : SDecl} {s' : EState}
    (h : evalStep s d = .ok (d', s')) :
    (∃ (α : SName) (A : STy) (A' : Ty), d = .tydef α A ∧ d' = d ∧ elabTy [] s.abbrevs A = some A' ∧
      s' = { s with abbrevs := (α, A') :: s.abbrevs }) ∨
    (∃ (A : STy) (e : EEntry), d' = .defn e.name A (rbTm 0 0 e.val) ∧
      elabTy [] s.abbrevs A = some e.ty ∧ (∃ t, d = .defn e.name A t) ∧
      s' = { s with globals := e :: s.globals }) := by
  cases d with
  | tydef α A =>
      simp only [evalStep] at h
      split at h
      · rename_i A' hA
        cases h
        exact .inl ⟨α, A, A', rfl, rfl, hA, rfl⟩
      · cases h
  | defn x A t =>
      simp only [evalStep] at h
      split at h
      · rename_i A' t' hA ht
        split at h
        · rename_i hi
          cases h
          exact .inr ⟨A, _, rfl, hA, ⟨t, rfl⟩, rfl⟩
        · cases h
      · cases h

/-- **An evaluated definition evaluates to itself**, with the same entry: its readback reads back
as its value, which is closed (so the substitution leaves it alone) and normal (so the normalizer
does). -/
theorem evalStep_reduced (s : EState) (A : STy) (e : EEntry)
    (hA : elabTy [] s.abbrevs A = some e.ty) :
    evalStep s (.defn e.name A (rbTm 0 0 e.val)) =
      .ok (.defn e.name A (rbTm 0 0 e.val), { s with globals := e :: s.globals }) := by
  have hr : elabTm [] [] s.abbrevs (s.globals.map (·.name)) (rbTm 0 0 e.val) = some e.val :=
    elabTm_rbTm e.val 0 0 s.abbrevs _ e.typed.scoped
  have hi : infer 0 s.ctx e.val = some e.ty := infer_complete e.typed.weaken_closed
  simp only [evalStep, hA, hr]
  rw [dif_pos hi]
  have hv : ((infer_sound hi).subst s.env_typed).eval = e.val := by
    show (e.val.subst s.env).eval _ = e.val
    rw [Tm.eval_congr (e.typed.subst_closed s.env) _ e.typed.sn]
    exact Tm.eval_of_normal _ e.normal
  have he : (⟨e.name, e.ty, ((infer_sound hi).subst s.env_typed).eval,
      ((infer_sound hi).subst s.env_typed).eval_typed,
      (Tm.eval_spec ((infer_sound hi).subst s.env_typed).sn).2⟩ : EEntry) = e :=
    EEntry.ext rfl rfl hv
  rw [he, hv]

/-- **Idempotence, a step at a time.** -/
theorem evalWalk_stepIdempotent : evalWalk.StepIdempotent := by
  intro s d d' s' h
  have h' : evalStep s d = .ok (d', s') := h
  rcases evalStep_sound h' with ⟨α, A, A', rfl, rfl, hA, rfl⟩ | ⟨A, e, rfl, hA, _, rfl⟩
  · exact h'
  · exact evalStep_reduced s A e hA

/-- What checking would carry, read off what evaluation carries. -/
def EState.proj (s : EState) : CState := ⟨s.abbrevs, s.globals.map (fun e => (e.name, e.ty))⟩

/-- **Evaluation's output checks**, a step at a time, in the corresponding state. -/
theorem evalStep_check {s : EState} {d d' : SDecl} {s' : EState}
    (h : evalStep s d = .ok (d', s')) : checkStep s.proj d' = .ok (d', s'.proj) := by
  rcases evalStep_sound h with ⟨α, A, A', rfl, rfl, hA, rfl⟩ | ⟨A, e, rfl, hA, _, rfl⟩
  · simp only [checkStep, EState.proj, hA]
  · have hr : elabTm [] [] s.abbrevs ((s.globals.map (fun e => (e.name, e.ty))).map (·.1))
        (rbTm 0 0 e.val) = some e.val :=
      elabTm_rbTm e.val 0 0 s.abbrevs _ e.typed.scoped
    have hi : infer 0 ((s.globals.map (fun e => (e.name, e.ty))).map (·.2)) e.val = some e.ty :=
      infer_complete e.typed.weaken_closed
    simp only [checkStep, EState.proj, hA, hr, hi, if_true]
    rfl

/-- **What evaluation produces still checks**: checking accepts evaluation's output a step at a
time (`evalStep_check`), so it accepts it whole (`Walk.runFrom_sim`). -/
theorem evalRun_check {p q : Program systemFLanguage} (h : evalWalk.run p = .ok q) :
    checkWalk.run q = .ok q :=
  (Walk.run_eq_ok _).mpr (evalWalk.runFrom_sim checkWalk EState.proj
    (fun _ _ _ _ hs => evalStep_check hs) _ _ _ ((Walk.run_eq_ok _).mp h))

/-- **The law, as the stage after checking.** -/
theorem evalWalk_lawfulOn : evalWalk.LawfulOn (fun p => checkWalk.run p = .ok p) where
  preserve _ _ _ h := evalRun_check h
  idem p q _ h := evalWalk.idempotent_of_step evalWalk_stepIdempotent p q h

/-! ## The front end -/

/-- After checking: the program as written, every definition well typed. -/
abbrev checkedStage : LambdaLab.Abstraction.Stage :=
  systemFLanguage.walkStage "checked program" checkWalk

/-- After evaluation: every definition's term in normal form. -/
abbrev evaluatedStage : LambdaLab.Abstraction.Stage :=
  systemFLanguage.walkStageOn "evaluated program" evalWalk (fun p => checkWalk.run p = .ok p)

/-- **The whole front end, stage by stage**: source, tokens, program, checked program, evaluated
program. -/
def systemFChain : LambdaLab.Abstraction.Chain sourceStage evaluatedStage :=
  (systemFLanguage.walkChain checkWalk checkWalk_idempotent "checked program").cons
    (Z := evaluatedStage) (systemFLanguage.walkCellOn evalWalk evalWalk_lawfulOn)

/-- **Characters to an evaluated program**, in `Abs`: one morphism, so one round-trip law. -/
def evalPipeline :=
  (systemFLanguage.walkPipeline checkWalk checkWalk_idempotent).comp
    (evalWalk.stageOn evalWalk_lawfulOn)

/-- Read, check and evaluate a source file. -/
def evaluateFile (s : String) : Except Diag (evalWalk.FixedOn (fun p => checkWalk.run p = .ok p)) :=
  evalPipeline.abstract s.toList

/-- Render an evaluated program canonically. -/
def renderEvaluated (q : evalWalk.FixedOn (fun p => checkWalk.run p = .ok p)) : String :=
  String.ofList (evalPipeline.realize (evalPipeline.default (a := q)))

/-- **The front end round-trips**: rendering an evaluated program and reading it back
re-tokenizes, re-parses, re-checks and re-evaluates to exactly what you started with. -/
theorem evaluateFile_renderEvaluated (q : evalWalk.FixedOn (fun p => checkWalk.run p = .ok p)) :
    evaluateFile (renderEvaluated q) = .ok q := by
  show evalPipeline.abstract (String.ofList (evalPipeline.realize (evalPipeline.default (a := q)))).toList = .ok q
  rw [String.toList_ofList]
  exact evalPipeline.abstract_realize q evalPipeline.default

end LambdaLab.Languages.SystemF
