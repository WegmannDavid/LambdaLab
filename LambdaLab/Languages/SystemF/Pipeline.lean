import LambdaLab.Languages.SystemF.Surface
import LambdaLab.Languages.SystemF.Check
import LambdaLab.Languages.SystemF.Eval
import LambdaLab.Semantics.Walk

/-!
# System F — from what is written to what it means

The surface (`Surface.lean`) is named; the metatheory (`Typing.lean` … `Eval.lean`) is de Bruijn.
This file connects them, and runs programs.

## Translation

`elabTy`/`elabTm` resolve every name: a bound variable becomes its de Bruijn index; a free type
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

/-! ## Canonical names -/

theorem sf_digit_not_sep : ∀ c, isDigitChar c = true → isSep c = false :=
  fun _ h => LambdaLab.Parser.Numeral.isDigitChar_not_whitespace h

/-- A generated name: a prefix character and a number. Never reserved, because no reserved token
has that shape. -/
def genName (pre : Char) (hpre : isSep pre = false)
    (hres : ∀ r ∈ sfReserved, isNatTok pre r = false) (k : Nat) : SName :=
  ⟨natTok pre hpre sf_digit_not_sep k, by
    show decide (natTok pre hpre sf_digit_not_sep k ∉ sfReserved) = true
    rw [decide_eq_true_eq]
    intro hmem
    have h1 := hres _ hmem
    rw [LambdaLab.Parser.Numeral.isNatTok_natTok] at h1
    cases h1⟩

theorem genName_inj {pre : Char} {hpre : isSep pre = false}
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

/-- Every variable is in scope: term variables below `d`, type variables below `e`. -/
def Tm.scoped : Nat → Nat → Tm → Bool
  | d, _, .var i => decide (i < d)
  | d, e, .lam A b => A.wf e && b.scoped (d + 1) e
  | d, e, .app f a => f.scoped d e && a.scoped d e
  | d, e, .tlam b => b.scoped d (e + 1)
  | d, e, .tapp f A => f.scoped d e && A.wf e

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

/-- A typed term has its variables in scope. -/
theorem HasType.scoped {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Δ Γ t A) :
    t.scoped Γ.length Δ = true := by
  induction h with
  | var hn =>
      simp only [Tm.scoped, decide_eq_true_eq]
      exact (List.getElem?_eq_some_iff.mp hn).1
  | lam hA _ ih =>
      simp only [Tm.scoped, Bool.and_eq_true, List.length_cons] at ih ⊢
      exact ⟨hA, ih⟩
  | app _ _ ih₁ ih₂ =>
      simp only [Tm.scoped, Bool.and_eq_true]
      exact ⟨ih₁, ih₂⟩
  | tlam _ ih =>
      simp only [Tm.scoped]
      rwa [List.length_map] at ih
  | tapp _ hB ih =>
      simp only [Tm.scoped, Bool.and_eq_true]
      exact ⟨ih, hB⟩

/-- Substitution leaves alone every variable it maps to itself; on a term whose variables are all
among those, it does nothing. -/
theorem Tm.subst_of_scoped : ∀ (t : Tm) (d e : Nat) (σ : Nat → Tm), (∀ i, i < d → σ i = .var i) →
    t.scoped d e = true → t.subst σ = t
  | .var i, d, _, σ, hσ, h => by
      simp only [Tm.scoped, decide_eq_true_eq] at h
      exact hσ i h
  | .lam A b, d, e, σ, hσ, h => by
      simp only [Tm.scoped, Bool.and_eq_true] at h
      simp only [Tm.subst]
      rw [Tm.subst_of_scoped b (d + 1) e (Tm.up σ) (fun i hi => by
        cases i with
        | zero => rfl
        | succ i => simp only [Tm.up_succ, hσ i (by omega)]; rfl) h.2]
  | .app f a, d, e, σ, hσ, h => by
      simp only [Tm.scoped, Bool.and_eq_true] at h
      simp only [Tm.subst, Tm.subst_of_scoped f d e σ hσ h.1, Tm.subst_of_scoped a d e σ hσ h.2]
  | .tlam b, d, e, σ, hσ, h => by
      simp only [Tm.scoped] at h
      simp only [Tm.subst]
      rw [Tm.subst_of_scoped b d (e + 1) (Tm.tup σ) (fun i hi => by
        simp only [Tm.tup, hσ i hi]; rfl) h]
  | .tapp f A, d, e, σ, hσ, h => by
      simp only [Tm.scoped, Bool.and_eq_true] at h
      simp only [Tm.subst, Tm.subst_of_scoped f d e σ hσ h.1]

/-- A closed, well-typed term is left alone by any substitution. -/
theorem HasType.subst_closed {t : Tm} {A : Ty} (h : HasType 0 [] t A) (σ : Nat → Tm) :
    t.subst σ = t :=
  Tm.subst_of_scoped t 0 0 σ (fun _ hi => absurd hi (Nat.not_lt_zero _)) h.scoped

/-- `eval` depends only on the term. -/
theorem Tm.eval_congr {t u : Tm} (e : t = u) (h : SN Step t) (h' : SN Step u) :
    t.eval h = u.eval h' := by
  subst e; rfl

/-! ## Checking -/

/-- What checking carries: the abbreviations so far, and the earlier definitions' types. -/
structure CState where
  abbrevs : List (SName × Ty)
  globals : List (SName × Ty)

/-- **Check one declaration.** It rewrites nothing. -/
def checkStep (s : CState) : SDecl → Option (SDecl × CState)
  | .tydef α A =>
      match elabTy [] s.abbrevs A with
      | some A' => some (.tydef α A, { s with abbrevs := (α, A') :: s.abbrevs })
      | none => none
  | .defn x A t =>
      match elabTy [] s.abbrevs A, elabTm [] [] s.abbrevs (s.globals.map (·.1)) t with
      | some A', some t' =>
          if infer 0 (s.globals.map (·.2)) t' = some A' then
            some (.defn x A t, { s with globals := (x, A') :: s.globals })
          else none
      | _, _ => none

/-- **The checker**, as a walk. -/
def checkWalk : Walk SDecl where
  State := CState
  init := ⟨[], []⟩
  step := checkStep

theorem checkStep_out {s : CState} {d d' : SDecl} {s' : CState}
    (h : checkStep s d = some (d', s')) : d' = d := by
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
  have h' : checkStep s d = some (d', s') := h
  have := checkStep_out h'
  subst this
  exact h

theorem checkWalk_idempotent : checkWalk.Idempotent :=
  checkWalk.idempotent_of_step checkWalk_stepIdempotent

/-- **A definition is accepted exactly when its translation is well typed** — against the
declarative judgement, in the context of the earlier definitions. -/
theorem checkStep_defn_iff (s : CState) (x : SName) (A : STy) (t : STm) :
    (checkStep s (.defn x A t)).isSome ↔
      ∃ A' t', elabTy [] s.abbrevs A = some A' ∧
        elabTm [] [] s.abbrevs (s.globals.map (·.1)) t = some t' ∧
        HasType 0 (s.globals.map (·.2)) t' A' := by
  simp only [checkStep]
  constructor
  · intro h
    split at h
    · rename_i A' t' hA ht
      split at h
      · rename_i hi
        exact ⟨A', t', hA, ht, infer_sound hi⟩
      · cases h
    · cases h
  · rintro ⟨A', t', hA, ht, hty⟩
    simp only [hA, ht, infer_complete hty, if_true]
    rfl

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
def evalStep (s : EState) : SDecl → Option (SDecl × EState)
  | .tydef α A =>
      match elabTy [] s.abbrevs A with
      | some A' => some (.tydef α A, { s with abbrevs := (α, A') :: s.abbrevs })
      | none => none
  | .defn x A t =>
      match elabTy [] s.abbrevs A, elabTm [] [] s.abbrevs (s.globals.map (·.name)) t with
      | some A', some t' =>
          if h : infer 0 s.ctx t' = some A' then
            some (.defn x A (rbTm 0 0 ((infer_sound h).subst s.env_typed).eval),
              { s with globals :=
                  ⟨x, A', ((infer_sound h).subst s.env_typed).eval,
                    ((infer_sound h).subst s.env_typed).eval_typed,
                    (Tm.eval_spec ((infer_sound h).subst s.env_typed).sn).2⟩ :: s.globals })
          else none
      | _, _ => none

/-- **The evaluator**, as a walk. -/
def evalWalk : Walk SDecl where
  State := EState
  init := ⟨[], []⟩
  step := evalStep

/-- What one evaluation step does: a `type` passes through; a `def` comes out as its value's
readback, the value pushed with its typing. -/
theorem evalStep_sound {s : EState} {d d' : SDecl} {s' : EState}
    (h : evalStep s d = some (d', s')) :
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
      some (.defn e.name A (rbTm 0 0 e.val), { s with globals := e :: s.globals }) := by
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
  have h' : evalStep s d = some (d', s') := h
  rcases evalStep_sound h' with ⟨α, A, A', rfl, rfl, hA, rfl⟩ | ⟨A, e, rfl, hA, _, rfl⟩
  · exact h'
  · exact evalStep_reduced s A e hA

/-- What checking would carry, read off what evaluation carries. -/
def EState.proj (s : EState) : CState := ⟨s.abbrevs, s.globals.map (fun e => (e.name, e.ty))⟩

/-- **Evaluation's output checks**, a step at a time, in the corresponding state. -/
theorem evalStep_check {s : EState} {d d' : SDecl} {s' : EState}
    (h : evalStep s d = some (d', s')) : checkStep s.proj d' = some (d', s'.proj) := by
  rcases evalStep_sound h with ⟨α, A, A', rfl, rfl, hA, rfl⟩ | ⟨A, e, rfl, hA, _, rfl⟩
  · simp only [checkStep, EState.proj, hA]
  · have hr : elabTm [] [] s.abbrevs ((s.globals.map (fun e => (e.name, e.ty))).map (·.1))
        (rbTm 0 0 e.val) = some e.val :=
      elabTm_rbTm e.val 0 0 s.abbrevs _ e.typed.scoped
    have hi : infer 0 ((s.globals.map (fun e => (e.name, e.ty))).map (·.2)) e.val = some e.ty :=
      infer_complete e.typed.weaken_closed
    simp only [checkStep, EState.proj, hA, hr, hi, if_true]
    rfl

theorem evalRunFrom_check : ∀ (s : EState) (ds out : List SDecl),
    evalWalk.runFrom s ds = some out → checkWalk.runFrom s.proj out = some out
  | s, [], out, h => by
      simp only [Walk.runFrom, Option.some.injEq] at h
      subst h
      rfl
  | s, d :: ds, out, h => by
      simp only [Walk.runFrom] at h
      cases hs : evalWalk.step s d with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some r =>
          obtain ⟨d', s'⟩ := r
          rw [hs] at h
          cases hr : evalWalk.runFrom s' ds with
          | none => simp [hr] at h
          | some rest =>
              simp only [hr, Option.map_some, Option.some.injEq] at h
              subst h
              have hc : checkWalk.step s.proj d' = some (d', s'.proj) := evalStep_check hs
              simp only [Walk.runFrom, hc, evalRunFrom_check s' ds rest hr, Option.map_some]

/-- **What evaluation produces still checks.** -/
theorem evalRun_check {p q : Program systemFLanguage} (h : evalWalk.run p = some q) :
    checkWalk.run q = some q :=
  (Walk.run_eq_some _).mpr (evalRunFrom_check evalWalk.init _ _ ((Walk.run_eq_some _).mp h))

/-- **The law, as the stage after checking.** -/
theorem evalWalk_lawfulOn : evalWalk.LawfulOn (fun p => checkWalk.run p = some p) where
  preserve _ _ _ h := evalRun_check h
  idem p q _ h := evalWalk.idempotent_of_step evalWalk_stepIdempotent p q h

/-! ## The front end -/

/-- After checking: the program as written, every definition well typed. -/
abbrev checkedStage : LambdaLab.Abstraction.Stage :=
  systemFLanguage.walkStage "checked program" checkWalk

/-- After evaluation: every definition's term in normal form. -/
abbrev evaluatedStage : LambdaLab.Abstraction.Stage :=
  systemFLanguage.walkStageOn "evaluated program" evalWalk (fun p => checkWalk.run p = some p)

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
def evaluateFile (s : String) : Option (evalWalk.FixedOn (fun p => checkWalk.run p = some p)) :=
  evalPipeline.abstract s.toList

/-- Render an evaluated program canonically. -/
def renderEvaluated (q : evalWalk.FixedOn (fun p => checkWalk.run p = some p)) : String :=
  String.ofList (evalPipeline.realize (evalPipeline.default (a := q)))

/-- **The front end round-trips**: rendering an evaluated program and reading it back
re-tokenizes, re-parses, re-checks and re-evaluates to exactly what you started with. -/
theorem evaluateFile_renderEvaluated (q : evalWalk.FixedOn (fun p => checkWalk.run p = some p)) :
    evaluateFile (renderEvaluated q) = some q := by
  show evalPipeline.abstract (String.ofList (evalPipeline.realize (evalPipeline.default (a := q)))).toList = some q
  rw [String.toList_ofList]
  exact evalPipeline.abstract_realize q evalPipeline.default

end LambdaLab.Languages.SystemF
