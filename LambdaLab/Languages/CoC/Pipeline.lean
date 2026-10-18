import LambdaLab.Languages.CoC.Surface
import LambdaLab.Languages.CoC.DeBruijn.Check
import LambdaLab.Languages.CoC.Named.Typing
import LambdaLab.Semantics.Walk

/-!
# CoC — from what is written to what it means

The surface (`Surface.lean`) parses into the named calculus (`Named/`); the checker and the
evaluator run on the de Bruijn core (`DeBruijn/`). This file connects them, and runs programs.

## Translation

`elab` is `Named.Tm.toDB` extended to programs (`elab_eq_toDB`): a bound name becomes its de
Bruijn index, and a free name is an earlier definition, **replaced by its value**. Definitions are
transparent — a later term may depend on what an earlier one *is*, not just on its type (`def T :
* := Nat` makes `T` and `Nat` interchangeable) — and inlining is the simplest semantics with that
property. Every definition's value is closed, so inlining it under binders needs no shifting.

## Readback

`rb` prints a core term back as a named one: each binder is named by its depth — `x0, x1, …` — so
no binder shadows another on any path; except that a product whose bound variable is unused gets
the name `A → B` stands for (`arrowName`), so it prints as an arrow. Reading the result back gives
the term again (`elab_rb`), for every term whose free variables are in scope — closed ones in
particular — which is what makes evaluation idempotent.

## Two walks

* **checking** (`checkWalk`): each definition is translated and its term checked against its
  declared type in the empty context — the earlier definitions having been inlined. It rewrites
  nothing. A definition is accepted exactly when its translation is well typed
  (`checkStep_iff`); with nothing declared before it, exactly when the *named* judgement holds of
  what was parsed (`checkStep_named`).
* **evaluation** (`evalWalk`), after checking: each definition's term, with the earlier
  definitions' values inlined, is normalized — total, by strong normalization — and written back.
  The state carries each value with its typing and normality.

Evaluation is idempotent a step at a time: a written-back normal form reads back as itself, is
closed, and is normal. And what evaluation produces still checks (`evalRun_check`).
-/

namespace LambdaLab.Languages.CoC

open LambdaLab.Pipeline
open LambdaLab.Parser.Numeral (isDigitChar natTok natOfTok isNatTok)
open LambdaLab.Semantics (Walk)
open LambdaLab.Nominal (freshFor freshFor_not_in)
open LambdaLab.Languages.CoC.DeBruijn

/-! ## Name lookup -/

/-- The position of a name in a binder list, innermost first. -/
def lookupIdx (n : SName) : List SName → Option Nat
  | [] => none
  | m :: ms => if m = n then some 0 else (lookupIdx n ms).map (· + 1)

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

/-! ## Translation -/

/-- Translate a term: bound names to indices, earlier definitions to their values. -/
def elabTm (bs : List SName) (gl : List (SName × Tm)) : STm → Option Tm
  | .var x =>
      match lookupIdx x bs with
      | some i => some (.var i)
      | none => (gl.find? (fun p => p.1 = x)).map (·.2)
  | .sort s => some (.sort s)
  | .pi x A B =>
      match elabTm bs gl A, elabTm (x :: bs) gl B with
      | some A', some B' => some (.pi A' B')
      | _, _ => none
  | .lam x A b =>
      match elabTm bs gl A, elabTm (x :: bs) gl b with
      | some A', some b' => some (.lam A' b')
      | _, _ => none
  | .app f a =>
      match elabTm bs gl f, elabTm bs gl a with
      | some f', some a' => some (.app f' a')
      | _, _ => none

/-- **With nothing declared, translation is the named calculus's**: a translation that succeeds is
`Named.Tm.toDB`. -/
theorem elab_eq_toDB : ∀ (t : STm) (bs : List SName) (t' : Tm),
    elabTm bs [] t = some t' → t' = Named.Tm.toDB bs t
  | .var x, bs, t', h => by
      simp only [elabTm] at h
      split at h
      · rename_i i hi
        cases h
        simp only [Named.Tm.toDB, lookupIdx_eq_some hi]
      · simp at h
  | .sort _, _, _, h => by simp only [elabTm, Option.some.injEq] at h; subst h; rfl
  | .pi x A B, bs, t', h => by
      simp only [elabTm] at h
      split at h
      · rename_i A' B' hA hB
        cases h
        simp only [Named.Tm.toDB, elab_eq_toDB A bs A' hA, elab_eq_toDB B (x :: bs) B' hB]
      · cases h
  | .lam x A b, bs, t', h => by
      simp only [elabTm] at h
      split at h
      · rename_i A' b' hA hb
        cases h
        simp only [Named.Tm.toDB, elab_eq_toDB A bs A' hA, elab_eq_toDB b (x :: bs) b' hb]
      · cases h
  | .app f a, bs, t', h => by
      simp only [elabTm] at h
      split at h
      · rename_i f' a' hf ha
        cases h
        simp only [Named.Tm.toDB, elab_eq_toDB f bs f' hf, elab_eq_toDB a bs a' ha]
      · cases h

/-! ## Canonical names -/

theorem coc_digit_word : ∀ c, isDigitChar c = true → cocLex.word c = true :=
  LambdaLab.Parser.IsoParser.Lexicon.make_digit_word

/-- The name of the binder at depth `k`: `x0`, `x1`, … Never reserved, because no reserved token
has that shape. -/
def tmName (k : Nat) : SName :=
  ⟨natTok 'x' (by decide) coc_digit_word k, by
    show decide (natTok 'x' (by decide) coc_digit_word k ∉ cocReserved) = true
    rw [decide_eq_true_eq]
    intro hmem
    have h1 : ∀ r ∈ cocReserved, isNatTok 'x' r = false := by decide
    have h2 := h1 _ hmem
    rw [LambdaLab.Parser.Numeral.isNatTok_natTok] at h2
    cases h2⟩

theorem tmName_inj {j k : Nat} (h : tmName j = tmName k) : j = k := by
  have := congrArg (fun n : SName => natOfTok n.val) h
  simp only [tmName, LambdaLab.Parser.Numeral.natOfTok_natTok] at this
  exact this

/-! ## Readback -/

/-- Does the variable `n` occur free? -/
def DeBruijn.Tm.hasFree (n : Nat) : Tm → Bool
  | .var i => i == n
  | .sort _ => false
  | .pi A B => A.hasFree n || B.hasFree (n + 1)
  | .lam A t => A.hasFree n || t.hasFree (n + 1)
  | .app t u => t.hasFree n || u.hasFree n

/-- **Print a core term with names**: binders by depth, an unused product binder as an arrow's. -/
def rb (bs : List SName) : Tm → STm
  | .var i => .var (Named.nameAt bs i)
  | .sort s => .sort s
  | .pi A B =>
      if B.hasFree 0 then .pi (tmName bs.length) (rb bs A) (rb (tmName bs.length :: bs) B)
      else .pi (arrowName (rb (tmName bs.length :: bs) B)) (rb bs A) (rb (tmName bs.length :: bs) B)
  | .lam A t => .lam (tmName bs.length) (rb bs A) (rb (tmName bs.length :: bs) t)
  | .app t u => .app (rb bs t) (rb bs u)

/-- The names of a term's free variables are where readback says: each free variable is named by
its depth, and nothing closer has that name. -/
def RbInv (bs : List SName) (t : Tm) : Prop :=
  ∀ i, t.hasFree i = true → i < bs.length ∧ Named.nameAt bs i = tmName (bs.length - 1 - i) ∧
    ∀ j < i, Named.nameAt bs j ≠ Named.nameAt bs i

theorem lookupIdx_nameAt : ∀ {bs : List SName} {i : Nat}, i < bs.length →
    (∀ j < i, Named.nameAt bs j ≠ Named.nameAt bs i) → lookupIdx (Named.nameAt bs i) bs = some i
  | [], _, h, _ => by simp at h
  | b :: bs, 0, _, _ => by simp [Named.nameAt, lookupIdx]
  | b :: bs, i + 1, h, hne => by
      have hb : b ≠ Named.nameAt bs i := by
        have := hne 0 (by omega)
        simpa [Named.nameAt] using this
      simp only [Named.nameAt, lookupIdx, if_neg hb]
      rw [lookupIdx_nameAt (by simp only [List.length_cons] at h; omega) (fun j hj => by
        have := hne (j + 1) (by omega)
        simpa [Named.nameAt] using this)]
      rfl

/-- The invariant survives a binder named by depth. -/
theorem RbInv.cons_depth {bs : List SName} {t : Tm} (h : ∀ i, t.hasFree (i + 1) = true →
    i < bs.length ∧ Named.nameAt bs i = tmName (bs.length - 1 - i) ∧
      ∀ j < i, Named.nameAt bs j ≠ Named.nameAt bs i) :
    RbInv (tmName bs.length :: bs) t := by
  intro i hi
  cases i with
  | zero => exact ⟨by simp, by simp [Named.nameAt], fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ i =>
      obtain ⟨hlt, hname, hne⟩ := h i hi
      refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
      · simp only [Named.nameAt, List.length_cons, hname]
        congr 1
        omega
      · intro j hj
        cases j with
        | zero =>
            simp only [Named.nameAt, hname]
            intro e
            have := tmName_inj e
            omega
        | succ j =>
            simp only [Named.nameAt]
            exact hne j (by omega)

/-- Readback depends only on the names of the free variables. -/
theorem rb_congr : ∀ (t : Tm) (bs bs' : List SName), bs.length = bs'.length →
    (∀ i, t.hasFree i = true → Named.nameAt bs i = Named.nameAt bs' i) → rb bs t = rb bs' t
  | .var i, _, _, _, h => by simp only [rb, h i (by simp [Tm.hasFree])]
  | .sort _, _, _, _, _ => rfl
  | .pi A B, bs, bs', hl, h => by
      have hA := rb_congr A bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi]))
      have hB := rb_congr B (tmName bs.length :: bs) (tmName bs.length :: bs') (by simp [hl])
        (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact h i (by simp [Tm.hasFree, hi]))
      simp only [rb, hA, hB]
      rw [hl]
  | .lam A t, bs, bs', hl, h => by
      have hA := rb_congr A bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi]))
      have ht := rb_congr t (tmName bs.length :: bs) (tmName bs.length :: bs') (by simp [hl])
        (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact h i (by simp [Tm.hasFree, hi]))
      simp only [rb, hA, ht]
      rw [hl]
  | .app t u, bs, bs', hl, h => by
      simp only [rb, rb_congr t bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi])),
        rb_congr u bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi]))]

/-- **A free variable's name is free in the readback.** -/
theorem rb_fv : ∀ (t : Tm) (bs : List SName), RbInv bs t →
    ∀ i, t.hasFree i = true → Named.nameAt bs i ∈ (rb bs t).fv
  | .var i, _, _, j, hj => by
      simp only [Tm.hasFree, beq_iff_eq] at hj
      subst hj
      simp [rb, Named.Tm.fv]
  | .sort _, _, _, _, hj => by simp [Tm.hasFree] at hj
  | .pi A B, bs, hinv, i, hi => by
      have hB := RbInv.cons_depth (bs := bs) (t := B) (fun i hi => hinv i (by
        simp [Tm.hasFree, hi]))
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      have hne : Named.nameAt bs i ≠ tmName bs.length := by
        obtain ⟨hlt, hname, _⟩ := hinv i (by simp [Tm.hasFree, hi])
        rw [hname]
        intro e
        have := tmName_inj e
        omega
      unfold rb
      split
      · rcases hi with hi | hi
        · exact List.mem_append_left _ (rb_fv A bs (fun j hj => hinv j (by
            simp [Tm.hasFree, hj])) i hi)
        · refine List.mem_append_right _ (List.mem_filter.mpr ⟨?_, by simpa using hne⟩)
          exact rb_fv B _ hB (i + 1) hi
      · rcases hi with hi | hi
        · exact List.mem_append_left _ (rb_fv A bs (fun j hj => hinv j (by
            simp [Tm.hasFree, hj])) i hi)
        · have hm := rb_fv B _ hB (i + 1) hi
          refine List.mem_append_right _ (List.mem_filter.mpr ⟨hm, ?_⟩)
          simp only [decide_eq_true_eq]
          intro e
          exact freshFor_not_in _ (e ▸ hm)
  | .lam A t, bs, hinv, i, hi => by
      have ht := RbInv.cons_depth (bs := bs) (t := t) (fun i hi => hinv i (by
        simp [Tm.hasFree, hi]))
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      have hne : Named.nameAt bs i ≠ tmName bs.length := by
        obtain ⟨hlt, hname, _⟩ := hinv i (by simp [Tm.hasFree, hi])
        rw [hname]
        intro e
        have := tmName_inj e
        omega
      simp only [rb]
      rcases hi with hi | hi
      · exact List.mem_append_left _ (rb_fv A bs (fun j hj => hinv j (by
          simp [Tm.hasFree, hj])) i hi)
      · refine List.mem_append_right _ (List.mem_filter.mpr ⟨?_, by simpa using hne⟩)
        exact rb_fv t _ ht (i + 1) hi
  | .app t u, bs, hinv, i, hi => by
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      simp only [rb, Named.Tm.fv]
      rcases hi with hi | hi
      · exact List.mem_append_left _ (rb_fv t bs (fun j hj => hinv j (by
          simp [Tm.hasFree, hj])) i hi)
      · exact List.mem_append_right _ (rb_fv u bs (fun j hj => hinv j (by
          simp [Tm.hasFree, hj])) i hi)

/-- **Reading a printed term back gives the term**, whatever definitions are in scope — none is
ever consulted, because every name is bound. -/
theorem elab_rb : ∀ (t : Tm) (bs : List SName) (gl : List (SName × Tm)), RbInv bs t →
    elabTm bs gl (rb bs t) = some t
  | .var i, bs, gl, hinv => by
      obtain ⟨hlt, _, hne⟩ := hinv i (by simp [Tm.hasFree])
      simp only [rb, elabTm, lookupIdx_nameAt hlt hne]
  | .sort _, _, _, _ => rfl
  | .pi A B, bs, gl, hinv => by
      have hA := elab_rb A bs gl (fun j hj => hinv j (by simp [Tm.hasFree, hj]))
      have hBinv := RbInv.cons_depth (bs := bs) (t := B) (fun i hi => hinv i (by
        simp [Tm.hasFree, hi]))
      unfold rb
      split
      · simp only [elabTm, hA, elab_rb B _ gl hBinv]
      · rename_i hB0
        -- the binder is unused, so the readback is the same under the arrow's name
        generalize hz : arrowName (rb (tmName bs.length :: bs) B) = z
        have hzfresh : z ∉ (rb (tmName bs.length :: bs) B).fv := hz ▸ freshFor_not_in _
        have hsame : rb (tmName bs.length :: bs) B = rb (z :: bs) B :=
          rb_congr B _ _ (by simp) (fun i hi => by
            cases i with
            | zero => simp [hB0] at hi
            | succ i => rfl)
        have hzinv : RbInv (z :: bs) B := by
          intro i hi
          cases i with
          | zero => simp [hB0] at hi
          | succ i =>
              obtain ⟨hlt, hname, hne⟩ := hBinv (i + 1) hi
              refine ⟨hlt, by simpa [Named.nameAt] using hname, fun j hj => ?_⟩
              cases j with
              | zero =>
                  simp only [Named.nameAt]
                  intro e
                  have hm := rb_fv B _ hBinv (i + 1) hi
                  simp only [Named.nameAt] at hm
                  exact hzfresh (e ▸ hm)
              | succ j =>
                  have := hne (j + 1) hj
                  simpa [Named.nameAt] using this
        rw [hsame]
        simp only [elabTm, hA, elab_rb B _ gl hzinv]
  | .lam A t, bs, gl, hinv => by
      have hA := elab_rb A bs gl (fun j hj => hinv j (by simp [Tm.hasFree, hj]))
      have htinv := RbInv.cons_depth (bs := bs) (t := t) (fun i hi => hinv i (by
        simp [Tm.hasFree, hi]))
      simp only [rb, elabTm, hA, elab_rb t _ gl htinv]
  | .app t u, bs, gl, hinv => by
      simp only [rb, elabTm, elab_rb t bs gl (fun j hj => hinv j (by simp [Tm.hasFree, hj])),
        elab_rb u bs gl (fun j hj => hinv j (by simp [Tm.hasFree, hj]))]

theorem DeBruijn.Tm.hasFree_lt : ∀ {t : Tm} {n i : Nat}, t.Scoped n → t.hasFree i = true → i < n
  | .var _, _, _, h, hi => by
      simp only [Tm.hasFree, beq_iff_eq] at hi
      subst hi
      exact h
  | .sort _, _, _, _, hi => by simp [Tm.hasFree] at hi
  | .pi _ _, _, i, ⟨hA, hB⟩, hi => by
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact DeBruijn.Tm.hasFree_lt hA hi
      · have := DeBruijn.Tm.hasFree_lt hB hi; omega
  | .lam _ _, _, i, ⟨hA, ht⟩, hi => by
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact DeBruijn.Tm.hasFree_lt hA hi
      · have := DeBruijn.Tm.hasFree_lt ht hi; omega
  | .app _ _, _, _, ⟨ht, hu⟩, hi => by
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact DeBruijn.Tm.hasFree_lt ht hi
      · exact DeBruijn.Tm.hasFree_lt hu hi

/-- A closed term reads back and translates to itself. -/
theorem elab_rb_closed {t : Tm} (h : t.Scoped 0) (gl : List (SName × Tm)) :
    elabTm [] gl (rb [] t) = some t :=
  elab_rb t [] gl (fun _ hi => absurd (DeBruijn.Tm.hasFree_lt h hi) (Nat.not_lt_zero _))

/-! ## Checking -/

/-- What checking carries: each earlier definition's name and translated value. -/
abbrev CState := List (SName × Tm)

/-- The diagnostic for a definition whose term does not have its type. -/
def illTypedMsg : String := "this definition does not have its declared type"

/-- The diagnostic for a definition that does not translate: its type, or else its term, names
something neither bound nor defined before it. -/
def unknownNameMsg (inType : Bool) : String :=
  s!"{if inType then "the declared type" else "the term"} mentions a name that is neither \
    bound nor an earlier definition"

/-- **Check one definition.** It rewrites nothing. -/
def checkStep (s : CState) (d : CDecl) : Except String (CDecl × CState) :=
  match elabTm [] s d.ty, elabTm [] s d.tm with
  | some T', some e' =>
      match decHasType [] Wf.nil e' T' with
      | isTrue _ => .ok (d, (d.name, e') :: s)
      | isFalse _ => .error illTypedMsg
  | T', _ => .error (unknownNameMsg T'.isNone)

/-- **The checker**, as a walk. -/
def checkWalk : Walk CDecl where
  State := CState
  init := []
  step := checkStep

theorem checkStep_out {s : CState} {d d' : CDecl} {s' : CState}
    (h : checkStep s d = .ok (d', s')) : d' = d := by
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

/-- **A definition is accepted exactly when its translation is well typed.** -/
theorem checkStep_iff (s : CState) (d : CDecl) :
    (∃ r, checkStep s d = .ok r) ↔
      ∃ T' e', elabTm [] s d.ty = some T' ∧ elabTm [] s d.tm = some e' ∧ HasType [] e' T' := by
  simp only [checkStep]
  constructor
  · rintro ⟨r, h⟩
    split at h
    · rename_i T' e' hT he
      split at h
      · rename_i hty _
        exact ⟨T', e', hT, he, hty⟩
      · cases h
    · cases h
  · rintro ⟨T', e', hT, he, hty⟩
    simp only [hT, he]
    split
    · exact ⟨_, rfl⟩
    · rename_i hn _; exact absurd hty hn

/-- **With nothing declared before it, a definition the checker accepts is well typed in the named
calculus** — the parsed term at the parsed type, no translation in sight. -/
theorem checkStep_named {d : CDecl} (h : ∃ r, checkStep [] d = .ok r) :
    Named.HasType [] d.tm d.ty := by
  obtain ⟨T', e', hT, he, hty⟩ := (checkStep_iff [] d).mp h
  have e₁ := elab_eq_toDB d.ty [] T' hT
  have e₂ := elab_eq_toDB d.tm [] e' he
  subst e₁ e₂
  exact (Named.hasType_iff_toDB (Γ := []) trivial).mpr hty

/-! ## Evaluation -/

/-- An earlier definition, evaluated: its value, closed, typed and normal. -/
structure EEntry where
  name : SName
  ty : Tm
  val : Tm
  typed : HasType [] val ty
  normal : val.Normal

theorem EEntry.ext {a b : EEntry} (hn : a.name = b.name) (ht : a.ty = b.ty)
    (hv : a.val = b.val) : a = b := by
  cases a; cases b
  simp only at hn ht hv
  subst hn ht hv
  rfl

/-- What evaluation carries: the earlier definitions' values. -/
abbrev EState := List EEntry

/-- The values, as translation looks them up. -/
def EState.vals (s : EState) : List (SName × Tm) := s.map (fun e => (e.name, e.val))

/-- **Evaluate one definition**: translate it with the earlier values inlined, check it, normalize
it — total, the closed term being well typed — and write it back with generated names. -/
def evalStep (s : EState) (d : CDecl) : Except String (CDecl × EState) :=
  match elabTm [] s.vals d.ty, elabTm [] s.vals d.tm with
  | some T', some e' =>
      match decHasType [] Wf.nil e' T' with
      | isTrue h =>
          .ok (⟨d.name, d.ty, rb [] (h.eval Wf.nil)⟩,
            ⟨d.name, T', h.eval Wf.nil, h.eval_typed Wf.nil,
              (Tm.eval_spec (h.sn Wf.nil)).2⟩ :: s)
      | isFalse _ => .error illTypedMsg
  | T', _ => .error (unknownNameMsg T'.isNone)

/-- **The evaluator**, as a walk. -/
def evalWalk : Walk CDecl where
  State := EState
  init := []
  step := evalStep

/-- What one evaluation step does: a definition comes out as its value's readback, the value
pushed with its typing. -/
theorem evalStep_sound {s : EState} {d d' : CDecl} {s' : EState}
    (h : evalStep s d = .ok (d', s')) :
    ∃ e : EEntry, d' = ⟨e.name, d.ty, rb [] e.val⟩ ∧ e.name = d.name ∧
      elabTm [] s.vals d.ty = some e.ty ∧ s' = e :: s := by
  simp only [evalStep] at h
  split at h
  · rename_i T' e' hT he
    split at h
    · cases h
      exact ⟨_, rfl, rfl, hT, rfl⟩
    · cases h
  · cases h

/-- **An evaluated definition evaluates to itself**, with the same entry: its readback reads back
as its value, which is closed and normal. -/
theorem evalStep_reduced (s : EState) (T : STm) (e : EEntry)
    (hT : elabTm [] s.vals T = some e.ty) :
    evalStep s ⟨e.name, T, rb [] e.val⟩ = .ok (⟨e.name, T, rb [] e.val⟩, e :: s) := by
  have hr : elabTm [] s.vals (rb [] e.val) = some e.val := elab_rb_closed e.typed.scoped _
  simp only [evalStep, hT, hr]
  split
  · rename_i h _
    have hv : h.eval Wf.nil = e.val := Tm.eval_of_normal _ e.normal
    have he : (⟨e.name, e.ty, h.eval Wf.nil, h.eval_typed Wf.nil,
        (Tm.eval_spec (h.sn Wf.nil)).2⟩ : EEntry) = e := EEntry.ext rfl rfl hv
    rw [he, hv]
  · rename_i hn _
    exact absurd e.typed hn

/-- **Idempotence, a step at a time.** -/
theorem evalWalk_stepIdempotent : evalWalk.StepIdempotent := by
  intro s d d' s' h
  have h' : evalStep s d = .ok (d', s') := h
  obtain ⟨e, rfl, hn, hT, rfl⟩ := evalStep_sound h'
  show evalStep s ⟨e.name, d.ty, rb [] e.val⟩ = .ok _
  exact evalStep_reduced s d.ty e hT

/-- What checking would carry, read off what evaluation carries. -/
def EState.proj (s : EState) : CState := s.vals

/-- **Evaluation's output checks**, a step at a time, in the corresponding state. -/
theorem evalStep_check {s : EState} {d d' : CDecl} {s' : EState}
    (h : evalStep s d = .ok (d', s')) : checkStep s.proj d' = .ok (d', s'.proj) := by
  obtain ⟨e, rfl, _, hT, rfl⟩ := evalStep_sound h
  have hr : elabTm [] s.vals (rb [] e.val) = some e.val := elab_rb_closed e.typed.scoped _
  simp only [checkStep, EState.proj, hT, hr]
  split
  · rfl
  · rename_i hn _
    exact absurd e.typed hn

/-- **What evaluation produces still checks**: checking accepts evaluation's output a step at a
time (`evalStep_check`), so it accepts it whole (`Walk.runFrom_sim`). -/
theorem evalRun_check {p q : Program cocLanguage} (h : evalWalk.run p = .ok q) :
    checkWalk.run q = .ok q :=
  (Walk.run_eq_ok _).mpr (evalWalk.runFrom_sim checkWalk EState.proj
    (fun _ _ _ _ hs => evalStep_check hs) _ _ _ ((Walk.run_eq_ok _).mp h))

/-- **The law, as the stage after checking.** -/
theorem evalWalk_lawfulOn : evalWalk.LawfulOn (fun p => checkWalk.run p = .ok p) where
  preserve _ _ _ h := evalRun_check h
  idem p q _ h := evalWalk.idempotent_of_step evalWalk_stepIdempotent p q h

/-! ## The front end -/

/-- After evaluation: every definition's term in normal form. -/
abbrev evaluatedStage : LambdaLab.Abstraction.Stage :=
  cocLanguage.walkStageOn "evaluated program" evalWalk (fun p => checkWalk.run p = .ok p)

/-- **The whole front end, stage by stage**: source, tokens, program, checked program, evaluated
program. -/
def cocChain : LambdaLab.Abstraction.Chain sourceStage evaluatedStage :=
  (cocLanguage.walkChain checkWalk checkWalk_idempotent "checked program").cons
    (Z := evaluatedStage) (cocLanguage.walkCellOn evalWalk evalWalk_lawfulOn)

/-- **Characters to an evaluated program**, in `Abs`: one morphism, so one round-trip law. -/
def evalPipeline :=
  (cocLanguage.walkPipeline checkWalk checkWalk_idempotent).comp
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
  show evalPipeline.abstract
    (String.ofList (evalPipeline.realize (evalPipeline.default (a := q)))).toList = .ok q
  rw [String.toList_ofList]
  exact evalPipeline.abstract_realize q evalPipeline.default

end LambdaLab.Languages.CoC
