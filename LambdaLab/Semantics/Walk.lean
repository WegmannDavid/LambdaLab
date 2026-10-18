import LambdaLab.Abstraction.Basic
import LambdaLab.NEList

/-!
# Walks — a state carried through the declarations

A program is a run of declarations, and whatever it means is worked out left to right: each
declaration is read in the light of the ones before it and leaves something behind for the ones
after. A `Walk` is exactly that and nothing more — a `State`, where it starts, and what one
declaration does to it.

Nothing here knows what a declaration is, what a type is, or that there is such a thing as a type
system. For a typed language the state records the declared types (a context), and an evaluator's
also records the reduced bodies so that later declarations can inline them. For a language of
numeric assignments it is a map from names to numbers. All three are walks, and all three get the
same stage out of this file.

## A step rewrites its declaration

`step` does not merely accept or reject: it hands back a declaration *of the same language* — the
elaborated one, the evaluated one. That is what lets the result be printed by the language's own
printer and read back by its own parser, which is how a pipeline's round-trip law can cover every
stage at once. A walk whose answer is "the final map" expresses it as the program of literal
assignments that produces that map.

One declaration in, one out. A program therefore stays non-empty without anyone having to say so.

## The one law: idempotence

A stage needs a canonical surface form for each value it produces (`Abstraction.default`). For a
walk the value is a program, and the canonical form is that program itself — which is legitimate
exactly when running the walk on its own output changes nothing. So that is the law
(`Idempotent`), and the stage's target is the programs the walk leaves unchanged (`Fixed`).

For many walks idempotence holds a step at a time: handed its own output in the state it was in, a
step gives the same output and moves to the same state (`StepIdempotent`, and
`idempotent_of_step`). Not for all of them — an elaborator's state records the metavariables it has
solved, and re-elaborating a solved declaration records a different (equally irrelevant) solution.
Such a walk proves the program-level law directly.

## A walk after a walk

The second walk of a pipeline runs on the first one's output, not on arbitrary programs, so its
source is a subtype `{ p // P p }` and its law is relative to `P` (`LawfulOn`): from a program
satisfying `P` it must produce one that does too (`preserve`), and be idempotent there (`idem`).
`stage` is the first walk's stage, `stageOn` every later one's.
-/

set_option autoImplicit false

namespace LambdaLab.Semantics

open LambdaLab (Abstraction)

/-- **A semantics, as a walk**: a state, where it starts, and what one declaration does to it —
reject it, saying why, or rewrite it and hand on the next state. -/
structure Walk (D : Type) where
  /-- What is carried from one declaration to the next. -/
  State : Type
  /-- The state before the first declaration. -/
  init : State
  /-- Process one declaration. A rejection's message is informal: no law mentions it. -/
  step : State → D → Except String (D × State)

namespace Walk

variable {D : Type} (w : Walk D)

/-- Run the walk over a list of declarations from a given state. A rejection says which
declaration of the list was rejected, and why. -/
def runFrom : w.State → List D → Except (Nat × String) (List D)
  | _, [] => .ok []
  | s, d :: ds =>
      match w.step s d with
      | .error m => .error (0, m)
      | .ok (d', s') =>
          match runFrom s' ds with
          | .error (i, m) => .error (i + 1, m)
          | .ok ds' => .ok (d' :: ds')

/-- **Run the walk over a program**, from `init`. A rejection points at the declaration. -/
def run (p : NEList D) : Except Diag (NEList D) :=
  match w.runFrom w.init p.toList with
  | .error (i, m) => .error { msg := m, loc := .decl i }
  | .ok [] => .error { msg := "a walk dropped every declaration" }
  | .ok (d :: ds) => .ok (d, ds)

theorem runFrom_length : ∀ (s : w.State) (ds ds' : List D), w.runFrom s ds = .ok ds' →
    ds'.length = ds.length
  | _, [], ds', h => by simp only [runFrom, Except.ok.injEq] at h; subst h; rfl
  | s, d :: ds, ds', h => by
      simp only [runFrom] at h
      split at h
      · cases h
      · rename_i d' s' _
        split at h
        · cases h
        · rename_i rest hrest
          cases h
          simp [runFrom_length s' ds rest hrest]

theorem run_eq_ok {p q : NEList D} :
    w.run p = .ok q ↔ w.runFrom w.init p.toList = .ok q.toList := by
  unfold run
  split
  · rename_i h; simp [h]
  · rename_i h
    have := runFrom_length w _ _ _ h
    simp [NEList.toList] at this
  · rename_i d ds h
    rw [h]
    obtain ⟨a, as⟩ := q
    simp [NEList.toList]

/-! ## Idempotence -/

/-- **The law**: running the walk on its own output changes nothing. -/
def Idempotent : Prop := ∀ p q, w.run p = .ok q → w.run q = .ok q

/-- **Idempotence a step at a time**: handed its own output in the state it was in, a step gives
that output back and moves to the same state. -/
def StepIdempotent : Prop :=
  ∀ s d d' s', w.step s d = .ok (d', s') → w.step s d' = .ok (d', s')

theorem runFrom_cons_ok {s : w.State} {d : D} {ds : List D} {out : List D}
    (h : w.runFrom s (d :: ds) = .ok out) :
    ∃ d' s' rest, w.step s d = .ok (d', s') ∧ w.runFrom s' ds = .ok rest ∧ out = d' :: rest := by
  simp only [runFrom] at h
  split at h
  · cases h
  · rename_i d' s' hs
    split at h
    · cases h
    · rename_i rest hrest
      cases h
      exact ⟨d', s', rest, hs, hrest, rfl⟩

theorem runFrom_cons_of {s : w.State} {d d' : D} {s' : w.State} {ds rest : List D}
    (hs : w.step s d = .ok (d', s')) (hr : w.runFrom s' ds = .ok rest) :
    w.runFrom s (d :: ds) = .ok (d' :: rest) := by
  simp only [runFrom, hs, hr]

/-- **Simulation**: if whatever `w` does to a declaration, `v` accepts the result in the
corresponding state, moving to the corresponding state, then `v` accepts `w`'s output whole. -/
theorem runFrom_sim (v : Walk D) (π : w.State → v.State)
    (hsim : ∀ s d d' s', w.step s d = .ok (d', s') → v.step (π s) d' = .ok (d', π s')) :
    ∀ (s : w.State) (ds out : List D), w.runFrom s ds = .ok out → v.runFrom (π s) out = .ok out
  | _, [], out, h => by simp only [runFrom, Except.ok.injEq] at h; subst h; rfl
  | s, d :: ds, out, h => by
      obtain ⟨d', s', rest, hs, hr, rfl⟩ := w.runFrom_cons_ok h
      exact v.runFrom_cons_of (hsim s d d' s' hs) (runFrom_sim v π hsim s' ds rest hr)

theorem runFrom_idempotent (h : w.StepIdempotent) :
    ∀ (s : w.State) (ds ds' : List D), w.runFrom s ds = .ok ds' → w.runFrom s ds' = .ok ds' :=
  w.runFrom_sim w id h

/-- Step-wise idempotence is enough for the law. -/
theorem idempotent_of_step (h : w.StepIdempotent) : w.Idempotent := by
  intro p q hpq
  rw [run_eq_ok] at hpq ⊢
  exact w.runFrom_idempotent h _ _ _ hpq

/-- **The law, for a walk run after another stage**: on programs satisfying `P` (what the earlier
stage guarantees) the walk keeps `P` and is idempotent. -/
structure LawfulOn (P : NEList D → Prop) : Prop where
  /-- What the walk produces from a `P`-program is a `P`-program. -/
  preserve : ∀ p q, P p → w.run p = .ok q → P q
  /-- …and running the walk on it changes nothing. -/
  idem : ∀ p q, P p → w.run p = .ok q → w.run q = .ok q

/-! ## Getting past a rejection

For diagnostics only, and informal. A rejected declaration is reported and skipped — the state
stays as it was, as though the declaration had not been written — and the rest are run as usual,
so one bad declaration does not hide the others. What a later declaration says about the skipped
one's name is then reported in its turn. -/

/-- Run the walk past its rejections: the rejections, by position, and the positions of the
declarations it accepted. -/
def runSkip : w.State → List D → Nat → List (Nat × String) × List Nat
  | _, [], _ => ([], [])
  | s, d :: ds, i =>
      match w.step s d with
      | .error m =>
          let r := runSkip s ds (i + 1)
          ((i, m) :: r.1, r.2)
      | .ok (_, s') =>
          let r := runSkip s' ds (i + 1)
          (r.1, i :: r.2)

/-- Point the `j`-th declaration of a sub-program at the declaration it was, `kept[j]`. -/
def declsFrom (kept : List Nat) : Loc → Loc
  | .decl j => .decl ((kept[j]?).getD j)
  | l => l

/-- **Best effort**: every rejection, and — when some declaration was rejected — what `run` makes of
the declarations that were not. -/
def recoverWith {α : Type} (run : NEList D → Except Diag α) (p : NEList D) :
    List Diag × Option (α × (Loc → Loc)) :=
  let r := w.runSkip w.init p.toList 0
  if r.1.isEmpty then
    match run p with
    | .ok q => ([], some (q, id))
    | .error d => ([d], none)
  else
    let diags := r.1.map fun e => ({ msg := e.2, loc := .decl e.1 } : Diag)
    match r.2.filterMap (p.toList[·]?) with
    | [] => (diags, none)
    | d :: ds =>
        match run (d, ds) with
        | .ok q => (diags, some (q, declsFrom r.2))
        | .error d' => (diags ++ [d'], none)

/-! ## The stage -/

/-- **What the walk produces**: the programs it leaves unchanged. For an idempotent walk this is
exactly its image. -/
def Fixed : Type := { q : NEList D // w.run q = .ok q }

/-- The walk, landing in what it produces. -/
def toFixed (h : w.Idempotent) (p : NEList D) : Except Diag w.Fixed :=
  match hp : w.run p with
  | .error d => .error d
  | .ok q => .ok ⟨q, h p q hp⟩

theorem toFixed_eq_ok (h : w.Idempotent) {p : NEList D} {q : w.Fixed} :
    w.toFixed h p = .ok q ↔ w.run p = .ok q.val := by
  unfold toFixed
  split
  · rename_i hp
    constructor
    · intro e; cases e
    · intro e; rw [hp] at e; cases e
  · rename_i q' hp
    constructor
    · intro e; cases e; exact hp
    · intro e; rw [hp] at e; cases e; rfl

/-- **A walk as a stage**: programs to the programs the walk leaves unchanged. Each output is its
own canonical source — the walk changes nothing about it — and the annotation over an output is
every program the walk takes there, so the stage is complete by construction
(`Abstraction.ofFibers`). -/
def stage (h : w.Idempotent) :
    Abstraction (NEList D) w.Fixed (fun q => { p : NEList D // w.toFixed h p = .ok q }) :=
  { Abstraction.ofFibers (w.toFixed h) (fun q => ⟨q.val, (w.toFixed_eq_ok h).mpr q.property⟩) with
    recover := w.recoverWith (w.toFixed h) }

/-- What the walk produces from `P`-programs: those it leaves unchanged that still satisfy `P`. -/
def FixedOn (P : NEList D → Prop) : Type := { q : NEList D // P q ∧ w.run q = .ok q }

/-- The walk on a `P`-program, landing in what it produces. -/
def toFixedOn {P : NEList D → Prop} (h : w.LawfulOn P) (p : { p : NEList D // P p }) :
    Except Diag (w.FixedOn P) :=
  match hp : w.run p.val with
  | .error d => .error d
  | .ok q => .ok ⟨q, h.preserve p.val q p.property hp, h.idem p.val q p.property hp⟩

theorem toFixedOn_eq_ok {P : NEList D → Prop} (h : w.LawfulOn P) {p : { p : NEList D // P p }}
    {q : w.FixedOn P} : w.toFixedOn h p = .ok q ↔ w.run p.val = .ok q.val := by
  unfold toFixedOn
  split
  · rename_i hp
    constructor
    · intro e; cases e
    · intro e; rw [hp] at e; cases e
  · rename_i q' hp
    constructor
    · intro e; cases e; exact hp
    · intro e; rw [hp] at e; cases e; rfl

/-- **A walk as a later stage**: from the `P`-programs an earlier stage produces, to what this walk
makes of them. The same construction as `stage`. -/
def stageOn {P : NEList D → Prop} (h : w.LawfulOn P) :
    Abstraction { p : NEList D // P p } (w.FixedOn P)
      (fun q => { p : { p : NEList D // P p } // w.toFixedOn h p = .ok q }) :=
  { Abstraction.ofFibers (w.toFixedOn h)
      (fun q => ⟨⟨q.val, q.property.1⟩, (w.toFixedOn_eq_ok h).mpr q.property.2⟩) with
    -- A sub-program of a `P`-program need not satisfy `P`, so past a rejection there is no value
    -- to hand on: every rejection is reported, and the chain stops here.
    recover := fun p =>
      let r := w.runSkip w.init p.val.toList 0
      if r.1.isEmpty then
        match w.toFixedOn h p with
        | .ok q => ([], some (q, id))
        | .error d => ([d], none)
      else (r.1.map fun e => ({ msg := e.2, loc := .decl e.1 } : Diag), none) }

end Walk

end LambdaLab.Semantics
