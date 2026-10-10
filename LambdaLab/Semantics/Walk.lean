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
reject it, or rewrite it and hand on the next state. -/
structure Walk (D : Type) where
  /-- What is carried from one declaration to the next. -/
  State : Type
  /-- The state before the first declaration. -/
  init : State
  /-- Process one declaration. -/
  step : State → D → Option (D × State)

namespace Walk

variable {D : Type} (w : Walk D)

/-- Run the walk over a list of declarations from a given state. -/
def runFrom : w.State → List D → Option (List D)
  | _, [] => some []
  | s, d :: ds =>
      match w.step s d with
      | none => none
      | some (d', s') => (runFrom s' ds).map (d' :: ·)

/-- **Run the walk over a program**, from `init`. -/
def run (p : NEList D) : Option (NEList D) :=
  match w.step w.init p.1 with
  | none => none
  | some (d', s') => (w.runFrom s' p.2).map (d', ·)

/-- Running a program is running its declarations as a list. -/
theorem run_toList (p : NEList D) :
    (w.run p).map NEList.toList = w.runFrom w.init p.toList := by
  obtain ⟨d, ds⟩ := p
  simp only [run, NEList.toList, runFrom]
  cases w.step w.init d with
  | none => rfl
  | some r =>
      obtain ⟨d', s'⟩ := r
      simp only
      cases w.runFrom s' ds <;> rfl

theorem run_eq_some {p q : NEList D} :
    w.run p = some q ↔ w.runFrom w.init p.toList = some q.toList := by
  rw [← run_toList]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    cases hr : w.run p with
    | none => rw [hr] at h; exact absurd h (by simp)
    | some q' =>
        rw [hr, Option.map_some, Option.some.injEq] at h
        obtain ⟨a, as⟩ := q'
        obtain ⟨b, bs⟩ := q
        simp only [NEList.toList, List.cons.injEq] at h
        rw [h.1, h.2]

/-! ## Idempotence -/

/-- **The law**: running the walk on its own output changes nothing. -/
def Idempotent : Prop := ∀ p q, w.run p = some q → w.run q = some q

/-- **Idempotence a step at a time**: handed its own output in the state it was in, a step gives
that output back and moves to the same state. -/
def StepIdempotent : Prop :=
  ∀ s d d' s', w.step s d = some (d', s') → w.step s d' = some (d', s')

theorem runFrom_idempotent (h : w.StepIdempotent) :
    ∀ (s : w.State) (ds ds' : List D), w.runFrom s ds = some ds' → w.runFrom s ds' = some ds'
  | s, [], ds', hr => by
      simp only [runFrom, Option.some.injEq] at hr
      subst hr; rfl
  | s, d :: ds, ds', hr => by
      simp only [runFrom] at hr
      cases hs : w.step s d with
      | none => rw [hs] at hr; exact absurd hr (by simp)
      | some r =>
          obtain ⟨d', s'⟩ := r
          rw [hs] at hr
          cases hrest : w.runFrom s' ds with
          | none => simp [hrest] at hr
          | some rest =>
              simp only [hrest, Option.map_some, Option.some.injEq] at hr
              subst hr
              simp only [runFrom, h s d d' s' hs, runFrom_idempotent h s' ds rest hrest]
              rfl

/-- Step-wise idempotence is enough for the law. -/
theorem idempotent_of_step (h : w.StepIdempotent) : w.Idempotent := by
  intro p q hpq
  rw [run_eq_some] at hpq ⊢
  exact w.runFrom_idempotent h _ _ _ hpq

/-- **The law, for a walk run after another stage**: on programs satisfying `P` (what the earlier
stage guarantees) the walk keeps `P` and is idempotent. -/
structure LawfulOn (P : NEList D → Prop) : Prop where
  /-- What the walk produces from a `P`-program is a `P`-program. -/
  preserve : ∀ p q, P p → w.run p = some q → P q
  /-- …and running the walk on it changes nothing. -/
  idem : ∀ p q, P p → w.run p = some q → w.run q = some q

/-! ## The stage -/

/-- **What the walk produces**: the programs it leaves unchanged. For an idempotent walk this is
exactly its image. -/
def Fixed : Type := { q : NEList D // w.run q = some q }

/-- The walk, landing in what it produces. -/
def toFixed (h : w.Idempotent) (p : NEList D) : Option w.Fixed :=
  match hp : w.run p with
  | none => none
  | some q => some ⟨q, h p q hp⟩

theorem toFixed_eq_some (h : w.Idempotent) {p : NEList D} {q : w.Fixed} :
    w.toFixed h p = some q ↔ w.run p = some q.val := by
  unfold toFixed
  split
  · rename_i hp
    constructor
    · intro e; exact absurd e (by simp)
    · intro e; rw [hp] at e; exact absurd e (by simp)
  · rename_i q' hp
    rw [Option.some.injEq]
    constructor
    · intro e; subst e; exact hp
    · intro e; rw [hp] at e; exact Subtype.ext (Option.some.inj e)

/-- **A walk as a stage**: programs to the programs the walk leaves unchanged. Each output is its
own canonical source — the walk changes nothing about it — and the annotation over an output is
every program the walk takes there, so the stage is complete by construction
(`Abstraction.ofFibers`). -/
def stage (h : w.Idempotent) :
    Abstraction (NEList D) w.Fixed (fun q => { p : NEList D // w.toFixed h p = some q }) :=
  Abstraction.ofFibers (w.toFixed h) (fun q => ⟨q.val, (w.toFixed_eq_some h).mpr q.property⟩)

/-- What the walk produces from `P`-programs: those it leaves unchanged that still satisfy `P`. -/
def FixedOn (P : NEList D → Prop) : Type := { q : NEList D // P q ∧ w.run q = some q }

/-- The walk on a `P`-program, landing in what it produces. -/
def toFixedOn {P : NEList D → Prop} (h : w.LawfulOn P) (p : { p : NEList D // P p }) :
    Option (w.FixedOn P) :=
  match hp : w.run p.val with
  | none => none
  | some q => some ⟨q, h.preserve p.val q p.property hp, h.idem p.val q p.property hp⟩

theorem toFixedOn_eq_some {P : NEList D → Prop} (h : w.LawfulOn P) {p : { p : NEList D // P p }}
    {q : w.FixedOn P} : w.toFixedOn h p = some q ↔ w.run p.val = some q.val := by
  unfold toFixedOn
  split
  · rename_i hp
    constructor
    · intro e; exact absurd e (by simp)
    · intro e; rw [hp] at e; exact absurd e (by simp)
  · rename_i q' hp
    rw [Option.some.injEq]
    constructor
    · intro e; subst e; exact hp
    · intro e; rw [hp] at e; exact Subtype.ext (Option.some.inj e)

/-- **A walk as a later stage**: from the `P`-programs an earlier stage produces, to what this walk
makes of them. The same construction as `stage`. -/
def stageOn {P : NEList D → Prop} (h : w.LawfulOn P) :
    Abstraction { p : NEList D // P p } (w.FixedOn P)
      (fun q => { p : { p : NEList D // P p } // w.toFixedOn h p = some q }) :=
  Abstraction.ofFibers (w.toFixedOn h)
    (fun q => ⟨⟨q.val, q.property.1⟩, (w.toFixedOn_eq_some h).mpr q.property.2⟩)

end Walk

end LambdaLab.Semantics
