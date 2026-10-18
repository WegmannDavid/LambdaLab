import LambdaLab.Abstraction.Basic

/-!
# `Chain` — a pipeline as the list of its stages

`Abstraction.comp` answers "what does the whole front end do", and in doing so throws away
"what were the stages". That is not a defect of the definition — composition in *any* category
forgets its factorization, and the forgetting is exactly what makes a composite a single object
with a single round-trip law. But a compiler needs the factorization back:

* to **show its work** (`--stages`: the token stream, then the parsed program, then the
  elaborated one), rather than only the last thing it produced;
* to **say what failed**: which stage rejected the input, with that stage's diagnostic, pointed
  back at the input of the whole pipeline.

So a pipeline is stored as the chain and *collapsed on demand*, rather than stored collapsed.
`Chain X Y` is a list of composable 1-cells with composability enforced by the indexing — the
free-category shape, `Quiver.Path` — and `compose` is the collapse.

## Why this is not `Quiver.Path`

Mathlib has exactly this type, `Quiver.Path`, with `CategoryTheory.composePath` as the collapse.
Two reasons it is re-declared here in four lines:

* `Pipeline/` is in the executables' import cone, and that cone is Mathlib-free — `Mathlib`
  appears nowhere in `stlc`'s or `float`'s link trace. One Mathlib import anywhere below them
  pulls in about 1300 modules; when that was last measured it was the difference between a
  2.8 MB `stlc` and a 129 MB one. Same trade as `Iso` versus `Equiv` in `Basic.lean`.
* `composePath` requires `[Category C]` and would not apply anyway. `Abs` is a *bi*category:
  `(f ≫ g) ≫ h` and `f ≫ (g ≫ h)` nest their `Σ`s differently, so they are isomorphic (the
  `associator` in `Bicat.lean`) and not equal. `compose` below therefore fixes an association
  order — left-nested, matching `cons` — and states no associativity law. Any such law is a
  2-cell, and 2-cells live in `Bicat.lean`, above Mathlib.

## Non-empty

There is no `nil`. An empty chain would compose to `OneCell.id`, and then a two-stage chain would
collapse to `𝟙 ≫ f ≫ g` rather than `f ≫ g` — equal only up to the left unitor, again a 2-cell.
With `one` as the base case, `compose` of a chain is *definitionally* the composite that
`Pipeline/Compose.lean` already builds by hand, so the two are linked by `rfl` rather than by a
transport. A pipeline with no stages is not a thing anyone wanted.

## What a `Stage` carries

Vertices are not bare types: displaying an intermediate needs a way to show it. `render` is
supplied per stage rather than derived from the prefix's canonical printer, and deliberately —
the canonical rendering of a program is one command per line, which is a `withDefault` on a
*composite* (see `Compose.lean`), not something either stage can state alone. The display of an
intermediate is a presentation choice of exactly that kind, so it is made where the structure is
known, and the pipeline hands the already-defined renderer over.
-/

set_option autoImplicit false

namespace LambdaLab.Abstraction

/-- A vertex of a pipeline: the type flowing out of one stage and into the next, what to call it
in a diagnostic, and how to show one of its values. -/
structure Stage where
  /-- The type of values at this point in the pipeline. -/
  Carrier : Type
  /-- The name this stage is reported under. -/
  name : String
  /-- How to display a value that reached this stage. -/
  render : Carrier → String

/-- One line of a step-by-step run: what the input looked like on arrival at `stage`. -/
structure Step where
  /-- The stage this value arrived at. -/
  stage : String
  /-- Its rendering, via that stage's `render`. -/
  text : String

/-- A rejection: the stage that was not reached, and the diagnostic of the stage that refused to
produce it — its location pulled back into the pipeline's input. -/
structure Failure where
  /-- The stage that was not reached. -/
  stage : String
  /-- What went wrong, and where in the pipeline's input. -/
  diag : Diag

/-- A pipeline from `X` to `Y`: a non-empty list of 1-cells whose endpoints line up, with the
lining-up enforced by the type. Left-nested, so `cons` appends a stage on the end. -/
inductive Chain : Stage → Stage → Type 1
  | /-- A one-stage pipeline. -/
    one {X Y : Stage} : OneCell X.Carrier Y.Carrier → Chain X Y
  | /-- One more stage on the end. -/
    cons {X Y Z : Stage} : Chain X Y → OneCell Y.Carrier Z.Carrier → Chain X Z

namespace Chain

variable {X Y Z : Stage}

/-- **The collapse**: the single morphism the stages compose to. This is what the rest of the
development talks about — the round-trip law of a pipeline is a law of `compose`, proved once for
the composite rather than stage by stage. -/
def compose : {X Y : Stage} → Chain X Y → OneCell X.Carrier Y.Carrier
  | _, _, .one e => e
  | _, _, .cons p e => p.compose.hcomp e

@[simp] theorem compose_one (e : OneCell X.Carrier Y.Carrier) :
    (Chain.one e).compose = e := by simp [compose]

@[simp] theorem compose_cons (p : Chain X Y) (e : OneCell Y.Carrier Z.Carrier) :
    (p.cons e).compose = p.compose.hcomp e := by simp [compose]

/-- Append a whole pipeline to another. No law relates `(p.comp q).compose` to
`p.compose.hcomp q.compose`: they are the same `Σ`s nested differently, i.e. related by the
associator, which is a 2-cell and lives above Mathlib. -/
def comp : {X Y Z : Stage} → Chain X Y → Chain Y Z → Chain X Z
  | _, _, _, p, .one e => .cons p e
  | _, _, _, p, .cons q e => .cons (p.comp q) e

/-- **Run the pipeline one stage at a time**, recording what arrived at each.

The first `Step` is the input itself, so a successful run of an `n`-stage chain reports `n + 1`
entries — a compiler that shows its work should show what it was given. A success also returns how
to pull a location in the output back into the input, the stages' `locate`s composed. On rejection
the steps gathered so far are still returned, and the failure names the stage that was not
reached, with the rejecting stage's diagnostic pulled back the same way. -/
def run : {X Y : Stage} → Chain X Y → X.Carrier →
    List Step × Except Failure (Y.Carrier × (Loc → Loc))
  | X, Y, .one e, x =>
      match e.hom.abstract x with
      | .error d => ([⟨X.name, X.render x⟩], .error ⟨Y.name, d⟩)
      | .ok y => ([⟨X.name, X.render x⟩, ⟨Y.name, Y.render y⟩], .ok (y, e.hom.locate x))
  | _, Z, .cons p e, x =>
      match p.run x with
      | (steps, .error f) => (steps, .error f)
      | (steps, .ok (y, back)) =>
          match e.hom.abstract y with
          | .error d => (steps, .error ⟨Z.name, { d with loc := back d.loc }⟩)
          | .ok z => (steps ++ [⟨Z.name, Z.render z⟩], .ok (z, back ∘ e.hom.locate y))

/-- **What a driver prints.** On success, with `showStages := false` the finished value rendered —
the very string the collapsed pipeline would have produced, by `run_eq_abstract`; with `true`, every
stage the input passed through, each under its own name. On rejection, the failure, and the stages
reached before it. -/
def report (c : Chain X Y) (showStages : Bool) (x : X.Carrier) :
    Except (List Step × Failure) String :=
  match c.run x with
  | (steps, .error f) => .error (steps, f)
  | (steps, .ok (y, _)) =>
      if showStages then
        .ok (String.intercalate "\n" (steps.map fun s => s!"== {s.stage} ==\n{s.text}"))
      else
        .ok (Y.render y)

/-- **Stepping agrees with collapsing**, on what is produced. Walking the stages and asking the
composite accept the same inputs and produce the same values; the chain is a finer
*presentation* of the pipeline, never a different pipeline. (What they *say* on rejection is not
compared: diagnostics are informal.) -/
theorem run_eq_abstract (c : Chain X Y) (x : X.Carrier) :
    ((c.run x).2.map Prod.fst).toOption = (c.compose.hom.abstract x).toOption := by
  induction c with
  | one e =>
      rw [compose_one]
      cases h : e.hom.abstract x <;> simp [run, h, Except.toOption, Except.map]
  | cons p e ih =>
      rw [compose_cons, OneCell.hcomp_abstract]
      simp only [run]
      unfold Abstraction.compAbstract
      cases hr : p.run x with
      | mk steps r =>
          rw [hr] at ih
          cases r with
          | error f =>
              cases hc : p.compose.hom.abstract x with
              | error => rfl
              | ok y => rw [hc] at ih; simp [Except.map, Except.toOption] at ih
          | ok yb =>
              obtain ⟨y, back⟩ := yb
              cases hc : p.compose.hom.abstract x with
              | error => rw [hc] at ih; simp [Except.map, Except.toOption] at ih
              | ok y' =>
                  rw [hc] at ih
                  simp only [Except.map, Except.toOption, Option.some.injEq] at ih
                  subst ih
                  cases h : e.hom.abstract y <;> simp [h, Except.toOption, Except.map]

/-! ## Losslessness

There is nothing left to say here. Completeness is a law of `Abstraction` now, so every cell of
every chain has it and `compose` inherits it like any other field — where this file used to carry
an inductive `Chain.Lossless` and a fold transferring it to the composite.

What that costs is the *prefix* statement the old predicate could express: "reconstruction extends
this far and no further" is not sayable when every stage reconstructs. The trade is deliberate —
a stage that cannot cover its fibers structurally takes the tautological family instead
(`Abstraction.ofFibers`) and covers them anyway. -/

end Chain

end LambdaLab.Abstraction
