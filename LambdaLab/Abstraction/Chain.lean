import LambdaLab.Abstraction.Basic

/-!
# `Chain` — a pipeline as the list of its stages

`Abstraction.comp` answers "what does the whole front end do", and in doing so throws away
"what were the stages". That is not a defect of the definition — composition in *any* category
forgets its factorization, and the forgetting is exactly what makes a composite a single object
with a single round-trip law. But a compiler needs the factorization back:

* to **show its work** (`--stages`: the token stream, then the parsed program, then the
  elaborated one), rather than only the last thing it produced;
* to **say what failed**. A composite's `abstract` returns `none`; the `Option.bind` in
  `Abstraction.comp` has erased which stage produced it.

So a pipeline is stored as the chain and *collapsed on demand*, rather than stored collapsed.
`Chain X Y` is a list of composable 1-cells with composability enforced by the indexing — the
free-category shape, `Quiver.Path` — and `compose` is the collapse.

## Why this is not `Quiver.Path`

Mathlib has exactly this type, `Quiver.Path`, with `CategoryTheory.composePath` as the collapse.
Two reasons it is re-declared here in four lines:

* `Pipeline/` is in the executables' import cone, and that cone is Mathlib-free — `Mathlib`
  appears nowhere in `stlc`'s or `arith`'s link trace. One Mathlib import anywhere below them
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
entries — a compiler that shows its work should show what it was given. On rejection the steps
gathered so far are still returned, and the error names the stage that was not reached: this is
the information `compose`'s `Option.bind` erases. -/
def run : {X Y : Stage} → Chain X Y → X.Carrier → List Step × Except String Y.Carrier
  | X, Y, .one e, x =>
      match e.hom.abstract x with
      | none => ([⟨X.name, X.render x⟩], .error Y.name)
      | some y => ([⟨X.name, X.render x⟩, ⟨Y.name, Y.render y⟩], .ok y)
  | _, Z, .cons p e, x =>
      match p.run x with
      | (steps, .error stage) => (steps, .error stage)
      | (steps, .ok y) =>
          match e.hom.abstract y with
          | none => (steps, .error Z.name)
          | some z => (steps ++ [⟨Z.name, Z.render z⟩], .ok z)

/-- **What a driver prints.** With `showStages := false` this is the finished value rendered —
the very string the collapsed pipeline would have produced, by `run_eq_abstract`. With `true` it
is every stage the input passed through, each under its own name. A rejection names the stage that
was not reached, which is exactly the information `compose`'s `Option.bind` erases. -/
def report (c : Chain X Y) (showStages : Bool) (x : X.Carrier) : Except String String :=
  match c.run x with
  | (_, Except.error stage) => Except.error s!"error: rejected while producing the {stage}"
  | (steps, Except.ok y) =>
      if showStages then
        Except.ok (String.intercalate "\n" (steps.map fun s => s!"== {s.stage} ==\n{s.text}"))
      else
        Except.ok (Y.render y)

/-- **Stepping agrees with collapsing.** Walking the stages and asking the composite are the same
question; the chain is a finer *presentation* of the pipeline, never a different pipeline. This is
what lets `Compose.lean` keep proving its round-trip law about the composite while the driver runs
the chain. -/
theorem run_eq_abstract (c : Chain X Y) (x : X.Carrier) :
    (c.run x).2.toOption = c.compose.hom.abstract x := by
  induction c with
  | one e =>
      rw [compose_one]
      cases h : e.hom.abstract x <;> simp [run, h, Except.toOption]
  | cons p e ih =>
      rw [compose_cons, OneCell.hcomp_abstract, ← ih]
      simp only [run]
      cases hr : p.run x with
      | mk steps r =>
          cases r with
          | error => rfl
          | ok y => cases h : e.hom.abstract y <;> simp [h, Except.toOption]

/-! ## Losslessness, stage by stage

`Lossless` is a property of a single morphism, and `Abstraction.Lossless.comp` closes it under
composition — so on a collapsed pipeline the only sayable thing is "lossless" or "not". On a chain
the useful statement is available: which *prefix* is lossless, i.e. how far back towards the
source a value can be turned into the text the user actually wrote. -/

/-- Every stage forgets nothing. -/
inductive Lossless : {X Y : Stage} → Chain X Y → Prop
  | /-- The base stage is lossless. -/
    one {X Y : Stage} {e : OneCell X.Carrier Y.Carrier} :
      e.hom.Lossless → Lossless (.one e)
  | /-- One more lossless stage on the end. -/
    cons {X Y Z : Stage} {p : Chain X Y} {e : OneCell Y.Carrier Z.Carrier} :
      Lossless p → e.hom.Lossless → Lossless (.cons p e)

/-- A stagewise-lossless chain collapses to a lossless morphism — `Abstraction.Lossless.comp`,
folded along the chain. The converse fails, and interestingly: a later stage may forget freely
off the image of the earlier ones without the composite noticing. -/
theorem Lossless.composite {c : Chain X Y} (h : c.Lossless) : c.compose.hom.Lossless := by
  induction h with
  | one he => rw [compose_one]; exact he
  | cons _ he ih => rw [compose_cons]; exact Abstraction.Lossless.comp ih he

end Chain

end LambdaLab.Abstraction
