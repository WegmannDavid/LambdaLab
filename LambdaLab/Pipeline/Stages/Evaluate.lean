import LambdaLab.Pipeline.Stages.Elaborate
import LambdaLab.TypeSystem.Named.Vernacular.Evaluate

/-!
# ④ Evaluation, as a morphism of `Abs`

The stage after elaboration: every declaration reduced — earlier declarations inlined (δ), then
every redex contracted (β). It exists only for a language that supplies the machinery —
`[Runnable]`, which is `PrincipalElaborate`, `LawfulHasEval` and `HasTermSubst` sharing one
judgement — exactly as ③ exists only for one that supplies an elaborator. A language missing any of
them simply has no fourth stage, and that is a fact about the language, not a gap here.

## Why δ and not β alone

A declared name enters the context as a *free variable*, so `λ x . id ( id x )` is already
β-normal and β alone would leave nearly every program untouched. Inlining is what makes the stage
do anything. It also changes what the output is: the declarations come out independent of one
another, each body closed.

## A walk after a walk

The stage is `Semantics.Walk.stageOn` applied to the evaluator `Vernacular.evalWalk`. Its source is
the elaboration stage's target — the programs elaboration leaves unchanged — and its target is the
programs evaluation leaves unchanged *among those*. The law it needs (`evalWalk_lawfulOn`) is that
evaluating an elaborated program gives an elaborated program, and that evaluation is idempotent;
the canonical annotation of an evaluated program is then the program itself.

## Lossy in the sense that matters

Reduction discards what it reduces. `λ x . ( λ y . y ) x` and `λ x . x` have the same normal form,
and after inlining a program no longer records which of its declarations were written by hand and
which were spelled out by name. Only the annotation, which holds the un-reduced program, tells them
apart. `realize default` still round-trips, so the canonical-print guarantee is untouched; what is
gone is the user's working, which is precisely what running a program is for.

The completeness law holds all the same, because it is a claim about the annotation and not about
the algorithm: the annotation over `q` is every elaborated program that runs to `q`, so the program
you started from is its own witness.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Semantics (Walk)

variable (D : DefLanguage) [TypeSystem.Named.Runnable (Var D) D.Tm D.Ty]

/-- The evaluator over `D`'s declarations. -/
abbrev DefLanguage.evalWalk : Walk (Command D) := TypeSystem.Named.Vernacular.evalWalk

/-- The **evaluated programs** of `D`: elaborated, and left unchanged by evaluation — every body
closed and normal. -/
abbrev DefLanguage.Evaluated : Type :=
  D.evalWalk.FixedOn (fun p => D.elabWalk.run p = .ok p)

/-- **Evaluation as an `Abs` morphism**, from the elaborated programs. `abstract` reduces every
body; the annotation over an evaluated program records an elaborated program that runs to it, and
`default` records the canonical such program — the evaluated program itself. -/
def DefLanguage.evalStage :=
  D.evalWalk.stageOn TypeSystem.Named.Vernacular.evalWalk_lawfulOn

end LambdaLab.Pipeline
