import LambdaLab.Pipeline.Stages.Elaborate
import LambdaLab.TypeSystem.Named.Vernacular.Evaluate

/-!
# ④ Evaluation, as a morphism of `Abs`

The stage after elaboration: every declaration body replaced by its normal form. It exists only
for a language that supplies an evaluator — `[Runnable]`, which is `PrincipalElaborate` and
`LawfulHasEval` sharing one judgement — exactly as ③ exists only for one that supplies an
elaborator. A language with no `HasEval` instance simply has no fourth stage, and that is a fact
about the language, not a gap here.

## The target is the image, as always

`Evaluated` is the *normalized* programs, not all well-typed ones. An arbitrary elaborated program
is not something evaluation produces, and `abstract_realize` would then have nothing to say about
it. Being a fixed point is what makes the canonical annotation legal: an already-normal program is
its own best re-presentation, so `default` is the program itself, justified by
`evalProgram_of_allNormal` exactly as ③'s `default` is justified by `elabProgram?_self`.

## The one stage that never rejects

`abstract` is `some` unconditionally. Evaluation is total on well-typed terms — that is
`StronglyNormalizing`, reached through `LawfulHasEval` — so this stage has no failure mode at all
and the `Option` in `Abstraction.abstract` is, here, pure overhead. That is worth saying out loud
because every earlier stage does reject: the tokenizer never does either, but the parser and the
elaborator both do, and a reader who has followed the pipeline this far will expect a third.

## And the one stage that is honestly lossy

`Lossless` fails, and not for elaboration's subtle reason (fibres constrained by unification) but
for the obvious one: β-reduction discards the redex. `λ x . ( λ y . y ) x` and `λ x . x` have the
same normal form and only the annotation — which records the un-reduced program — tells them
apart. `realize default` still round-trips, so the canonical-print guarantee is untouched; what is
gone is the user's arithmetic, which is precisely what running a program is for.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Abstraction

open TypeSystem.Named.Vernacular (HasType AllNormal evalProgram evalProgram_hasType
  evalProgram_allNormal evalProgram_of_allNormal)

variable (L : Language) [TypeSystem.Named.Runnable (Var L) L.Tm L.Ty]

/-- The **evaluated programs** of `L`: well-typed, every metavariable solved, and every body a
normal form. The image of `evalProgram`, and a fixed point of it. -/
def Language.Evaluated : Type := { q : Program L // HasType q ∧ AllNormal q }

/-- **Evaluation as an `Abs` morphism.** `abstract` normalizes every body; the annotation over an
evaluated `q` records an elaborated program that runs to it, and `default` records the canonical
such program — `q` itself, which runs to itself because it is already normal. -/
def Language.evalStage :
    Abstraction L.Elaborated L.Evaluated
      (fun q => { p : L.Elaborated // evalProgram p.val p.property = q.val }) where
  abstract p := some ⟨evalProgram p.val p.property,
    evalProgram_hasType p.val p.property, evalProgram_allNormal p.val p.property⟩
  realize ann := ann.val
  default {q} := ⟨⟨q.val, q.property.1⟩, evalProgram_of_allNormal q.val q.property.1 q.property.2⟩
  abstract_realize _ ann := congrArg some (Subtype.ext ann.property)

end LambdaLab.Pipeline
