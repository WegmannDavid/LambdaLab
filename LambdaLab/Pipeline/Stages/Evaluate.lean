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
another, each body closed, which is why the target predicate says *closed* and normal.

## The target is the image, as always

`Evaluated` is the *reduced* programs, not all well-typed ones. An arbitrary elaborated program is
not something reduction produces, and `abstract_realize` would then have nothing to say about it.
Being a fixed point is what makes the canonical annotation legal: an already-reduced program is its
own best re-presentation, so `default` is the program itself, justified by
`evalProgram_of_allReduced` exactly as ③'s `default` is justified by `elabProgram?_self`.

`AllReduced` demands *closed* and normal, and the first conjunct is load-bearing rather than
incidental: a body that were merely normal could still name an earlier declaration, inlining would
rewrite it, and the fixed point — hence `default` — would be false.

## The one stage that never rejects

`abstract` is `some` unconditionally. Evaluation is total on well-typed terms — that is
`StronglyNormalizing`, reached through `LawfulHasEval` — so this stage has no failure mode at all
and the `Option` in `Abstraction.abstract` is, here, pure overhead. That is worth saying out loud
because every earlier stage does reject: the tokenizer never does either, but the parser and the
elaborator both do, and a reader who has followed the pipeline this far will expect a third.

## And the stage whose forgetting is all in the fibers

Reduction discards what it reduces: `λ x . ( λ y . y ) x` and `λ x . x` have the same normal
form, and after inlining a program no longer records which of its declarations were written by
hand and which were spelled out by name. Yet `complete` holds, in one line — the annotation over
an evaluated `q` is a program that runs to it, so a program the stage accepted is verbatim an
annotation of its own result. The discard shows up not as a failed law but as the *size* of the
fibers: everything with the same normal form sits over it, told apart only by its annotation.
`realize default` still round-trips, so the canonical-print guarantee is untouched; the user's
working survives exactly as long as its annotation does, which is precisely what running a
program spends.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Abstraction

open TypeSystem.Named.Vernacular (HasType AllReduced evalProgram evalProgram_hasType
  evalProgram_allReduced evalProgram_of_allReduced)

variable (L : Language) [TypeSystem.Named.Runnable (Var L) L.Tm L.Ty]

/-- The **evaluated programs** of `L`: well-typed, every metavariable solved, and every body a
normal form. The image of `evalProgram`, and a fixed point of it. -/
def Language.Evaluated : Type := { q : Program L // HasType q ∧ AllReduced q }

/-- **Evaluation as an `Abs` morphism.** `abstract` normalizes every body; the annotation over an
evaluated `q` records an elaborated program that runs to it, and `default` records the canonical
such program — `q` itself, which runs to itself because it is already normal. -/
def Language.evalStage :
    Abstraction L.Elaborated L.Evaluated
      (fun q => { p : L.Elaborated // evalProgram p.val p.property = q.val }) where
  abstract p := some ⟨evalProgram p.val p.property,
    evalProgram_hasType p.val p.property, evalProgram_allReduced p.val p.property⟩
  realize ann := ann.val
  default {q} := ⟨⟨q.val, q.property.1⟩, evalProgram_of_allReduced q.val q.property.1 q.property.2⟩
  abstract_realize _ ann := congrArg some (Subtype.ext ann.property)
  complete p _q h := ⟨⟨p, congrArg Subtype.val (Option.some.inj h)⟩, rfl⟩

end LambdaLab.Pipeline
