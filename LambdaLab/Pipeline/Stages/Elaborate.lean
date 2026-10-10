import LambdaLab.Pipeline.Def
import LambdaLab.TypeSystem.Named.Vernacular.Elaborate

/-!
# The elaboration stage: `Program ⇝ elaborated Program`

One stage, and nothing else — `Compose.lean` is where it is chained onto the ones before it.

Note what this file does **not** import: neither the tokenizer nor `Stages/Parse.lean`. Nothing
here knows how a program was read. A `DefLanguage` is only the source of `Command D`, `Var D`,
`D.Tm` and `D.Ty` — `Pipeline/Def.lean` does drag in the parser *types*, since a `DefLanguage` has
`pTy` and `pTm` fields, but no parsing happens at or below this file.

## Where the semantics comes from

Nowhere in this file. The stage is `Semantics.Walk.stage` applied to the program elaborator
`Vernacular.elabWalk`, which is parameterised by
`[TypeSystem.Named.PrincipalElaborate (Var D) D.Tm D.Ty]`: **the moment a language's own types and
terms satisfy the elaboration interface, the stage exists**, with nothing further to supply.

`Var D` is the language's variable alphabet, which is also its declaration-name alphabet, so the
instance the front end needs is exactly the instance the object language would want anyway —
`Stlc/Named/TypeSystem.lean` proves it once, generically in the name type, and this file consumes it
at `Var stlcLanguage` without STLC knowing a parser exists.

## What the stage abstracts onto

Concrete is the program as written; abstract is what the elaborator leaves unchanged
(`Walk.Fixed`) — exactly the well-typed programs, every metavariable solved
(`Vernacular.elabWalk_fixed_iff`). The annotation over such a program is the fiber: the source
programs that elaborate to it, its canonical member being the program itself. That the canonical
member lies in the fiber is the walk's idempotence, which is soundness together with
`elabWalk_self`: an elaborated program is ground, substitution does not touch a ground object, so
re-elaborating it changes nothing.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Semantics (Walk)

variable (D : DefLanguage) [TypeSystem.Named.PrincipalElaborate (Var D) D.Tm D.Ty]

/-- The program elaborator over `D`'s declarations. -/
abbrev DefLanguage.elabWalk : Walk (Command D) := TypeSystem.Named.Vernacular.elabWalk

/-- The **elaborated programs** of `D`: what elaboration leaves unchanged — the well-typed programs
with every metavariable solved. -/
abbrev DefLanguage.Elaborated : Type := D.elabWalk.Fixed

/-- **Elaboration as an `Abs` morphism.** `abstract` runs the elaborator; the annotation over an
elaborated program records a source program that elaborates to it, and `default` records the
canonical such source — the program itself. -/
def DefLanguage.elabStage :=
  D.elabWalk.stage TypeSystem.Named.Vernacular.elabWalk_idempotent

end LambdaLab.Pipeline
