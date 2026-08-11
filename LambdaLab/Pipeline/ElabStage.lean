import LambdaLab.Pipeline.Pipeline
import LambdaLab.TypeSystem.Vernacular.Elaborate

/-!
# Elaboration as a pipeline stage — the front end, type checking included

`Abstraction` stages compose into the front end: `List Char ⇝ List Token ⇝ Program`. This file
builds the *next* stage, `Program ⇝ well-typed Program`, and composes it on.

## Where the semantics comes from

Nowhere in this file. A `Language` says how to read and print; it says nothing about what a
program *means*, and it never will — meaning is the type system's business. So the stage below is
parameterised by `[Vernacular.Elaboratable (Var L) L.Tm L.Ty]`: **the moment a language's own
types and terms satisfy the elaboration interface, the whole front end exists**, parse and check
as one `Abs` morphism, with nothing further to supply.

That is the entire wiring. `Var L` is the language's variable alphabet, which is also its
declaration-name alphabet, so the instance the front end needs is exactly the instance the object
language would want anyway — `Stlc/Named/TypeSystem.lean` proves it once, generically in the name
type, and this file consumes it at `Var stlcLanguage` without STLC knowing a parser exists.

## What the stage abstracts onto

Concrete is the program as written; abstract is `{ p // HasType p }` — the programs
that are well-typed *and* carry no unsolved metavariable, which is what that judgement means. The
annotation over such a `p` is the fiber: the source programs that elaborate to it.

## Why `default` is available, and what it costs

`Abstraction.default` demands a canonical member of every fiber — a printer must have something to
print. Here it is `p` itself, and `elabProgram?_self` is exactly the proof that `p` lies
in its own fiber: an elaborated program is ground, substitution does not touch a ground object, so
running the elaborator on it succeeds and returns it unchanged.

Note what is *not* claimed. `Lossless` is not proved and does not hold: the fiber over `p` is every
way of leaving annotations to be inferred, jointly constrained by unification, and the annotation
family here does not enumerate it — `Abstraction/Basic.lean` says why no node-local family could.
What survives is the canonical-print round trip, which is the compiler-grade guarantee: render an
elaborated program and re-read it, and you are back where you started.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Abstraction

/-! Selectively, not wholesale: `Vernacular` also exports `Command` and `Program`, which this
namespace has its own instantiated abbreviations for. -/
open LambdaLab.TypeSystem.Vernacular
  (Elaboratable HasType elabProgram elabProgram? elabProgram?_self)

variable (L : Language) [Elaboratable (Var L) L.Tm L.Ty]

/-- The **elaborated programs** of `L`: well-typed, and with every metavariable solved.

This, not `Program L`, is what elaboration abstracts onto. An arbitrary program need not be
anything the elaborator produces, and `default` would then have no surface form to offer for
it. -/
def Language.Elaborated : Type := { p : Program L // HasType p }

/-- **Elaboration as an `Abs` morphism.** `abstract` runs the whole-program elaborator and applies
the substitution it found; the annotation over an elaborated `p` records a source program that
means it, and `default` records the canonical such source — `p` itself. -/
def Language.elabStage :
    Abstraction (Program L) L.Elaborated
      (fun p => { q : Program L // elabProgram? q = some p.val }) where
  abstract q := (elabProgram q).map fun s => ⟨HasSubst.pSubst q s.val, s.property⟩
  realize ann := ann.val
  default {p} := ⟨p.val, elabProgram?_self p.property⟩
  abstract_realize p ann := by
    have hann : elabProgram? ann.val = some p.val := ann.property
    rw [elabProgram?] at hann
    show ((elabProgram ann.val).map _) = some p
    cases hq : elabProgram ann.val with
    | none => rw [hq] at hann; exact absurd hann (by simp)
    | some s =>
        rw [hq] at hann
        rw [Option.map_some, Option.some.injEq]
        exact Subtype.ext (Option.some.inj hann)

/-- **The whole front end**: characters to an elaborated program, in `Abs`. Parsing and
elaboration are one morphism, so the round-trip law covers both — `realize` of any annotation
re-parses *and* re-elaborates to exactly the value it indexes. -/
def Language.elabPipeline :
    Abstraction (List Char) L.Elaborated
      (fun p => Σ ann : { q : Program L // elabProgram? q = some p.val },
        Σ a : Program.Ann L ann.val, Gaps isSep (L.parser.print a)) :=
  L.pipeline.comp L.elabStage

/-- Parse *and* elaborate a source file. -/
def Language.elaborateFile (s : String) : Option L.Elaborated :=
  L.elabPipeline.abstract s.toList

/-- Render an elaborated program canonically: every declaration in its canonical spelling, with
the types elaboration solved written out. -/
def Language.renderElaborated (p : L.Elaborated) : String :=
  String.ofList (L.elabPipeline.realize (L.elabPipeline.default (a := p)))

/-- **The front end round-trips.** Render an elaborated program and read it back, and elaboration
returns it — the canonical-print guarantee, covering tokenizing, parsing and type checking at
once. -/
theorem Language.elaborateFile_renderElaborated (p : L.Elaborated) :
    L.elaborateFile (L.renderElaborated p) = some p := by
  show L.elabPipeline.abstract (String.ofList
    (L.elabPipeline.realize (L.elabPipeline.default (a := p)))).toList = some p
  rw [String.toList_ofList]
  exact L.elabPipeline.abstract_realize p L.elabPipeline.default

end LambdaLab.Pipeline
