import LambdaLab.Pipeline.Basic
import LambdaLab.TypeSystem.Named.Vernacular.Elaborate

/-!
# The elaboration stage: `Program ⇝ well-typed Program`

One stage, and nothing else — `Compose.lean` is where it is chained onto the ones before it.

Note what this file does **not** import: neither the tokenizer nor `Stages/Parse.lean`. Nothing
here knows how a program was read. A `Language` is only the source of `Program L`, `Var L`, `L.Tm`
and `L.Ty` — `Pipeline/Basic.lean` does drag in the parser *types*, since a `Language` has `pTy`
and `pTm` fields, but no parsing happens at or below this file. Keeping the composition out of it
is what makes that visible in the import list rather than merely asserted below.

## Where the semantics comes from

Nowhere in this file. A `Language` says how to read and print; it says nothing about what a
program *means*, and it never will — meaning is the type system's business. So the stage below is
parameterised by `[TypeSystem.Named.PrincipalElaborate (Var L) L.Tm L.Ty]`: **the moment a language's own
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

And `complete` costs nothing more: the annotation family *is* the fiber of `elabProgram?`, so a
source the stage accepts is its own annotation — `abstract` succeeding is fiber membership, and
the proof is a line. The fiber is rich (every way of leaving annotations to be inferred, jointly
constrained by unification), and no family assembled from node-local choices would enumerate it —
`Abstraction/Basic.lean` tells that story; indexing by the fiber itself is what sidesteps the
enumeration. The canonical-print round trip stays the compiler-grade guarantee: render an
elaborated program and re-read it, and you are back where you started.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Abstraction

/-! Selectively, not wholesale: `Vernacular` also exports `Command` and `Program`, which this
namespace has its own instantiated abbreviations for. -/
open LambdaLab.TypeSystem.Named.Vernacular
  (HasType elabProgram elabProgram? elabProgram?_self)

variable (L : Language) [TypeSystem.Named.PrincipalElaborate (Var L) L.Tm L.Ty]

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
  abstract q := (elabProgram q).map fun s => ⟨HasSubst.pSubst q s.val, s.property.1⟩
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
  complete q p h := by
    rw [Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨⟨q, by rw [elabProgram?, hs]; rfl⟩, rfl⟩

end LambdaLab.Pipeline
