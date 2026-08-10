import LambdaLab.TypeSystem.Vernacular.Typing

/-!
# The program elaborator, derived from the object language's

A calculus that implements `DecideableElaborate` decides *one* checking problem: under `Γ`, does
`t` elaborate against `τ`, and by which substitution. This file lifts that to a whole program, by
the obvious fold — elaborate the first declaration, insist nothing is left unsolved, push its name
at its now-ground type, elaborate the next against that context, and so on.

Nothing about the object language appears below. The fold is written once, against the interface,
and every language that decides its own elaboration gets a vernacular elaborator for free.

## What it produces

Not a `Bool` and not a bare program: `Option { p' // HasType p' }`. A success carries the
elaborated program *with* a derivation of `Vernacular.HasType`, so soundness is not a lemma to
prove afterwards — it is the return type. The elaborated program differs from the input exactly
where a metavariable was solved.

## Two laws the interface did not state

The fold needs more than `DecideableElaborate` provides, and it is worth being precise about why,
because the gap is not an accident of this file.

`elaborate Γ t τ` promises `HasType (pSubst Γ σ) (pSubst t σ) (pSubst τ σ)` — a typing under the
**substituted** context. The vernacular needs it under `Γ`, the context it actually maintains.
Those agree when `Γ` is ground, which it is here, but proving so needs:

* `GroundStable Ty Ty` — substitution fixes a ground type. Then a ground context is unchanged
  keywise (`Context.pSubst_get?_of_ground`).
* `LawfulContext N Tm Ty` — typing transports along keywise agreement. Needed because the
  *equation* `pSubst Γ σ = Γ` is unavailable: `Std.HashMap` has no `getElem?` extensionality, so
  keywise agreement is the strongest fact about contexts anyone here can have.

Both are mixins over instances already in scope, so neither reopens the `HasType` diamond, and
both hold for STLC (`HasType.cong` is literally the second).

Groundness must also be **decidable** to be checked. `HasVars.Ground` is `∀ n, ¬ isFree x n`,
which no instance can decide by unfolding, so the check is requested as a `DecidablePred`
instance; a language supplies it from its own structural check (STLC: `Ty.ground_iff` and
`Term.annotsGround_iff_ground` against `decide`).
-/

namespace LambdaLab.TypeSystem.Vernacular

open HasVars (Ground)

variable {N Tm Ty : Type} [NameAlphabet N]
  [DecideableElaborate N Tm Ty] [LawfulContext N Tm Ty] [GroundStable Ty Ty]
  [DecidablePred (Ground : Ty → Prop)] [DecidablePred (Ground : Tm → Prop)]

/-- The typing `elaborate` returns, re-read under the context the vernacular maintains rather than
under the substituted one. This is the single step the two extra laws exist for. -/
theorem hasType_of_solution {Γ : Context N Ty} {t : Tm} {τ : Ty} {σ : Subst Ty}
    (hΓ : CtxGround Γ)
    (hσ : _root_.LambdaLab.TypeSystem.HasType.HasType
            (HasSubst.pSubst Γ σ) (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ)) :
    _root_.LambdaLab.TypeSystem.HasType.HasType Γ (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ) :=
  LawfulContext.cong (Context.pSubst_get?_of_ground Γ σ hΓ) hσ

/-- **Elaborate a list of declarations against a ground context.**

Each step calls the object language's decision procedure, refuses the answer if it left a
metavariable in the declared type or the body, and continues under the context extended with the
solved type. The length is carried in the result so that a non-empty input provably yields a
non-empty output — `Program` is a `NEList`, and without it the head could not be recovered. -/
def elabCommands : (Γ : Context N Ty) → CtxGround Γ → (cs : List (Command N Tm Ty)) →
    Option { cs' : List (Command N Tm Ty) // HasTypeGround Γ cs' ∧ cs'.length = cs.length }
  | Γ, hΓ, [] => some ⟨[], .nil hΓ, rfl⟩
  | Γ, _hΓ, Command.decl x τ t :: cs =>
      match DecideableElaborate.elaborate Γ t τ with
      | .impossible _ => none
      | .solution σ hσ =>
          if hgτ : Ground (HasSubst.pSubst τ σ) then
            if hgt : Ground (HasSubst.pSubst t σ) then
              match elabCommands (Γ.cons x (HasSubst.pSubst τ σ)) (_hΓ.cons hgτ) cs with
              | none => none
              | some ⟨cs', hcs', hlen⟩ =>
                  some ⟨Command.decl x (HasSubst.pSubst τ σ) (HasSubst.pSubst t σ) :: cs',
                        .decl (hasType_of_solution _hΓ hσ) hgτ hgt hcs',
                        by simp [hlen]⟩
            else none
          else none

/-- **Elaborate a whole program.** The empty context is ground, so `nil`'s condition is discharged
by construction and never surfaces as an obligation on the caller. -/
def elabProgram (p : Program N Tm Ty) :
    Option { p' : Program N Tm Ty // HasType p' } :=
  match elabCommands (Context.empty : Context N Ty) CtxGround.empty p.toList with
  | none => none
  | some ⟨[], _, hlen⟩ => absurd hlen (by simp [NEList.toList])
  | some ⟨c :: cs, h, _⟩ => some ⟨(c, cs), h⟩

/-- The elaborated program with the certificate forgotten — what a caller that only wants the
output calls. -/
def elabProgram? (p : Program N Tm Ty) : Option (Program N Tm Ty) :=
  (elabProgram p).map Subtype.val

/-- **Soundness**, for the forgetful version: whatever comes out is a well-typed, fully resolved
program. Trivial here precisely because the certificate travels in the subtype rather than being
reconstructed afterwards. -/
theorem elabProgram?_hasType {p p' : Program N Tm Ty} (h : elabProgram? p = some p') :
    HasType p' := by
  rw [elabProgram?, Option.map_eq_some_iff] at h
  obtain ⟨q, _, rfl⟩ := h
  exact q.property

end LambdaLab.TypeSystem.Vernacular
