import LambdaLab.TypeSystem.Vernacular.Typing

/-!
# The program elaborator, derived from the object language's

A calculus that implements `DecideableElaborate` decides *one* checking problem: under `Γ`, does
`t` elaborate against `τ`, and by which substitution. This file lifts that to a whole program, by
the obvious fold — elaborate the first declaration, insist nothing is left unsolved, push its name
at its now-ground type, elaborate the next against that context, and so on.

Nothing about the object language appears below. The fold is written once, against the interface,
and every language that decides its own elaboration gets a vernacular elaborator for free.

## What it produces: a substitution, not a new program

`Option { σ // HasType (pSubst p σ) }`. The answer is the *solution*, and the certificate is
about the program that was actually written — `p`, not some value the elaborator built and the
caller must then relate back to its source. The elaborated form is `pSubst p σ`, available
whenever anyone wants it (`elabProgram?`), and `Vernacular/Basic.lean`'s `Command` instance is
what makes that one application well-defined: `Program` is `Command × List Command`, and the pair
and list instances in `Substitution/Basic.lean` do the rest.

One substitution for a whole program means metavariable indices are **global to the file**: `?0`
in the third declaration is the same `?0` as in the first. That is a real commitment, and this
return type is where it is made.

## Composition, and why it is sound

The declarations are solved one at a time, so the answers have to be composed — `σ` from the head,
then whatever the tail needs, as `Subst.comp σ' σ`. Composing is only sound because a later `σ'`
lands on declarations an earlier `σ` already made **ground**, and substitution does not touch a
ground object. Groundness is not merely a well-formedness check the vernacular happens to want; it
is what makes the fold's answers combine at all.

## Four laws the interface did not state

The fold needs more than `DecideableElaborate` provides, and the gaps are not accidents of this
file.

`elaborate Γ t τ` promises `HasType (pSubst Γ σ) (pSubst t σ) (pSubst τ σ)` — a typing under the
**substituted** context. The vernacular needs it under `Γ`, the context it actually maintains.
Those agree when `Γ` is ground, but proving it needs:

* `GroundStable Ty Ty` — substitution fixes a ground type. Then a ground context is unchanged
  keywise (`Context.pSubst_get?_of_ground`).
* `LawfulContext N Tm Ty` — typing transports along keywise agreement. Needed because the
  *equation* `pSubst Γ σ = Γ` is unavailable: `Std.HashMap` has no `getElem?` extensionality, so
  keywise agreement is the strongest fact about contexts anyone here can have.

And composing the per-declaration answers needs:

* `GroundStable Tm Ty` — the same, for a term whose annotations are all solved.
* `LawfulComp Ty Ty`, `LawfulComp Tm Ty` — substituting twice is substituting once through the
  composite. Without it the fold could never describe its answers by a single `Subst`.

All four are mixins over instances already in scope, so none reopens the `HasType` diamond, and
all four hold for STLC — three are one-line packagings of existing theorems (`HasType.cong`,
`Term.pSubst_comp`, `Signature.pSubst_comp`).

Groundness must also be **decidable** to be checked. `HasVars.Ground` is `∀ n, ¬ isFree x n`,
which no instance can decide by unfolding, so the check is requested as a `DecidablePred`
instance; a language supplies it from its own structural check (STLC: `Ty.ground_iff` and
`Term.annotsGround_iff_ground` against `decide`).
-/

namespace LambdaLab.TypeSystem.Vernacular

open HasVars (Ground)

variable {N Tm Ty : Type} [NameAlphabet N]
  [DecideableElaborate N Tm Ty] [LawfulContext N Tm Ty]
  [GroundStable Ty Ty] [GroundStable Tm Ty] [LawfulComp Ty Ty] [LawfulComp Tm Ty]
  [DecidablePred (Ground : Ty → Prop)] [DecidablePred (Ground : Tm → Prop)]

/-- The typing `elaborate` returns, re-read under the context the vernacular maintains rather than
under the substituted one. This is the single step the two extra laws exist for. -/
theorem hasType_of_solution {Γ : Context N Ty} {t : Tm} {τ : Ty} {σ : Subst Ty}
    (hΓ : CtxGround Γ)
    (hσ : _root_.LambdaLab.TypeSystem.HasType.HasType
            (HasSubst.pSubst Γ σ) (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ)) :
    _root_.LambdaLab.TypeSystem.HasType.HasType Γ (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ) :=
  LawfulContext.cong (Context.pSubst_get?_of_ground Γ σ hΓ) hσ

/-- **Elaborate a list of declarations against a ground context**, returning the *substitution*
that solves them all.

Each step calls the object language's decision procedure, refuses the answer if it left a
metavariable in the declared type or the body, and continues under the context extended with the
solved type — with the head's solution already applied to the remaining declarations, so that the
tail is elaborated against what the head decided rather than against the raw source. The answers
are then composed, and the certificate is about the *original* list under that single composite.

**Why composing is sound.** A later `σ₂` is applied to declarations that an earlier `σ₁` already
made *ground*, and substitution does not touch a ground object (`GroundStable`). So extending the
answer never disturbs what earlier steps settled — which is exactly why the judgement insists on
groundness rather than merely checking it at the end.

Recursion is on the tail's *length*, not its structure: the recursive call is on
`pSubst cs σ`, which is not a subterm. `List.length_pSubst` is what makes it terminate. -/
def elabCommands : (Γ : Context N Ty) → CtxGround Γ → (cs : List (Command N Tm Ty)) →
    Option { σ : Subst Ty // HasTypeGround Γ (HasSubst.pSubst cs σ) }
  | Γ, hΓ, [] => some ⟨∅, .nil hΓ⟩
  | Γ, hΓ, Command.decl x τ t :: cs =>
      match DecideableElaborate.elaborate Γ t τ with
      | .impossible _ => none
      | .solution σ hσ =>
          if hgτ : Ground (HasSubst.pSubst τ σ) then
            if hgt : Ground (HasSubst.pSubst t σ) then
              match hrec : elabCommands (Γ.cons x (HasSubst.pSubst τ σ)) (hΓ.cons hgτ)
                             (HasSubst.pSubst cs σ) with
              | none => none
              | some ⟨σ', hσ'⟩ =>
                  some ⟨Subst.comp σ' σ, by
                    show HasTypeGround Γ (HasSubst.pSubst (Command.decl x τ t) (Subst.comp σ' σ)
                            :: HasSubst.pSubst cs (Subst.comp σ' σ))
                    rw [Command.pSubst_decl,
                        LawfulComp.pSubst_comp τ σ' σ, LawfulComp.pSubst_comp t σ' σ,
                        GroundStable.pSubst_ground σ' hgτ, GroundStable.pSubst_ground σ' hgt,
                        LawfulComp.pSubst_comp cs σ' σ]
                    exact .decl (hasType_of_solution hΓ hσ) hgτ hgt hσ'⟩
            else none
          else none
  termination_by _ _ cs => cs.length
  decreasing_by simp [List.length_pSubst]

/-- **Elaborate a whole program**: a substitution under which the *source* program is well-typed
and fully resolved.

The certificate is about `p` itself, not about some other program the elaborator built — reading
off the elaborated form is `HasSubst.pSubst p σ`, and the caller can do that whenever it wants
rather than being handed a value it must then relate back to what was written.

The empty context is ground, so `nil`'s condition is discharged by construction and never surfaces
as an obligation on the caller. -/
def elabProgram (p : Program N Tm Ty) :
    Option { σ : Subst Ty // HasType (HasSubst.pSubst p σ) } :=
  match elabCommands (Context.empty : Context N Ty) CtxGround.empty p.toList with
  | none => none
  | some ⟨σ, h⟩ => some ⟨σ, h⟩

/-- The elaborated program itself, for a caller that wants the value rather than the solution. -/
def elabProgram? (p : Program N Tm Ty) : Option (Program N Tm Ty) :=
  (elabProgram p).map (fun σ => HasSubst.pSubst p σ.val)

/-- **Soundness**, for the forgetful version: whatever comes out is a well-typed, fully resolved
program. Trivial here precisely because the certificate travels in the subtype rather than being
reconstructed afterwards. -/
theorem elabProgram?_hasType {p p' : Program N Tm Ty} (h : elabProgram? p = some p') :
    HasType p' := by
  rw [elabProgram?, Option.map_eq_some_iff] at h
  obtain ⟨σ, _, rfl⟩ := h
  exact σ.property

end LambdaLab.TypeSystem.Vernacular
