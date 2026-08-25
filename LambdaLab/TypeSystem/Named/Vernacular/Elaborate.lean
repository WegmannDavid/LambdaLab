import LambdaLab.TypeSystem.Named.Vernacular.Typing

/-!
# The program elaborator, derived from the object language's

A calculus that implements `PrincipalElaborate` decides *one* checking problem: under `Γ`, does
`t` elaborate against `τ`, and by which substitution. The fold ignores the most-generality half —
it needs *a* solution per declaration, not the best one — but a language must supply it, so
`.mgu`'s third argument is discarded below. This file lifts that to a whole program, by
the obvious fold — elaborate the first declaration, insist nothing is left unsolved, push its name
at its now-ground type, elaborate the next against that context, and so on.

Nothing about the object language appears below. The fold is written once, against the interface,
and every language that decides its own elaboration gets a vernacular elaborator for free.

## What it produces: a substitution, not a new program

`Option { σ // HasType (pSubst p σ) ∧ Minimal p σ }`. The answer is the *solution*, and the
certificate is about the program that was actually written — `p`, not some value the elaborator
built and the caller must then relate back to its source. The elaborated form is `pSubst p σ`,
available whenever anyone wants it (`elabProgram?`), and `Vernacular/Basic.lean`'s `Command`
instance is what makes that one application well-defined: `Program` is `Command × List Command`,
and the pair and list instances in `Nominal/Unification/Subst.lean` do the rest.

The second conjunct says σ binds nothing at or above `p`'s own threshold — no redundant bindings.
It is a condition on σ's *domain*; see `Minimal` below for why that is the honest strengthening
available here and `MGUProp` is not.

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

The fold needs more than `PrincipalElaborate` provides, and the gaps are not accidents of this
file.

`elaborate Γ t τ` promises `HasType (pSubst Γ σ) (pSubst t σ) (pSubst τ σ)` — a typing under the
**substituted** context. The vernacular needs it under `Γ`, the context it actually maintains.
Those agree when `Γ` is ground, but proving it needs:

* `GroundStable Nat Ty Ty` — substitution fixes a ground type. Then a ground context is unchanged
  keywise (`Context.pSubst_get?_of_ground`).
* `LawfulTypeSystem.cong` — typing transports along keywise agreement. Needed because the
  *equation* `pSubst Γ σ = Γ` is unavailable: `Std.HashMap` has no `getElem?` extensionality, so
  keywise agreement is the strongest fact about contexts anyone here can have.

And composing the per-declaration answers needs:

* `GroundStable Nat Tm Ty` — the same, for a term whose annotations are all solved.
* `LawfulComp Nat Ty Ty`, `LawfulComp Nat Tm Ty` — substituting twice is substituting once through the
  composite. Without it the fold could never describe its answers by a single `Subst`.

All four are mixins over instances already in scope, so none reopens the `HasType` diamond, and
all four hold for STLC — three are one-line packagings of existing theorems (`HasType.cong`,
`Term.pSubst_comp`, `Signature.pSubst_comp`).

A fifth, `LawfulRestrict`, is not needed by the fold but by what `elabProgram` does with its
result; it is discussed under "Pruning" below.

Groundness must also be **decidable** to be checked. `HasVars.Ground` is `∀ n, ¬ isFree x n`,
which no instance can decide by unfolding, so the check is requested as a `DecidablePred`
instance; a language supplies it from its own structural check (STLC: `Ty.ground_iff` and
`Term.annotsGround_iff_ground` against `decide`).
-/

namespace LambdaLab.TypeSystem.Named.Vernacular

open HasVars (Ground)
open LambdaLab.Nominal (Atom)

/-! ## What the fold asks for: `PrincipalElaborate`, and nothing else

Everything below runs off a single binder. That was not always so — the laws and decision
procedures the fold needs used to be collected here in a seven-field `Elaboratable` class whose
every field was `inferInstance`. They have since moved to the classes that *own* them:
`cong` to `LawfulTypeSystem` (a property of the judgement), the four `GroundStable`/`LawfulComp`
laws to `LawfulMVars` (properties of the substitution action), and the two `DecidablePred Ground`
to `PrincipalElaborate` itself. Each is justified there without reference to a vernacular, so
`TypeSystem/Named/Basic.lean` still does not know this file exists.
-/

variable {N Tm Ty : Type} [Atom N] [PrincipalElaborate N Tm Ty]

/-- The typing `elaborate` returns, re-read under the context the vernacular maintains rather than
under the substituted one. This is the single step the two extra laws exist for. -/
theorem hasType_of_solution {Γ : Context N Ty} {t : Tm} {τ : Ty} {σ : Subst Nat Ty}
    (hΓ : CtxGround Γ)
    (hσ : _root_.LambdaLab.TypeSystem.Named.HasType.HasType
            (HasSubst.pSubst Γ σ) (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ)) :
    _root_.LambdaLab.TypeSystem.Named.HasType.HasType Γ (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ) :=
  LawfulTypeSystem.cong (Context.pSubst_get?_of_ground Γ σ hΓ) hσ

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
    Option { σ : Subst Nat Ty // HasTypeGround Γ (HasSubst.pSubst cs σ) }
  | Γ, hΓ, [] => some ⟨∅, .nil hΓ⟩
  | Γ, hΓ, Command.decl x τ t :: cs =>
      match PrincipalElaborate.elaborate Γ t τ with
      | .impossible _ => none
      | .mgu σ hσ _ =>
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

/-! ## Pruning: the answer is about the source, and only about the source

The fold's composite binds more than the program mentions. Each step's `elaborate` draws its own
fresh metavariables, and although a language is expected to prune its *own* scaffolding (STLC's
`elabSubst` restricts below `sourceSupp`), the fold then elaborates the tail against
`pSubst cs σ` — a term whose metavariables may sit above anything in the source, because a solved
binding's *range* can reach up even when its domain does not. Those bindings are algorithm
exhaust. They are invisible to `p`, they are not part of the answer, and handing them to a caller
invites it to depend on them.

So `elabProgram` restricts the composite to `p`'s own threshold before returning it, and records
that it did. This is the same boundary-pruning `Target.elabSubst` performs one level down — option
D of the principal-types discussion, applied to a program instead of a term. -/

/-- **No redundant bindings**: σ binds no metavariable at or above `x`'s threshold.

This is a condition on σ's *domain*, and it is deliberately not phrased through `MoreGeneral`,
which constrains a substitution's action and says nothing about what it binds. It is also the
weaker, numeric reading of "no redundant bindings" rather than the support condition
`dom σ ⊆ mvars x`: proving the latter would need `elaborate` to promise something about its own
domain, a field the interface does not have. Note too that `freshIdx` is only required to be
exact, so this is now the sharp statement — the old one only bounded the indices.

Stated get?-wise rather than as `σ = Subst.restrictTo σ (supp x)`: `Std.HashMap` has no
`getElem?` extensionality here, so the equation is not available even when it is true. -/
def Minimal {𝕋 𝕊 : Type} [HasVars Nat 𝕋] (x : 𝕋) (σ : Subst Nat 𝕊) : Prop :=
  ∀ a, σ.get? a ≠ none → HasVars.isFree x a

/-- Pruning at exactly the threshold is what makes minimality true by construction, rather than
something to be recovered afterwards from facts the interface does not supply. -/
theorem minimal_restrictTo {𝕋 𝕊 : Type} [HasVars Nat 𝕋] (x : 𝕋) (σ : Subst Nat 𝕊) :
    Minimal x (Subst.restrictTo σ (HasVars.supp (A := Nat) x)) := by
  intro a ha
  rw [Subst.restrictTo_get?] at ha
  by_cases h : a ∈ HasVars.supp (A := Nat) x
  · exact (HasVars.mem_supp_iff_isFree x a).mp h
  · rw [if_neg h] at ha
    exact absurd rfl ha

/-- **Elaborate a whole program**: a substitution under which the *source* program is well-typed
and fully resolved, binding nothing the source does not reach.

The certificate is about `p` itself, not about some other program the elaborator built — reading
off the elaborated form is `HasSubst.pSubst p σ`, and the caller can do that whenever it wants
rather than being handed a value it must then relate back to what was written.

The empty context is ground, so `nil`'s condition is discharged by construction and never surfaces
as an obligation on the caller. -/
def elabProgram (p : Program N Tm Ty) :
    Option { σ : Subst Nat Ty // HasType (HasSubst.pSubst p σ) ∧ Minimal p σ } :=
  match elabCommands (Context.empty : Context N Ty) CtxGround.empty p.toList with
  | none => none
  | some ⟨σ, h⟩ =>
      some ⟨Subst.restrictTo σ (HasVars.supp (A := Nat) p), by
        refine ⟨?_, minimal_restrictTo p σ⟩
        rw [LawfulRestrict.pSubst_restrictTo p σ _
          (fun a ha => (HasVars.mem_supp_iff_isFree p a).mpr ha)]
        exact h⟩

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
  exact σ.property.1

/-! ## An elaborated program is a fixed point of the elaborator

Soundness says what comes out is well-typed. This is the converse *on the image*: run the
elaborator on a program that is already well-typed and fully resolved, and it succeeds and returns
that program unchanged.

It is not completeness — nothing here says a program with unsolved metavariables elaborates, and
in general it need not (`elaborate` returns *a* solution, not a most general one, so an earlier
declaration may commit to a type a later one cannot live with). What is claimed is exactly the
part a front end needs: **the elaborated form is its own canonical source**, so a printer has
something to print and re-reading what it printed lands back where it started.

The proof rests on one observation, and it is the same one that makes the fold's substitutions
compose: a well-typed program is *ground*, and substitution does not touch a ground object. So
every substitution the fold applies to it is the identity, and the recursion runs down the
original list with the original context. -/

/-- Every declaration in a well-typed run is ground, hence so is the run — at the `List` instance,
which is what the fold substitutes through. -/
theorem HasTypeGround.ground {Γ : Context N Ty} {cs : List (Command N Tm Ty)}
    (h : HasTypeGround Γ cs) : Ground cs := by
  rintro n ⟨c, hc, hn⟩
  obtain ⟨x, τ, t⟩ := c
  obtain ⟨hτ, ht⟩ := h.ground_of_mem hc
  have hn' : HasVars.isFree τ n ∨ HasVars.isFree t n := hn
  exact hn'.elim (hτ n) (ht n)

/-- The same for a program, through the pair instance: `Program` is head-and-tail, and both are
ground. -/
theorem HasType.ground {p : Program N Tm Ty} (h : HasType p) : Ground p := by
  intro n hn
  refine HasTypeGround.ground h n ?_
  have hn' : HasVars.isFree p.1 n ∨ HasVars.isFree p.2 n := hn
  exact hn'.elim (fun h₁ => ⟨p.1, by simp [NEList.toList], h₁⟩)
    (fun ⟨c, hc, hcn⟩ => ⟨c, by simp [NEList.toList, hc], hcn⟩)

/-- The `CtxGround` argument is a proof, and equal contexts and command lists give equal answers —
so it never has to be threaded through a rewrite. This is what lets the ground case rewrite
`Γ.cons x (pSubst τ σ)` to `Γ.cons x τ` underneath a `elabCommands` application. -/
theorem elabCommands_isSome_congr {Γ Γ' : Context N Ty} (hΓ : CtxGround Γ) (hΓ' : CtxGround Γ')
    {cs cs' : List (Command N Tm Ty)} (hΓeq : Γ = Γ') (hcs : cs = cs') :
    (elabCommands Γ hΓ cs).isSome = (elabCommands Γ' hΓ' cs').isSome := by
  subst hΓeq; subst hcs; rfl

/-- **The elaborator does not refuse an already-elaborated run.**

Both branches use groundness. A `.impossible` answer claims *no* substitution types the
declaration; instantiating it at `∅` and using groundness to strip the substitutions off `t` and
`τ` contradicts the derivation directly — the context is handled by `cong`, since
`pSubst Γ ∅ = Γ` is only available keywise. A `.mgu` answer passes both `Ground` checks for
the same reason, and recurses on a list and a context that groundness shows are the originals. -/
theorem elabCommands_isSome_of_hasTypeGround :
    ∀ {Γ : Context N Ty} {cs : List (Command N Tm Ty)}, HasTypeGround Γ cs →
      ∀ hΓ : CtxGround Γ, (elabCommands Γ hΓ cs).isSome := by
  intro Γ cs h
  induction h with
  | nil _ => intro hΓ; rw [elabCommands]; rfl
  | @decl Γ x τ t cs hty hτ ht hrest ih =>
      intro hΓ
      rw [elabCommands]
      split
      · rename_i hno _
        refine absurd ?_ (hno ∅)
        rw [GroundStable.pSubst_ground (∅ : Subst Nat Ty) ht,
            GroundStable.pSubst_ground (∅ : Subst Nat Ty) hτ]
        exact LawfulTypeSystem.cong (fun y => (Context.pSubst_get?_of_ground Γ ∅ hΓ y).symm) hty
      · rename_i σ _ _ _
        have hgτ : Ground (HasSubst.pSubst τ σ) := by
          rw [GroundStable.pSubst_ground σ hτ]; exact hτ
        have hgt : Ground (HasSubst.pSubst t σ) := by
          rw [GroundStable.pSubst_ground σ ht]; exact ht
        rw [dif_pos hgτ, dif_pos hgt]
        have key : (elabCommands (Γ.cons x (HasSubst.pSubst τ σ)) (hΓ.cons hgτ)
                      (HasSubst.pSubst cs σ)).isSome := by
          rw [elabCommands_isSome_congr (hΓ.cons hgτ) (hΓ.cons hτ)
                (by rw [GroundStable.pSubst_ground σ hτ])
                (GroundStable.pSubst_ground σ hrest.ground)]
          exact ih (hΓ.cons hτ)
        cases hrec : elabCommands (Γ.cons x (HasSubst.pSubst τ σ)) (hΓ.cons hgτ)
                       (HasSubst.pSubst cs σ) with
        | none => rw [hrec] at key; exact absurd key (by simp)
        | some r => obtain ⟨σ', hσ'⟩ := r; rfl

/-- **An elaborated program re-elaborates to itself.** The canonical surface form of a well-typed
program is the program, which is what gives a front end a printer whose output re-reads. -/
theorem elabProgram?_self {p : Program N Tm Ty} (h : HasType p) : elabProgram? p = some p := by
  have hs : (elabCommands (Context.empty : Context N Ty) CtxGround.empty p.toList).isSome :=
    elabCommands_isSome_of_hasTypeGround h CtxGround.empty
  rw [elabProgram?, elabProgram]
  cases hc : elabCommands (Context.empty : Context N Ty) CtxGround.empty p.toList with
  | none => rw [hc] at hs; exact absurd hs (by simp)
  | some s =>
      obtain ⟨σ, hσ⟩ := s
      rw [Option.map_some, Option.some.injEq]
      -- Pruning is irrelevant here: `p` is ground, so *every* substitution fixes it, restricted
      -- or not.
      exact GroundStable.pSubst_ground _ h.ground

end LambdaLab.TypeSystem.Named.Vernacular
