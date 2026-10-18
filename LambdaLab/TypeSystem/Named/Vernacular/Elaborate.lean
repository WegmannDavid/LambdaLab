import LambdaLab.TypeSystem.Named.Vernacular.Typing
import LambdaLab.Semantics.Walk

/-!
# The program elaborator, as a walk

A calculus that implements `PrincipalElaborate` decides *one* checking problem: under `Γ`, does
`t` elaborate against `τ`, and by which substitution. This file lifts that to a whole program as a
`Walk` (`Semantics/Walk.lean`): elaborate the first declaration, insist nothing is left unsolved,
push its name at its now-ground type, elaborate the next in that context, and so on.

Nothing about the object language appears below. The walk is written once, against the interface,
and every language that decides its own elaboration gets a program elaborator for free. The fold
ignores the most-generality half of `elaborate` — it needs *a* solution per declaration, not the
best one — so `.mgu`'s third argument is discarded.

## The state

Two things are carried from one declaration to the next:

* **the context** — every earlier declaration's name at its solved type, which is what the next
  declaration is checked against;
* **the solved metavariables.** Metavariable indices are **global to the file**: `?0` in the third
  declaration is the same `?0` as in the first. So a step first applies everything solved so far
  to its declaration, and only then elaborates it.

## Each step rewrites its declaration to a ground one

`elaborate` answers with a substitution; the step applies it, and refuses the answer if the
declared type or the body still holds a metavariable — the vernacular's judgement
(`HasTypeGround`) demands ground declarations, and a declaration is a commitment later ones are
checked against. What the step hands on is the elaborated declaration itself.

## Why it is sound, and why it is idempotent

`elaborate Γ t τ` promises `HasType (pSubst Γ σ) (pSubst t σ) (pSubst τ σ)` — a typing under the
**substituted** context. The walk needs it under `Γ`, the context it actually maintains. Those
agree because `Γ` is ground: `GroundStable` makes substitution fix it keywise, and
`LawfulTypeSystem.cong` transports the typing along keywise agreement (`hasType_of_solution`). So
everything the walk produces is well-typed (`elabWalk_sound`).

Idempotence then has nothing to do with the solved metavariables. A well-typed program is ground,
and substitution does not touch a ground object, so on such a program every substitution the walk
applies is the identity and every `elaborate` succeeds: the walk returns the program unchanged
(`elabWalk_self`), *whatever* metavariables its state has recorded. That is why the law is proved
for whole programs rather than a step at a time — re-elaborating a ground declaration records a
solution of its own, so the *state* after the second pass need not equal the state after the first,
even though every declaration does.

Together: the walk's fixed points are exactly the well-typed programs (`elabWalk_fixed_iff`).

## What the walk needs of the language

`PrincipalElaborate`, and nothing else. `cong` comes from `LawfulTypeSystem` and `GroundStable`
from `LawfulMVars`, both parents of it; groundness is decided by its `tyGroundDec`/`tmGroundDec`.
-/

namespace LambdaLab.TypeSystem.Named.Vernacular

open HasVars (Ground)
open LambdaLab.Nominal (Atom)
open LambdaLab.Semantics (Walk)

variable {N Tm Ty : Type} [Atom N] [PrincipalElaborate N Tm Ty]

/-- The typing `elaborate` returns, re-read under the context the walk maintains rather than under
the substituted one. This is the single step `cong` and `GroundStable` exist for here. -/
theorem hasType_of_solution {Γ : Context N Ty} {t : Tm} {τ : Ty} {σ : Subst Nat Ty}
    (hΓ : CtxGround Γ)
    (hσ : HasSubst.pSubst Γ σ ⊢ HasSubst.pSubst t σ : HasSubst.pSubst τ σ) :
    Γ ⊢ HasSubst.pSubst t σ : HasSubst.pSubst τ σ :=
  LawfulTypeSystem.cong (Context.pSubst_get?_of_ground Γ σ hΓ) hσ

/-- What elaboration carries from one declaration to the next. -/
structure ElabState (N Ty : Type) [Atom N] where
  /-- Every earlier declaration's name, at its solved type. -/
  ctx : Context N Ty
  /-- Every metavariable solved so far. -/
  solved : Subst Nat Ty

/-! Names are displayed in a rejection's diagnostic. -/
variable [ToString N]

/-- **Elaborate one declaration**: apply what is already solved, elaborate against the context,
and keep the answer only if it leaves nothing unsolved. -/
def elabStep (s : ElabState N Ty) :
    Command N Tm Ty → Except String (Command N Tm Ty × ElabState N Ty)
  | .decl x τ t =>
      match PrincipalElaborate.elaborate s.ctx (HasSubst.pSubst t s.solved)
          (HasSubst.pSubst τ s.solved) with
      | .impossible _ =>
          .error (PrincipalElaborate.explain (fun y : N => toString y) s.ctx (HasSubst.pSubst t s.solved)
            (HasSubst.pSubst τ s.solved))
      | .mgu σ _ _ =>
          if Ground (HasSubst.pSubst (HasSubst.pSubst τ s.solved) σ) ∧
              Ground (HasSubst.pSubst (HasSubst.pSubst t s.solved) σ) then
            .ok (.decl x (HasSubst.pSubst (HasSubst.pSubst τ s.solved) σ)
                (HasSubst.pSubst (HasSubst.pSubst t s.solved) σ),
              ⟨s.ctx.cons x (HasSubst.pSubst (HasSubst.pSubst τ s.solved) σ),
                Subst.comp σ s.solved⟩)
          else .error (PrincipalElaborate.explainUnsolved (N := N) (fun y : N => toString y)
            (HasSubst.pSubst (HasSubst.pSubst t s.solved) σ)
            (HasSubst.pSubst (HasSubst.pSubst τ s.solved) σ))

/-- **The program elaborator**: the walk from the empty context, nothing solved. -/
def elabWalk : Walk (Command N Tm Ty) where
  State := ElabState N Ty
  init := ⟨Context.empty, ∅⟩
  step := elabStep

/-! ## Soundness -/

/-- What one step produces is a ground declaration, typed in the context it was elaborated in, and
the next context is that one extended with it. -/
theorem elabStep_sound {s : ElabState N Ty} {x : N} {τ : Ty} {t : Tm}
    {d : Command N Tm Ty} {s' : ElabState N Ty} (hΓ : CtxGround s.ctx)
    (h : elabStep s (.decl x τ t) = .ok (d, s')) :
    ∃ τ' t', d = .decl x τ' t' ∧ s'.ctx = s.ctx.cons x τ' ∧ (s.ctx ⊢ t' : τ') ∧
      Ground τ' ∧ Ground t' := by
  simp only [elabStep] at h
  split at h
  · cases h
  · rename_i σ hσ _ _
    split at h
    · rename_i hg
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, _, rfl, rfl, hasType_of_solution hΓ hσ, hg.1, hg.2⟩
    · cases h

theorem elabRunFrom_sound : ∀ (s : ElabState N Ty) (cs cs' : List (Command N Tm Ty)),
    CtxGround s.ctx → (elabWalk (N := N) (Tm := Tm) (Ty := Ty)).runFrom s cs = .ok cs' →
      HasTypeGround s.ctx cs'
  | s, [], cs', hΓ, h => by
      simp only [Walk.runFrom, Except.ok.injEq] at h
      subst h
      exact .nil hΓ
  | s, .decl x τ t :: cs, cs', hΓ, h => by
      obtain ⟨d, s', rest, hs, hr, rfl⟩ := Walk.runFrom_cons_ok _ h
      obtain ⟨τ', t', rfl, hctx, hty, hτ', ht'⟩ := elabStep_sound hΓ hs
      have hrest := elabRunFrom_sound s' cs rest (hctx ▸ hΓ.cons hτ') hr
      exact .decl hty hτ' ht' (hctx ▸ hrest)

/-- **Soundness**: whatever the walk produces is a well-typed, fully resolved program. -/
theorem elabWalk_sound {p q : Program N Tm Ty}
    (h : (elabWalk (N := N) (Tm := Tm) (Ty := Ty)).run p = .ok q) : HasType q :=
  elabRunFrom_sound _ _ _ CtxGround.empty ((Walk.run_eq_ok _).mp h)

/-! ## A well-typed program is a fixed point -/

/-- On a ground declaration that already types, a step returns it unchanged. Both branches use
groundness. An `.impossible` answer claims *no* substitution types the declaration; instantiating it
at `∅` and stripping the substitutions off contradicts the derivation — the context is handled by
`cong`, since `pSubst Γ ∅ = Γ` is only available keywise. A `.mgu` answer passes both `Ground`
checks, and leaves the declaration as it was. -/
theorem elabStep_self {s : ElabState N Ty} {x : N} {τ : Ty} {t : Tm}
    (hΓ : CtxGround s.ctx) (hty : s.ctx ⊢ t : τ) (hτ : Ground τ) (ht : Ground t) :
    ∃ s', elabStep s (.decl x τ t) = .ok (.decl x τ t, s') ∧ s'.ctx = s.ctx.cons x τ := by
  have eτ : HasSubst.pSubst τ s.solved = τ := GroundStable.pSubst_ground s.solved hτ
  have et : HasSubst.pSubst t s.solved = t := GroundStable.pSubst_ground s.solved ht
  simp only [elabStep]
  split
  · rename_i hno _
    refine absurd ?_ (hno ∅)
    rw [eτ, et, GroundStable.pSubst_ground (∅ : Subst Nat Ty) ht,
      GroundStable.pSubst_ground (∅ : Subst Nat Ty) hτ]
    exact LawfulTypeSystem.cong (fun y => (Context.pSubst_get?_of_ground s.ctx ∅ hΓ y).symm) hty
  · rename_i σ _ _ _
    have e1 : HasSubst.pSubst (HasSubst.pSubst τ s.solved) σ = τ := by
      rw [eτ, GroundStable.pSubst_ground σ hτ]
    have e2 : HasSubst.pSubst (HasSubst.pSubst t s.solved) σ = t := by
      rw [et, GroundStable.pSubst_ground σ ht]
    rw [if_pos (by rw [e1, e2]; exact ⟨hτ, ht⟩)]
    exact ⟨⟨s.ctx.cons x τ, Subst.comp σ s.solved⟩, by rw [e1, e2], rfl⟩

theorem elabRunFrom_self : ∀ (s : ElabState N Ty) (cs : List (Command N Tm Ty)),
    CtxGround s.ctx → HasTypeGround s.ctx cs →
      (elabWalk (N := N) (Tm := Tm) (Ty := Ty)).runFrom s cs = .ok cs
  | _, [], _, _ => rfl
  | s, .decl x τ t :: cs, hΓ, h => by
      cases h with
      | decl hty hτ ht hrest =>
          obtain ⟨s', hstep, hctx⟩ := elabStep_self (x := x) hΓ hty hτ ht
          have hstep' : (elabWalk (N := N) (Tm := Tm) (Ty := Ty)).step s (.decl x τ t)
              = .ok (.decl x τ t, s') := hstep
          have hΓ' : CtxGround s'.ctx := hctx ▸ hΓ.cons hτ
          have hrest' : HasTypeGround s'.ctx cs := hctx ▸ hrest
          exact Walk.runFrom_cons_of _ hstep' (elabRunFrom_self s' cs hΓ' hrest')

/-- **An elaborated program re-elaborates to itself.** The canonical surface form of a well-typed
program is the program, which is what gives a front end a printer whose output re-reads. -/
theorem elabWalk_self {q : Program N Tm Ty} (h : HasType q) :
    (elabWalk (N := N) (Tm := Tm) (Ty := Ty)).run q = .ok q :=
  (Walk.run_eq_ok _).mpr (elabRunFrom_self _ _ CtxGround.empty h)

/-- **The law.** -/
theorem elabWalk_idempotent : (elabWalk (N := N) (Tm := Tm) (Ty := Ty)).Idempotent :=
  fun _ _ h => elabWalk_self (elabWalk_sound h)

/-- **What elaboration produces is exactly the well-typed programs**: its fixed points are those,
and nothing else. -/
theorem elabWalk_fixed_iff {q : Program N Tm Ty} :
    (elabWalk (N := N) (Tm := Tm) (Ty := Ty)).run q = .ok q ↔ HasType q :=
  ⟨elabWalk_sound, elabWalk_self⟩

end LambdaLab.TypeSystem.Named.Vernacular
