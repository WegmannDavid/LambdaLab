import LambdaLab.Stlc.Named.Typing.Basic
import LambdaLab.Stlc.Named.Typing.Unification
import LambdaLab.Stlc.Named.Typing.Properties
import LambdaLab.Substitution.Unification.Soundness
import LambdaLab.Stlc.Named.Typing.J

/-!
# The formalization target, compactly

One definition — `elabSubst`, the elaborator every consumer actually calls — its soundness proof,
and the statement `GenerationComplete` that completeness rests on. Everything else in `Typing/` is
either machinery for these or a specification to compare them against.

The obligations themselves are no longer stated here. They were, as unreferenced `Prop`s and an
`Option`-of-subtype wrapper nobody called, and keeping them meant keeping a `sorry` in a file on
the live path. They now sit where they can be discharged: completeness as `JComplete`'s theorems,
most-generality as `TypeSystem.Named.PrincipalElaborate`'s field.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Nominal (Atoms)

variable {N : Type} [Atoms N] [HasVars N]

/-! ## Deciding groundness

`Term.AnnotsGround` is a `Prop` recursion; this is the same recursion in `Bool`, which is what lets
the elaborator *demand* that no metavariable survives.
-/

/-- Every type annotation inside `e` is ground, decidably. -/
def Term.annotsGround : Term N → Bool
  | .var _        => true
  | .lam _ τ body => τ.isGround && body.annotsGround
  | .app e₁ e₂    => e₁.annotsGround && e₂.annotsGround

omit [Atoms N] [HasVars N] in
@[simp] theorem Term.annotsGround_iff : ∀ {e : Term N}, e.annotsGround = true ↔ e.AnnotsGround := by
  intro e
  induction e with
  | var x => simp [Term.annotsGround, Term.AnnotsGround]
  | lam x τ body ih => simp [Term.annotsGround, Term.AnnotsGround, ih, Ty.Ground]
  | app e₁ e₂ ih₁ ih₂ => simp [Term.annotsGround, Term.AnnotsGround, ih₁, ih₂]

instance (e : Term N) : Decidable e.AnnotsGround :=
  decidable_of_iff (e.annotsGround = true) Term.annotsGround_iff

/-! ## The formalization target -/

/-- The threshold above which every index belongs to the algorithm rather than the source.
Same definition as `W.srcFresh`, repeated so this file depends on no particular algorithm. -/
def sourceFresh (Γ : Ctx N) (t : Term N) (τ : Ty) : Nat :=
  max (HasVars.fresh Γ) (max (HasVars.fresh t) (HasVars.fresh τ))

/-! ## The algorithm, and its soundness

The *computation* is separated from the proofs about it, so that consumers which only need a
working, certified-sound elaborator inherit nothing else. Both declarations below are sorry-free,
and so is everything downstream of them: completeness is `JComplete.elabSubst_complete`, and the
two together are packaged as `JComplete.elabSolution`. Note it is `JComplete.elabMGU` that fills
`TypeSystem.Named.PrincipalElaborate` — `elabSolution` plus the still-open `elabSubst_principal` — so the
sorry-free path stops here, and `elabSolution` is what to use when most-generality is not wanted.

This file used to also carry `elaborate`, returning a subtype that demanded most-generality
alongside the typing, and `Complete`, the corresponding `none`-case obligation. Nothing ever
consumed either: the elaborator on the live path is `elabSubst`, and the two obligations are now
stated where an instance can discharge them — most-generality as
`TypeSystem.Named.PrincipalElaborate`'s comparison, completeness as a theorem. Both are deleted rather
than kept as an unreferenced specification carrying the file's only `sorry`.
-/

/-- **The computation.** Generate every constraint, then solve once — with the *declared* type
thrown in as one more equation, which is how a synthesising generator handles a checking problem.

The answer is returned **pruned**: the raw solution binds the variables `gen` drew, which mean
nothing to a competing σ' and would defeat most-generality outright.

Built from `J`, not `W`. W's answer is a composition of substitutions accumulated during the
traversal, so its most-generality is entangled with the freshness discipline. J's answer is
*literally* `unify`'s output. -/
def elabSubst (Γ : Ctx N) (t : Term N) (τ : Ty) : Option (Subst Ty) :=
  match gen Γ t (sourceFresh Γ t τ) with
  | none => none
  | some r => (unify ((r.1, τ) :: r.2.1)).map (Subst.restrictBelow · (sourceFresh Γ t τ))

/-- **Soundness of the computation**, and it is short: `gen_correct` moves to the judgement,
`HasTypeJ.sound` does the work, the head equation rewrites the synthesised type into the declared
one, and pruning above the source threshold disturbs none of `Γ`, `t`, `τ`. -/
theorem elabSubst_sound {Γ : Ctx N} {t : Term N} {τ : Ty} {σ : Subst Ty}
    (h : elabSubst Γ t τ = some σ) :
    HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ) := by
  rw [elabSubst] at h
  split at h
  · exact absurd h (by simp)
  · rename_i r hg
    rw [Option.map_eq_some_iff] at h
    obtain ⟨σ₀, hu, rfl⟩ := h
    have hall : Subst.Unifies σ₀ ((r.1, τ) :: r.2.1) := unify_unifies _ σ₀ hu
    have hsound := (gen_correct t Γ _ r.1 r.2.1 r.2.2 hg).sound
      (fun q hq => hall q (List.mem_cons_of_mem _ hq))
    have hhead : HasSubst.pSubst r.1 σ₀ = HasSubst.pSubst τ σ₀ := hall _ List.mem_cons_self
    rw [hhead] at hsound
    have hΓf : HasVars.fresh Γ ≤ sourceFresh Γ t τ := Nat.le_max_left _ _
    have htf : HasVars.fresh t ≤ sourceFresh Γ t τ :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hτf : HasVars.fresh τ ≤ sourceFresh Γ t τ :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    rw [Term.tyPSubst_restrictBelow t σ₀ _ htf, Signature.pSubst_restrictBelow σ₀ _ τ hτf]
    exact HasType.cong (fun y => (Ctx.pSubst_restrictBelow_get? Γ σ₀ _ hΓf y).symm) hsound

/-- **Proved**, in `Typing/JComplete.lean` — see `generationComplete`. It was long described here
as "the one missing lemma"; it was missing, but it was never the whole of what stands between the
elaborator and principality. See the second half of this docstring.

`unify_mgu` already says the computed σ is most general among *unifiers of the constraints*. To
turn that into most general among *typings*, one needs the converse of `HasTypeJ.sound`: every
substitution that types the triple satisfies the generated constraints.

It cannot be σ' itself — the constraints mention the variables `gen` drew, about which σ' says
nothing — so the statement produces an extension agreeing with σ' on everything below the starting
supply. The proof is an induction on the `HasTypeJ` derivation, needing a bound on which variables
the constraints mention (`HasTypeJ.fresh_bound`, the analogue of `HasTypeJ.supply_le`) and a notion
of substitutions agreeing below `n` (`AgreeBelow`). One wrinkle the sketch missed: this checking
form does not induct, because the `lam` case would have to split a declared `τ` that may be a bare
metavariable. `JComplete.complete_aux` is the synthesising form that does.

**And it is exactly half of most-generality.** `unify_mgu` then gives `MoreGeneral σ σ''`, and
transferring that to σ' works *below the source threshold* and only there: the pruned
substitution's **range** need not stay below it — unifying `(?0, ⋆ → ?d)` for a drawn `?d` binds
the source variable `?0` to a type mentioning `?d` — so above the threshold there is nothing to
transfer. That is not a gap in the argument but a fact about the problem:
`Typing/Principality.lean` proves the unrestricted claim false. The restricted one is
`JComplete.elabSubst_principal_below`, and it is what `TypeSystem.Named.PrincipalElaborate` asks for. -/
def GenerationComplete : Prop :=
  ∀ (Γ : Ctx N) (t : Term N) (τ τg : Ty) (n n' : Nat) (C : Equations Ty) (σ' : Subst Ty),
    HasVars.fresh Γ ≤ n → HasVars.fresh t ≤ n → HasVars.fresh τ ≤ n →
    HasTypeJ n Γ t τg C n' →
    HasType (HasSubst.pSubst Γ σ') (HasSubst.pSubst t σ') (HasSubst.pSubst τ σ') →
    ∃ σ'', Subst.Unifies σ'' ((τg, τ) :: C) ∧
      ∀ u : Ty, HasVars.fresh u ≤ n → HasSubst.pSubst u σ'' = HasSubst.pSubst u σ'

end LambdaLab.Stlc.Named
