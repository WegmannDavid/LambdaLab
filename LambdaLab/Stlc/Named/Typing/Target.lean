import LambdaLab.Stlc.Named.Typing.Basic
import LambdaLab.Stlc.Named.Typing.Unification
import LambdaLab.Stlc.Named.Typing.Properties
import LambdaLab.Substitution.Unification.Soundness
import LambdaLab.Substitution.Unification.MGU
import LambdaLab.Stlc.Named.Typing.J

/-!
# The formalization target, compactly

One definition and two obligations. Everything else in `Typing/` is either machinery for these or
a specification to compare them against.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.TypeSystem (NameAlphabet)

variable {N : Type} [NameAlphabet N] [HasVars N]

/-! ## Deciding groundness

`Term.AnnotsGround` is a `Prop` recursion; this is the same recursion in `Bool`, which is what lets
the elaborator *demand* that no metavariable survives.
-/

/-- Every type annotation inside `e` is ground, decidably. -/
def Term.annotsGround : Term N → Bool
  | .var _        => true
  | .lam _ τ body => τ.isGround && body.annotsGround
  | .app e₁ e₂    => e₁.annotsGround && e₂.annotsGround

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

/-- **What elaboration must produce**: a substitution under which the declared triple is a real
typing, *and* which is at least as general as any other that does.

Both halves are in the subtype, so neither soundness nor principality is a separate obligation —
producing a value of this type discharges them. Only completeness (below) is left outside, because
it is a statement about the `none` case and so cannot live in the payload.

Note this forces the returned σ to be **pruned**. An algorithm's raw output carries bindings for
its own internal fresh variables, which mean nothing to a competing `σ'`, and `MoreGeneral` fails
at exactly those. Pruning below `sourceFresh` drops them and keeps the source ones — and the
typing half survives pruning, since none of `Γ`, `t`, `τ` mentions an index that high.

This is the same shape as `W.Elaboration`, arrived at from the other direction. -/
abbrev elaborationResult (Γ : Ctx N) (t : Term N) (τ : Ty) :=
  { σ // HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ)
       ∧ ∀ σ', HasType (HasSubst.pSubst Γ σ') (HasSubst.pSubst t σ') (HasSubst.pSubst τ σ') →
           MoreGeneral σ σ' }

/-! ## The algorithm, in three pieces

The *computation* is separated from the two proofs, so that consumers which only need a working,
certified-sound elaborator do not inherit the open obligation. `elabSubst` and `elabSubst_sound`
are sorry-free; only `elaborate`, which bundles the unproved conjunct, is not.
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

/-- **The target**: the same computation, carrying both conjuncts. Only the second is open. -/
def elaborate (Γ : Ctx N) (hΓ : Γ.Ground) (t : Term N) (τ : Ty) :
    Option (elaborationResult Γ t τ) :=
  match h : elabSubst Γ t τ with
  | none => none
  | some σ => some ⟨σ, elabSubst_sound h, by sorry⟩

/-- **The one missing lemma**, and the whole of what stands between `elaborate` and being done.

`unify_mgu` already says the computed σ is most general among *unifiers of the constraints*. To
turn that into most general among *typings*, one needs the converse of `HasTypeJ.sound`: every
substitution that types the triple satisfies the generated constraints.

It cannot be σ' itself — the constraints mention the variables `gen` drew, about which σ' says
nothing — so the statement produces an extension agreeing with σ' on everything below the starting
supply. Proving it is an induction on the `HasTypeJ` derivation, needing a bound on which variables
the constraints mention (the analogue of `HasTypeJ.supply_le`) and a lemma that substitutions
agreeing below `n` act alike on types whose variables are below `n`.

**And that is not the end of it.** `unify_mgu` then gives `MoreGeneral σ σ''`, and transferring
that to σ' needs the generality witness patched above the threshold — sound only if the *pruned*
substitution's **range** also stays below it. It need not: unifying `(?0, ⋆ → ?d)` for a drawn `?d`
binds the source variable `?0` to a type mentioning `?d`. Establishing that bound is the same
obstacle `W_principal` has, reached by a different road, and it is the reason this conjunct is not
a short proof. -/
def GenerationComplete : Prop :=
  ∀ (Γ : Ctx N) (t : Term N) (τ τg : Ty) (n n' : Nat) (C : Equations Ty) (σ' : Subst Ty),
    HasVars.fresh Γ ≤ n → HasVars.fresh t ≤ n → HasVars.fresh τ ≤ n →
    HasTypeJ n Γ t τg C n' →
    HasType (HasSubst.pSubst Γ σ') (HasSubst.pSubst t σ') (HasSubst.pSubst τ σ') →
    ∃ σ'', Subst.Unifies σ'' ((τg, τ) :: C) ∧
      ∀ u : Ty, HasVars.fresh u ≤ n → HasSubst.pSubst u σ'' = HasSubst.pSubst u σ'

/-- **The one remaining obligation — completeness.** `none` only when nothing works. -/
def Complete : Prop :=
  ∀ (Γ : Ctx N) (hΓ : Γ.Ground) (t : Term N) (τ : Ty),
    (∃ σ, HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst t σ) (HasSubst.pSubst τ σ)) →
    (elaborate Γ hΓ t τ).isSome

end LambdaLab.Stlc.Named
