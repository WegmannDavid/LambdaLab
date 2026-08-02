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

open LambdaLab.Language (NameAlphabet)

variable {N : Type} [NameAlphabet N] [HasVars N]

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

/-- **The algorithm.** Generate every constraint, then solve once — with the *declared* type
thrown in as one more equation, which is how a synthesising generator handles a checking problem.

`Option`, because not every triple is elaborable and no substitution can repair that: in
`(λ x : ⋆ . x) (λ y : ⋆ . y)` the annotations are ground, so σ cannot touch them, and the
argument's `⋆ → ⋆` never matches the parameter's `⋆`. A total version is uninhabited.

Built from `J`, not `W`. W's answer is a composition of substitutions accumulated during the
traversal, so its most-generality is entangled with the freshness discipline. J's answer is
*literally* `unify`'s output, so the second conjunct reduces through `unify_mgu` to a statement
about generation alone. -/
def elaborate (Γ : Ctx N) (hΓ : Γ.Ground) (t : Term N) (τ : Ty) :
    Option (elaborationResult Γ t τ) :=
  match hg : gen Γ t (sourceFresh Γ t τ) with
  | none => none
  | some r =>
      match hu : unify ((r.1, τ) :: r.2.1) with
      | none => none
      | some σ =>
          some ⟨σ,
            -- the typing conjunct: `gen_correct` to the judgement, `sound` for the work, and the
            -- head equation rewrites the synthesised type into the declared one
            by
              have hall : Subst.Unifies σ ((r.1, τ) :: r.2.1) := unify_unifies _ σ hu
              have hsound := (gen_correct t Γ _ r.1 r.2.1 r.2.2 hg).sound
                (fun q hq => hall q (List.mem_cons_of_mem _ hq))
              have hhead : HasSubst.pSubst r.1 σ = HasSubst.pSubst τ σ :=
                hall _ List.mem_cons_self
              rwa [hhead] at hsound,
            -- the most-generality conjunct: `unify_mgu` reduces this to `GenerationComplete`
            -- below, which is the only thing still missing
            by sorry⟩

/-- **The one missing lemma**, and the whole of what stands between `elaborate` and being done.

`unify_mgu` already says the computed σ is most general among *unifiers of the constraints*. To
turn that into most general among *typings*, one needs the converse of `HasTypeJ.sound`: every
substitution that types the triple satisfies the generated constraints.

It cannot be σ' itself — the constraints mention the variables `gen` drew, about which σ' says
nothing — so the statement produces an extension agreeing with σ' on everything below the starting
supply. Proving it is an induction on the `HasTypeJ` derivation, needing a bound on which variables
the constraints mention (the analogue of `HasTypeJ.supply_le`) and a lemma that substitutions
agreeing below `n` act alike on types whose variables are below `n`. -/
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
