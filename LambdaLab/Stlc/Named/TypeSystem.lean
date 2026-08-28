import LambdaLab.Stlc.Named.Step.Confluence
import LambdaLab.Stlc.Named.Step.Eval
import LambdaLab.TypeSystem.Named.Basic
import LambdaLab.Stlc.Named.Alpha
import LambdaLab.Stlc.Named.Typing.Preservation
import LambdaLab.Stlc.Named.Typing.Normalization
import LambdaLab.Stlc.Named.Typing.Unification
import LambdaLab.Stlc.Named.Typing.JComplete
import LambdaLab.TypeSystem.Named.Vernacular.Elaborate

/-!
# STLC against the `TypeSystem` interface

The named STLC plugged into the classes of `TypeSystem/Named/Basic.lean`, as `Pipeline.lean` plugs it
into `Pipeline.Language`. Every field is an existing declaration under its own name; nothing is
proved here, which is the point — the interface asks for what the development already has.

## Every instance is generic in `N`

* `HasType` is **generic in `N`**. The typing judgement never inspects a name beyond equality and
  context lookup, so `Term N` is typeable for any atoms.
* `Step` is generic too — and this was not always so. It was declared at `Term String`, and that
  pinned `TypeSystem`, `LawfulTypeSystem`, `MVars` and `LawfulMVars` at `String` with it. The pin
  was never necessary: the β-rule's capture-avoiding substitution draws fresh names from
  `Atom.freshFor`, which every `Atom` instance has, and the de Bruijn translation carrying
  subject reduction only ever compares names. Generalising `Step`, `MStep`, `Translation` and
  `HasType.preservation` changed signatures and **not one proof**.
  That matters practically, not just aesthetically: `Pipeline.lean` names terms by `VName`, so
  with the instances pinned at `String` it could not use this interface at all and had to call
  `Target.elabSubst` directly. Now it goes through `PrincipalElaborate`.
* `MVars` needs no new work at all: `HasSubst Nat (Term N) Ty` and `HasSubst Nat Ty Ty` already exist, so
  both fields are `inferInstance` and the bundled copies are definitionally the canonical ones,
  which is what `MVars`' own docstring asks for.
* `LawfulMVars` is discharged by `HasType.subst`, which was proved generic in `N` long before the
  interface asked for it. Both laws the interface demands — subject reduction and stability under
  substitution — were already theorems here; neither needed a line of new proof.

* `HasAlphaEq` is **not** here, for the reason `instHasType` is not: it sits beside the relation
  it names, in `Stlc/Named/Alpha.lean`, so `≈α` reads from that file onwards. α-equality is
  equality of de Bruijn erasures, so the instance is `Translation.lean`'s work under a new name —
  once again the interface asking for what the development already had. `LawfulAlphaEq` *is* here,
  since its law mentions the judgement: α-equal terms type alike, by the same round trip.

* `PrincipalElaborate` is discharged by `elabMGU`. Its negative branch is
  `no_typing_of_elabSubst_none`, the one that took work: `none` has to mean *there is no typing*,
  not *this algorithm found none*. Its positive branch pairs `elabSubst_sound` with
  `elabSubst_principal_below`.

## Most-generality, and the shape it takes

`elaborate` returns a `PrincipalProp`, so filling it demands most-generality as well as the
decision. It is discharged by `Typing/JComplete.lean`'s **`elabSubst_principal_below`, a theorem** —
principality *on the source*, which is what the claim can be: the elaborator draws metavariables of
its own, and `Typing/Principality.lean` proves the unrestricted `MoreGeneral` form false for this
very elaborator. The threshold is `sourceSupp`, the same one `elabSubst` prunes to, handed to the
class through its own field.

Nothing in this file is claimed on credit any more, and nothing downstream reports `sorryAx`.

So the honest report is: STLC satisfies the metatheory unconditionally, decides elaboration
unconditionally (`elabSolution` is proved and still exported), and proves principality *on the
source* — the strongest form the unrestricted statement leaves available.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Nominal (Atom)

/-! ## The judgement — any atoms

`instHasType` is not here: it lives beside the inductive in `Typing/Basic.lean`, so that the `⊢`
notation the class owns is available from the judgement's own file onwards. -/

/-! ## Reduction and above — every atoms instance too

`Step` was declared at `Term String` and everything above it inherited the pin. It did not have
to be: `Term.subst` is capture-avoiding via `Atom.freshFor`, which every `Atom` instance
supplies, and the de Bruijn translation that carries subject reduction only ever compares names.
Generalising `Step`, `MStep`, `Translation` and `HasType.preservation` to an arbitrary `N` cost no
proof changes at all — only signatures — and it is what lets `Pipeline.lean` reach these instances
at its own name type `VName` instead of calling the elaborator directly.

`[HasVars Nat N]` appears from `LawfulTypeSystem` on: preservation needs it (through
`HasType.freeVars_in_ctx`), and the substitution the classes above it talk about is defined by it.
-/

variable {N : Type} [Atom N]

instance instTypeSystem : TypeSystem.Named.TypeSystem N (Term N) Ty := {}

/-- The metatheory field, discharged by the unconditional subject-reduction theorem. This is the
one instance with content: building it *is* the claim that STLC is well-behaved in the framework's
sense, since `Preservation` cannot be filled without a proof. -/
instance instLawfulTypeSystem : TypeSystem.Named.LawfulTypeSystem N (Term N) Ty where
  Preservation := HasType.preservation
  cong h ht := HasType.cong h ht

/-- Both substitution instances already exist, so fill from them rather than defining new ones —
the copies are then definitionally canonical and lemmas about either apply to both. -/
instance instMVars : TypeSystem.Named.MVars N (Term N) Ty where
  tmSubst := inferInstance
  tySubst := inferInstance

/-- The second instance with content: stability of typing under substitution, discharged by
`HasType.subst`. Like `Preservation` this is a field, so it cannot be skipped — and like it, the
proof already existed, generic in `N`, before the interface asked for it. -/
instance instLawfulMVars : TypeSystem.Named.LawfulMVars N (Term N) Ty where
  Stability σ h := HasType.subst h σ
  tyGroundStable := inferInstance
  tmGroundStable := inferInstance
  tyLawfulComp := inferInstance
  tmLawfulComp := inferInstance
  tyLawfulRestrict := inferInstance
  tmLawfulRestrict := inferInstance

/-- **The fourth instance with content**: α-equal terms type alike, discharged by
`Term.AlphaEq.hasType`. Like `Preservation` and `Stability` this is a field that cannot be skipped,
and like them the proof is the translation's, not new work — α-equality *is* equality of de Bruijn
erasures, so the law is `HasType.toDB` out and `HasType.fromDB` back.

`HasAlphaEq` itself is supplied in `Stlc/Named/Alpha.lean`, beside the relation; this is only the
law that ties it to the judgement. -/
instance instLawfulAlphaEq : TypeSystem.Named.LawfulAlphaEq N (Term N) Ty where
  typing_respects h ht := Term.AlphaEq.hasType h ht

/-! ## Groundness, decided

`PrincipalElaborate` asks for these, and they are the reason it does: `HasVars.Ground` quantifies
over every index, so no instance decides it by unfolding. Both were here long before the interface
wanted them. Declared ahead of the instance that consumes them. -/

/-- Groundness of a type, by the structural check — `Ty.ground_iff` routes it to `Ty.isGround`. -/
instance : DecidablePred (HasVars.Ground : Ty → Prop) :=
  fun _ => decidable_of_iff _ Ty.ground_iff

/-- The same for terms, via `Term.AnnotsGround`. -/
instance : DecidablePred (HasVars.Ground : Term N → Prop) :=
  fun _ => decidable_of_iff _ Term.annotsGround_iff_ground

/-- The third instance with content, and the first that is algorithmic rather than metatheoretic.
`elabMGU`'s negative branch is `no_typing_of_elabSubst_none` — a proof that nothing types the
triple, not a report that nothing was found — and its positive branch is `elabSubst_sound` paired
with `elabSubst_principal_below`. Both are theorems, so this instance is discharged in full.

`sourceSupp` is `Target.sourceSupp`, the threshold `elabSubst` prunes its answer to; the
principality the class asks for is stated below it, which is the only place it can hold
(`Typing/Principality.lean`). The plain decision remains available on its own as `elabSolution`. -/
instance instPrincipalElaborate : TypeSystem.Named.PrincipalElaborate N (Term N) Ty where
  sourceSupp := sourceSupp
  elaborate := elabMGU
  tyGroundDec := inferInstance
  tmGroundDec := inferInstance

/-! ## Normalization, and the rest of the reduction classes

All five are discharged, and — since the evaluation stage in `Pipeline/Stages/Evaluate.lean` needed
them — all five are now generic in `[Atom N]` like everything else here. They used to be pinned at
`String`, on the belief that the de Bruijn detour forced it. It did not: `Translation.lean` was
already generic and `Alpha.lean` mentions `String` only in a private example, so the pin lived
entirely in the four statements that carried it (`MStep.confluent`, `SN`, `HasType.sn`,
`Term.eval`) and lifting it was a matter of widening those binders. It had to be lifted: the
front end's name type is `Var stlcLanguage = VName`, not `String`, so a `String`-only evaluator is
one the pipeline cannot call. What each class cost:

* **`Confluent` is discharged**, up to `≈α`. It used to be unstateable: the class asked for a
  common reduct in `Tm` itself, and `Named.MStep.confluent` cannot give one — two reduction paths
  pick different fresh binder names, so they converge only up to α-equivalence, which is why that
  theorem states convergence *after* translation to de Bruijn. On-the-nose joining was not merely
  unproved here, it was false.

  What closed it, once the class joined its reducts up to `≈α`, was the direction `Translation.lean`
  never needed: `Term.step_reflect` lifts a de Bruijn step back to a named one (the erasure is
  shape-preserving, and the β case is `Term.toDB_subst` read right to left), `Term.mstep_reflect`
  iterates it, and `Term.alphaEq_of_toDB` turns the resulting agreement of erasures into `≈α`. All
  three are in `Stlc/Named/Alpha.lean`.

* **`HasEval` is `Step/Eval.lean`'s evaluator**, which already had the shape the class asks for:
  `HasType.eval` takes the derivation, not the bare term, so it is total with no error case to
  invent. Nothing had to be written for the data field.

* **`LawfulHasEval` is the one that needed new proofs**, and only two. `Term.eval_normalForm` and
  `Term.mstep_eval` follow the evaluator's own well-founded recursion, and both rest on
  `Term.findReductStep_ne_none` — the completeness of the redex picker, which is what makes "the
  loop stopped" mean "there was no redex" rather than "the picker missed one". All three are in
  `Step/Eval.lean`, beside the function they are about. -/

/-- **Strong normalization.** The field is `HasType.sn` outright — `Named.SN` *is* `LambdaLab.SN`
at this `Step`, so there is nothing to convert.

The field could not ask for well-foundedness of `⟶`: `omega_not_sn` refutes that. -/
instance instStronglyNormalizing :
    TypeSystem.Named.StronglyNormalizing N (Term N) Ty where
  StronglyNormalizing h := HasType.sn h

/-- **Confluence.**

The reducts are joined **up to `≈α`**, and they have to be: the β-rule renames binders out of the
way through `Atom.freshFor`, so two reduction paths from one term reach results that differ in
their bound names. Joining them on the nose is not merely unproved for this language, it is false.

The proof is `MStep.confluent` — which converges only after translation to de Bruijn — plus the two
halves that were missing until now, both in `Stlc/Named/Alpha.lean`: `Term.mstep_reflect` lifts each
de Bruijn reduction back to a named one, and `Term.alphaEq_of_toDB` turns the resulting agreement of
erasures into `≈α`. The context is `t.freeVars`, the smallest one `MStep.confluent` accepts, and
reduction never introduces a free variable (`MStep.preserves_freeVars`), so it stays adequate all
the way down. -/
instance instConfluent : TypeSystem.Named.Confluent N (Term N) Ty where
  Confluent {_Γ} {t t₁ t₂} {_τ} _ht h₁ h₂ := by
    obtain ⟨d, hd₁, hd₂⟩ := MStep.confluent t.freeVars (fun _ hw => hw) h₁ h₂
    have hfv1 : ∀ w ∈ t₁.freeVars, w ∈ t.freeVars := MStep.preserves_freeVars h₁
    have hfv2 : ∀ w ∈ t₂.freeVars, w ∈ t.freeVars := MStep.preserves_freeVars h₂
    obtain ⟨u₁, hs₁, he₁⟩ := Term.mstep_reflect hd₁ t₁ rfl hfv1
    obtain ⟨u₂, hs₂, he₂⟩ := Term.mstep_reflect hd₂ t₂ rfl hfv2
    refine ⟨u₁, u₂, hs₁, hs₂, ?_⟩
    exact Term.alphaEq_of_toDB
      (fun w hw => hfv1 w (MStep.preserves_freeVars hs₁ w hw))
      (fun w hw => hfv2 w (MStep.preserves_freeVars hs₂ w hw))
      (he₁.trans he₂.symm)

/-- **The normalizer.** `HasType.eval` is already derivation-indexed, so the field is filled
outright. -/
instance instHasEval : TypeSystem.Named.HasEval N (Term N) Ty where
  eval _Γ _e _τ ht := HasType.eval ht

/-- **The normalizer is one for real**: its answer admits no further reduction, and the input
reaches it. The two fields are `Term.eval_normalForm` and `Term.mstep_eval`, both proved beside
`Term.eval` itself.

The three parents are the instances above — `HasEval`, `StronglyNormalizing`, `Confluent` — so the
diamond the class documents is closed here by the elaborator, not by hand. -/
instance instLawfulHasEval : TypeSystem.Named.LawfulHasEval N (Term N) Ty where
  evalNormal ht := Term.eval_normalForm _ (HasType.sn ht)
  evalReachable ht := Term.mstep_eval _ (HasType.sn ht)
  evalGround ht hg :=
    Term.annotsGround_iff_ground.mp
      (Term.eval_annotsGround _ (HasType.sn ht) (Term.annotsGround_iff_ground.mpr hg))

/-! ## Substitution, for the stage that inlines definitions -/

/-- **The substitution lemma, from subject reduction.** β *is* substitution, so
`(λ x : σ . t) v` is a well-typed term whose one β-step is the substitution, and `Preservation`
carries the type across. No induction, no weakening lemma, no renaming lemma — this is the whole
proof. `weaken_closed` is the only extra step, moving the closed value into `Γ`. -/
theorem HasType.subst_typing {Γ : Ctx N} {x : N} {σ τ : Ty} {t v : Term N}
    (ht : HasType (Γ.cons x σ) t τ) (hv : HasType Ctx.empty v σ) :
    HasType Γ (t.subst x v) τ :=
  HasType.preservation (HasType.app (HasType.lam ht) (HasType.weaken_closed Γ hv)) Step.beta

/-- **Substituting into a closed term does nothing.** Both terms closed, so neither the variable
being replaced nor a capture-avoiding rename has anything to act on. -/
theorem HasType.subst_closed {x : N} {σ τ : Ty} {t v : Term N}
    (ht : HasType Ctx.empty t τ) (hv : HasType Ctx.empty v σ) : t.subst x v = t :=
  Term.subst_of_not_free
    (List.eq_nil_iff_forall_not_mem.mpr (HasType.closed_no_free hv)) t
    (HasType.closed_no_free ht x)

/-- **STLC substitutes terms for variables**, with the three laws the inlining stage asks of it —
two of which were already sitting here under other names. -/
instance instHasTermSubst : TypeSystem.Named.HasTermSubst N (Term N) Ty where
  tsubst t x v := t.subst x v
  tsubst_typing ht hv := HasType.subst_typing ht hv
  tsubst_ground hg hv :=
    Term.annotsGround_iff_ground.mp
      (Term.annotsGround_subst (Term.annotsGround_iff_ground.mpr hv) _
        (Term.annotsGround_iff_ground.mpr hg))
  tsubst_closed ht hv := HasType.subst_closed ht hv
  weaken_closed ht := HasType.weaken_closed _ ht

/-- **STLC elaborates and runs.** Nothing new to discharge: the class is the conjunction of two
instances already proved, and its only content is that they share a `LawfulMVars` — which they do,
since both are built from the same `instLawfulMVars`. -/
instance instRunnable : TypeSystem.Named.Runnable N (Term N) Ty :=
  { instPrincipalElaborate, instLawfulHasEval, instHasTermSubst with }

/-! ## The fields are definitionally what they came from

Each is `rfl`. They are stated so that a later change to the interface — reordering fields,
wrapping a component, adding a parameter — fails here, at the plug-in, rather than silently
rebinding one of STLC's notions to something else. -/

@[simp] theorem hasType_eq :
    TypeSystem.Named.HasType.HasType (N := N) (Tm := Term N) (Ty := Ty) = HasType := rfl

@[simp] theorem step_eq : TypeSystem.Named.Step.Step (Tm := Term N) = Step := rfl

@[simp] theorem eval_eq {Γ : Ctx N} {e : Term N} {τ : Ty} (ht : Γ ⊢ e : τ) :
    TypeSystem.Named.HasEval.eval Γ e τ ht = HasType.eval ht := rfl

@[simp] theorem elaborate_eq :
    TypeSystem.Named.PrincipalElaborate.elaborate (N := N) (Tm := Term N) (Ty := Ty)
      = elabMGU := rfl

/-! ## Beyond the interface

STLC satisfies strictly more than `LawfulTypeSystem` asks. Recorded next to the instance so the
gap is documented where someone comparing the two will look — `TypeSystem/Named/Basic.lean` argues at
length for keeping normalization *out* of the interface, and that argument reads better with the
thing it excludes in view. -/

/-- STLC is strongly normalizing — a property the interface does not require. -/
theorem sn_of_hasType {Γ : Ctx N} {e : Term N} {τ : Ty} :
    Γ ⊢ e : τ → SN e :=
  HasType.sn

end LambdaLab.Stlc.Named
