import LambdaLab.Stlc.DeBruijn.Unification
import LambdaLab.Stlc.DeBruijn.Preservation
import LambdaLab.Stlc.DeBruijn.Confluence
import LambdaLab.Stlc.DeBruijn.Eval
import LambdaLab.Stlc.DeBruijn.Reducibility
import LambdaLab.TypeSystem.DeBruijn.Basic

/-!
# The de Bruijn STLC instantiates the de Bruijn tower

The mirror of `Stlc/Named/TypeSystem.lean`: the same calculus claims the same interface, on the
other side of the naming divide. The purpose is the one `TypeSystem/DeBruijn/Basic.lean` states —
this tower hosts metatheory and audits the named formalization — so the instances here are the
*reference* readings of the properties the named side claims through translation.

What discharges immediately is the metatheory this side always owned: preservation
(`HasType.preservation`), confluence on the nose (`MStep.confluent` — no `≈α` anywhere),
strong normalization (`HasType.sn`, through the reducibility candidates), and the normalizer
(`HasType.eval`). What is `sorry` is the frontier: stability of typing under type-substitution,
the term-side substitution mixins, the two `eval` laws (`Term.eval` was defined here long before
anything asked what its answer *means*), and the `tsubst` laws — each a de Bruijn-native proof to
be written, not a translation.

`PrincipalElaborate` and `Runnable` are deliberately not claimed: there is no de Bruijn
elaborator yet. The seat stays warm — the classes exist, per the tower's opt-in doctrine — for
the day elaboration's metatheory earns its own detour (dependent types are the expected
trigger). -/

namespace LambdaLab.Stlc.DeBruijn

/-- The judgement, as the tower's one field. `Ctx` *is* `TypeSystem.DeBruijn.Context Ty` — both
are `List Ty` — so nothing is translated, only claimed. -/
instance instHasType : TypeSystem.DeBruijn.HasType Term Ty where
  HasType := HasType

/-- Judgement and reduction together — `Step.lean`'s `instStep` supplies the reduction half. -/
instance instTypeSystem : TypeSystem.DeBruijn.TypeSystem Term Ty := {}

/-- Preservation, discharged by the proof that predates the interface. -/
instance instLawfulTypeSystem : TypeSystem.DeBruijn.LawfulTypeSystem Term Ty where
  Preservation := HasType.preservation

/-- Both substitution instances exist (`Unification.lean`), so fill from them. -/
instance instMVars : TypeSystem.DeBruijn.MVars Term Ty where
  tmSubst := inferInstance
  tySubst := inferInstance

/-- Stability of typing under type-substitution, and the term-side mixins: the frontier. The
type-side mixins come from the `Signature` machinery, as the named ones do. -/
instance instLawfulMVars : TypeSystem.DeBruijn.LawfulMVars Term Ty where
  Stability := sorry
  tyGroundStable := inferInstance
  tmGroundStable := sorry
  tyLawfulComp := inferInstance
  tmLawfulComp := sorry
  tyLawfulRestrict := inferInstance
  tmLawfulRestrict := sorry

/-- `Reducibility.lean`'s `SN` and `Relation/Normalization.lean`'s are the same inductive shape
at this `Step`; this is the conversion, by the one induction available. -/
theorem SN.toRelation : ∀ {e : Term}, SN e → LambdaLab.SN (· ⟶ ·) e := by
  intro e h
  induction h with
  | intro _ ih => exact LambdaLab.SN.intro (fun e' hs => ih e' hs)

/-- Strong normalization: the reducibility-candidates theorem, converted. -/
instance instStronglyNormalizing : TypeSystem.DeBruijn.StronglyNormalizing Term Ty where
  StronglyNormalizing h := (HasType.sn h).toRelation

/-- Confluence **on the nose** — the whole point of this side. The typing hypothesis is unused,
as the tower's docstring anticipates for a system whose confluence never needed it. -/
instance instConfluent : TypeSystem.DeBruijn.Confluent Term Ty where
  Confluent _ h₁ h₂ := MStep.confluent h₁ h₂

/-- The normalizer: recursion on `SN`, total on well-typed terms. -/
instance instHasEval : TypeSystem.DeBruijn.HasEval Term Ty where
  eval _ _ _ h := HasType.eval h

/-- The two `eval` laws and groundness: the frontier. `Term.eval` was defined long before
anything asked whether its answer is normal or reachable; the named side proved both for *its*
eval (`Term.eval_normalForm`, `Term.mstep_eval`), and these are their de Bruijn-native
counterparts, to be proved beside `Term.eval` where they belong. -/
instance instLawfulHasEval : TypeSystem.DeBruijn.LawfulHasEval Term Ty where
  evalNormal := sorry
  evalReachable := sorry
  evalGround := sorry

/-- Term-for-variable substitution at index `0`, with its laws: the frontier. The operation is
`Basic.lean`'s `subst`; the typing law is `HasType.subst_lemma` specialized to the head binder;
the rest are de Bruijn-native statements the named side needed `Atom.freshFor` gymnastics for. -/
instance instHasTermSubst : TypeSystem.DeBruijn.HasTermSubst Term Ty where
  tsubst t v := t.subst 0 v
  tsubst_typing := sorry
  tsubst_ground := sorry
  tsubst_closed := sorry
  weaken_closed := sorry

end LambdaLab.Stlc.DeBruijn
