import LambdaLab.Stlc.Named.Translation
import LambdaLab.Stlc.Named.Alpha
import LambdaLab.Stlc.DeBruijn.TypeSystem
import LambdaLab.TypeSystem.Bridge

/-!
# STLC instantiates the bridge

The named STLC and its de Bruijn reference, related through `TypeSystem/Bridge.lean`'s
interface. Every field is a theorem `Translation.lean` already carries — `Step.toDB_pos` *is*
`erase_step_pos`, `Step.preserves_freeVars` *is* `preserves_freeVars` — which is the point: the
bridge is the shape those proofs always had, stated once.

The corollaries below re-derive by generic transport what the named side proves by hand:
`sn_fromDB'` is `SN.fromDB` from `StepBridge.sn_of_erase`, and `Term.AlphaEq` agrees with the
bridge-induced `ErasureEq` *by `Iff.rfl`* — the named α-equality was the induced one all along.
Retiring the hand proofs in favour of these is deliberate later work; today the two live side by
side as the check that the interface loses nothing.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Nominal (Atom)
open LambdaLab.TypeSystem.Bridge

variable {N : Type} [Atom N]

instance : HasFreeVars N (Term N) where
  freeVars := Term.freeVars

instance : HasErase N (Term N) Stlc.DeBruijn.Term where
  erase t Γ := t.toDB Γ

/-- The reduction bridge: both laws are `Translation.lean`'s theorems, verbatim. -/
instance instStepBridge : StepBridge N (Term N) Stlc.DeBruijn.Term where
  erase_step_pos Γ hc s := Step.toDB_pos Γ hc s
  preserves_freeVars s x hx := Step.preserves_freeVars s x hx

/-- `SN.fromDB`, re-derived from the generic transfer: the de Bruijn `SN` converts to the
relational one and reflects along erasure. -/
theorem sn_fromDB' (e : Term N) (Γ : List N) (hc : ∀ x ∈ e.freeVars, x ∈ Γ)
    (hsn : Stlc.DeBruijn.SN (e.toDB Γ)) : SN (· ⟶ ·) e :=
  StepBridge.sn_of_erase Γ (fun x hx => hc x hx) hsn.toRelation

/-- **The named α-equality is the bridge-induced one — definitionally.** `Term.AlphaEq`'s two
conjuncts are `ErasureEq`'s two conjuncts; nothing to prove, and that is the adequacy claim in
its cheapest possible form. -/
theorem alphaEq_iff_erasureEq {t u : Term N} :
    t.AlphaEq u ↔ ErasureEq Stlc.DeBruijn.Term (N := N) t u :=
  Iff.rfl

end LambdaLab.Stlc.Named
