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

/-! ## The typing bridge

Two vocabulary adapters, then the instance. The bridge states de Bruijn lookup as `Δ[i]?` (the
de Bruijn tower's spelling); `Translation.lean` states it as the `Lookup` inductive with
`lookupVar` computing the index. The adapters say these are the same facts. -/

/-- The bridge's index function is `Translation.lean`'s, clause for clause. -/
theorem scopeIdx_eq_lookupVar (x : N) : ∀ l : List N, scopeIdx x l = lookupVar x l
  | [] => rfl
  | y :: ys => by simp [scopeIdx, lookupVar, scopeIdx_eq_lookupVar x ys]

/-- The `Lookup` inductive is positional `getElem?`. -/
theorem lookup_iff_getElem? {Δ : Stlc.DeBruijn.Ctx} {n : Nat} {τ : Stlc.DeBruijn.Ty} :
    Stlc.DeBruijn.Lookup Δ n τ ↔ Δ[n]? = some τ := by
  constructor
  · intro h
    induction h with
    | here => rfl
    | there _ ih => simpa using ih
  · intro h
    induction Δ generalizing n with
    | nil => simp at h
    | cons τ' Δ ih =>
        cases n with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at h
            exact h ▸ .here
        | succ n =>
            simp only [List.getElem?_cons_succ] at h
            exact .there (ih h)

/-- The bridge's compatibility is `Translation.lean`'s `CtxCompat`, through the adapters. -/
theorem ctxCompat_iff {Γ : Ctx N} {binders : List N} {Δ : Stlc.DeBruijn.Ctx} :
    TypeSystem.Bridge.CtxCompat Ty.toDB Γ binders Δ ↔ CtxCompat Γ binders Δ := by
  constructor <;> intro h x hx <;> obtain ⟨τ, h1, h2⟩ := h x hx <;> refine ⟨τ, h1, ?_⟩
  · rw [← scopeIdx_eq_lookupVar]
    exact lookup_iff_getElem?.mpr h2
  · rw [scopeIdx_eq_lookupVar]
    exact lookup_iff_getElem?.mp h2

instance : HasEraseTy Ty Stlc.DeBruijn.Ty where
  eraseTy := Ty.toDB

/-- The typing bridge: both laws are `Translation.lean`'s theorems, through the adapters —
reflection recovering the on-the-nose type by `Ty.fromDB_toDB`. -/
instance instTypingBridge :
    TypingBridge N (Term N) Ty Stlc.DeBruijn.Term Stlc.DeBruijn.Ty :=
  { instStepBridge with
    eraseTy := Ty.toDB
    erase_typing := fun binders Δ hc hcompat ht =>
      HasType.toDB _ ht binders Δ hc (ctxCompat_iff.mp hcompat)
    erase_typing_reflect := fun binders Δ hc hcompat hdb => by
      have h := HasType.fromDB _ binders Δ _ hc (ctxCompat_iff.mp hcompat) hdb
      rwa [Ty.fromDB_toDB] at h
    typing_covers := fun ht x hx => HasType.freeVars_in_ctx _ ht x hx }

/-- The reflection bridge: both laws are `Alpha.lean`'s theorems — `Term.step_reflect` lifts a
de Bruijn step, `Term.alphaEq_of_toDB` lifts a one-scope agreement to `Term.AlphaEq`, which *is*
`ErasureEq` (`alphaEq_iff_erasureEq`), so the inlined conclusion is met on the nose. -/
instance instReflectBridge : ReflectBridge N (Term N) Stlc.DeBruijn.Term :=
  { instStepBridge with
    step_reflect := fun Γ hc hs =>
      let ⟨u, hu, he⟩ := Term.step_reflect _ Γ _ hc hs
      ⟨u, RTC.single hu, he⟩
    erasureEq_of_agree := fun hct hcu heq => Term.alphaEq_of_toDB hct hcu heq }

end LambdaLab.Stlc.Named
