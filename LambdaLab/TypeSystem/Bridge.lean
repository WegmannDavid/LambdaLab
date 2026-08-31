import LambdaLab.TypeSystem.Named.Basic
import LambdaLab.TypeSystem.DeBruijn.Basic

/-!
# The bridge — named and de Bruijn, related by erasure, one obligation per class

The generic interface for the division of labour the two STLCs practice concretely: metatheory is
*proved* where binding is positional and *used* where the pipeline runs. `Stlc/Named/Translation.lean`
is one instance of this file's classes; the transport theorems here are the generalizations of the
proofs that file and `Typing/Normalization.lean` carry by hand, proved once against the interface
so the next calculus writes one translation and inherits its named metatheory.

**The compiler never sees this file.** The bridge is formalization apparatus — the audit relating
a named system to its de Bruijn reference — and nothing in `Pipeline/` imports it; the front end
operates purely in the named realm. That is also why it is *not* an `Abs` morphism, though erasure
is lossy and its fibers are α-classes: `realize`/`default` are printer vocabulary, `OneCell`
composes into pipelines, and the one thing the bridge must never be is a stage.

## The shape: erasure is scope-relative

`erase t Γ` reads a term under an *enumeration of its scope* — the de Bruijn index of a variable
is its position in `Γ` — so every law carries the covering hypothesis `∀ x ∈ freeVars t, x ∈ Γ`.
`freeVars` is data of the bridge, not of the named tower: it is exactly the syntax-description the
tower's `HasAlphaEq` docstring promises never to demand, surrendered here, once, where describing
the syntax is the entire point.

## What transports, and at what strength

* `erase_mstep` — reduction sequences erase (steps may collapse only in number, never to zero:
  `erase_step_pos` demands a *positive* image, which is what the SN transfer consumes).
* `sn_of_erase` — **strong normalization reflects**: an SN erasure has an SN source, the
  generalization of `SN.fromDB`. This is the generator-level fact no equivalence of categories
  sees; it lives here.
* `confluent_erase` — two named reduction paths join *after erasure*, from de Bruijn confluence.
* `ErasureEq` — the induced α-equality: same free variables, same erasure under every covering
  scope. An equivalence by construction, and `HasAlphaEq`-shaped (`erasureAlphaEq`, a `def` and
  not an instance, as `HasAlphaEq.ofEq` is and for its reason).

Still to come, in later units: erasure of types and contexts with typing transported both ways,
the `eval` commutation theorem, the reflection law (`step_reflect` generalized) with named
confluence-up-to-`≈α` derived, and — the stated destination — the syntactic categories with the
bridge as an equivalence between them, where subobjects await.
-/

namespace LambdaLab.TypeSystem.Bridge

open LambdaLab.TypeSystem.Named (Step)

/-- **The named side's scoping data**: which names a term mentions freely. The one piece of
syntax-description the bridge asks of a language. -/
class HasFreeVars (N Tm : Type) where
  /-- The free variables, as the list the covering hypotheses quantify over. -/
  freeVars : Tm → List N

/-- **The erasure**: a term read under an enumeration of its scope — a variable's index is its
position in `Γ`. Data only; the laws live in `StepBridge` and above. -/
class HasErase (N Tm Tm' : Type) where
  /-- Erase under the scope `Γ`. Total — the covering hypothesis travels in the laws, as
  `Term.toDB`'s side conditions do. -/
  erase : Tm → List N → Tm'

/-- `Γ` covers `t`: every free variable is enumerated. The hypothesis every bridge law carries. -/
def Covers {N Tm : Type} [HasFreeVars N Tm] (Γ : List N) (t : Tm) : Prop :=
  ∀ x ∈ HasFreeVars.freeVars t, x ∈ Γ

/-- **The reduction bridge**: named steps erase to *positive* de Bruijn reductions, and
reduction never invents a free variable.

Positivity is load-bearing: a named step may erase to *several* de Bruijn steps (a β under a
binder that also renames), but never to none — else an infinite named reduction could erase to a
stationary point and the SN transfer below would be false. The named side's `Step.toDB_pos` is
the concrete form. -/
class StepBridge (N Tm Tm' : Type) [Step Tm] [Step Tm']
    extends HasFreeVars N Tm, HasErase N Tm Tm' where
  /-- A step erases to at least one step: one now, the rest after. -/
  erase_step_pos : ∀ {t t' : Tm} (Γ : List N), (∀ x ∈ freeVars t, x ∈ Γ) → t ⟶ t' →
    ∃ d : Tm', erase t Γ ⟶ d ∧ d ⟶* erase t' Γ
  /-- Reduction never invents a free variable, so a covering scope keeps covering. -/
  preserves_freeVars : ∀ {t t' : Tm}, t ⟶ t' → ∀ x ∈ freeVars t', x ∈ freeVars t

namespace StepBridge

open HasFreeVars HasErase

variable {N Tm Tm' : Type} [Step Tm] [Step Tm'] [StepBridge N Tm Tm']

/-- A covering scope survives a step. -/
theorem covers_step {t t' : Tm} {Γ : List N} (hc : Covers Γ t) (s : t ⟶ t') : Covers Γ t' :=
  fun x hx => hc x (preserves_freeVars (Tm' := Tm') s x hx)

/-- …and a whole reduction sequence. -/
theorem covers_mstep {t t' : Tm} {Γ : List N} (hc : Covers Γ t) (hs : t ⟶* t') : Covers Γ t' := by
  induction hs with
  | refl => exact hc
  | tail _ s ih => exact covers_step (Tm' := Tm') ih s

/-- **Reduction sequences erase**: `erase_step_pos` folded along `⟶*`. -/
theorem erase_mstep {t t' : Tm} (Γ : List N) (hc : Covers Γ t) (hs : t ⟶* t') :
    erase (N := N) t Γ ⟶* (erase t' Γ : Tm') := by
  induction hs with
  | refl => exact RTC.refl
  | tail hs' s ih =>
      obtain ⟨d, hd, hrest⟩ := erase_step_pos Γ (covers_mstep hc hs') s
      exact ih.trans (RTC.head hd hrest)

/-- The workhorse of the SN transfer: induct on the de Bruijn `SN` with a motive closed under
`⟶*`, so a single named step — whose erasure may take several de Bruijn steps — can be advanced
through the trace. The generalization of `SN.fromDB_aux`, proved once. -/
private theorem sn_of_erase_aux :
    ∀ {d : Tm'}, SN (· ⟶ ·) d →
      ∀ (t : Tm) (Γ : List N), Covers Γ t → d ⟶* erase t Γ → SN (· ⟶ ·) t := by
  intro d hsn
  induction hsn with
  | intro _ ih =>
      intro t Γ hc hms
      apply SN.intro
      intro t' s
      have hc' : Covers Γ t' := covers_step (Tm' := Tm') hc s
      obtain ⟨dmid, hd1, hd2⟩ := erase_step_pos Γ hc s
      rcases RTC.cases_head hms with heq | ⟨c, hcstep, hrest⟩
      · exact ih dmid (heq ▸ hd1) t' Γ hc' hd2
      · exact ih c hcstep t' Γ hc' (hrest.trans (RTC.head hd1 hd2))

/-- **Strong normalization reflects along erasure** — the bridge's crown, and the theorem that
justifies proving SN by reducibility candidates once, on the positional side. -/
theorem sn_of_erase {t : Tm} (Γ : List N) (hc : Covers Γ t)
    (hsn : SN (· ⟶ ·) (erase (N := N) t Γ : Tm')) : SN (· ⟶ ·) t :=
  sn_of_erase_aux hsn t Γ hc RTC.refl

/-- **Named reduction is confluent after erasure**: two named paths from one term join in the
de Bruijn image, given de Bruijn confluence. The joined-in-the-image form the named STLC states
concretely as `MStep.confluent`; the up-to-`≈α` form on the named side needs step *reflection*,
which is a later unit's law. -/
theorem confluent_erase
    (hconf : ∀ {d d₁ d₂ : Tm'}, d ⟶* d₁ → d ⟶* d₂ → ∃ e, d₁ ⟶* e ∧ d₂ ⟶* e)
    {t t₁ t₂ : Tm} (Γ : List N) (hc : Covers Γ t) (h₁ : t ⟶* t₁) (h₂ : t ⟶* t₂) :
    ∃ d : Tm', erase (N := N) t₁ Γ ⟶* d ∧ erase t₂ Γ ⟶* d :=
  hconf (erase_mstep Γ hc h₁) (erase_mstep Γ hc h₂)

end StepBridge

/-! ## The induced α-equality

Two terms are the same term when nothing but their names distinguishes them — same free
variables, same erasure under every covering scope. The two-conjunct shape is
`Stlc/Named/Alpha.lean`'s, abstracted: the free-variable conjunct is what makes the relation
usable without fixing a scope. -/

/-- The bridge-induced α-equality. -/
def ErasureEq (Tm' : Type) {N Tm : Type} [HasFreeVars N Tm] [HasErase N Tm Tm']
    (t u : Tm) : Prop :=
  HasFreeVars.freeVars (N := N) t = HasFreeVars.freeVars u ∧
    ∀ Γ : List N, Covers Γ t → HasErase.erase t Γ = (HasErase.erase u Γ : Tm')

namespace ErasureEq

variable {N Tm Tm' : Type} [HasFreeVars N Tm] [HasErase N Tm Tm']

theorem refl (t : Tm) : ErasureEq Tm' (N := N) t t := ⟨rfl, fun _ _ => rfl⟩

theorem symm {t u : Tm} (h : ErasureEq Tm' (N := N) t u) : ErasureEq Tm' (N := N) u t :=
  ⟨h.1.symm, fun Γ hc => (h.2 Γ (fun x hx => hc x (h.1 ▸ hx))).symm⟩

theorem trans {t u v : Tm} (h₁ : ErasureEq Tm' (N := N) t u) (h₂ : ErasureEq Tm' (N := N) u v) :
    ErasureEq Tm' (N := N) t v :=
  ⟨h₁.1.trans h₂.1, fun Γ hc => (h₁.2 Γ hc).trans (h₂.2 Γ (fun x hx => hc x (h₁.1 ▸ hx)))⟩

end ErasureEq

/-- The induced α-equality, packaged for the named tower's `HasAlphaEq` slot. A `def`, not an
instance, exactly as `HasAlphaEq.ofEq` is and for its reason: a blanket instance would match
every `Tm` and displace the language's own. A language with a bridge opts in by naming it — and
then its `≈α` is *derived* from its binding structure rather than asserted beside it. -/
@[reducible] def erasureAlphaEq (N Tm Tm' : Type) [HasFreeVars N Tm] [HasErase N Tm Tm'] :
    Named.HasAlphaEq Tm where
  AlphaEq := ErasureEq Tm' (N := N)
  refl := ErasureEq.refl
  symm := ErasureEq.symm
  trans := ErasureEq.trans

/-! ## The typing bridge

A named context is a map, a de Bruijn context is a list, and the enumeration `binders` is the
choice that relates them: a name's index is its position, its type erases to that position's
entry. `CtxCompat` is that relation; the two laws say the judgement transports both ways over
it. Reflection is stated *at erased types* — no inverse of `eraseTy` is demanded; a language
with an iso (as STLC has `Ty.fromDB`) recovers the stronger form by rewriting.

Both towers' turnstiles are global and both fire below; the type of the context picks the
reading, which is what the two towers' notation design promised. -/

section Typing

open LambdaLab.Nominal (Atom)

/-- **Type erasure**: data only, as `HasErase` is. -/
class HasEraseTy (Ty Ty' : Type) where
  /-- Erase a type. Total — types carry no binders in the towers this bridges. -/
  eraseTy : Ty → Ty'

variable {N Tm Ty Tm' Ty' : Type}

/-- A name's de Bruijn index: its position in the scope enumeration. The definition matches the
concrete `lookupVar` clause for clause, so instances adapt by `rfl`-adjacent lemmas. -/
def scopeIdx [Atom N] (x : N) : List N → Nat
  | [] => 0
  | y :: ys => if y = x then 0 else scopeIdx x ys + 1

/-- **Context compatibility**: every enumerated name is bound, and its erased type sits at its
index. `eraseTy` is passed as a function rather than found as an instance, so the definition is
usable inside the class below, where the instance is the parent under construction. -/
def CtxCompat [Atom N] (eraseTy : Ty → Ty') (Γ : Named.Context N Ty) (binders : List N)
    (Δ : DeBruijn.Context Ty') : Prop :=
  ∀ x ∈ binders, ∃ τ : Ty, Γ.get? x = some τ ∧ Δ[scopeIdx x binders]? = some (eraseTy τ)

/-- Compatibility extends under a binder: the new name at index `0`, everything else shifted —
by `cons` on all three components at once. -/
theorem CtxCompat.cons [Atom N] {eraseTy : Ty → Ty'} {Γ : Named.Context N Ty}
    {binders : List N} {Δ : DeBruijn.Context Ty'} (x : N) (τ : Ty)
    (h : CtxCompat eraseTy Γ binders Δ) :
    CtxCompat eraseTy (Γ.cons x τ) (x :: binders) (eraseTy τ :: Δ) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    refine ⟨τ, ?_, ?_⟩
    · rw [Named.Context.get?_cons, if_pos rfl]
    · show (eraseTy τ :: Δ)[scopeIdx y (y :: binders)]? = some (eraseTy τ)
      rw [show scopeIdx y (y :: binders) = 0 from by simp [scopeIdx]]
      rfl
  · obtain ⟨τ', hget, hidx⟩ :=
      h y ((List.mem_cons.mp hy).resolve_left hyx)
    have hxy : ¬ x = y := fun h => hyx h.symm
    refine ⟨τ', ?_, ?_⟩
    · rw [Named.Context.get?_cons, if_neg hxy]
      exact hget
    · show (eraseTy τ :: Δ)[scopeIdx y (x :: binders)]? = some (eraseTy τ')
      rw [show scopeIdx y (x :: binders) = scopeIdx y binders + 1 from by
        simp [scopeIdx, hxy]]
      simpa using hidx

/-- **The typing bridge**: the judgement transports both ways over a compatible context triple.
Extends `StepBridge` rather than standing beside it, so a consumer holding both sees one
erasure — the diamond lesson, applied preemptively. -/
class TypingBridge (N Tm Ty Tm' Ty' : Type) [Atom N] [Step Tm] [Step Tm']
    [Named.HasType N Tm Ty] [DeBruijn.HasType Tm' Ty']
    extends StepBridge N Tm Tm', HasEraseTy Ty Ty' where
  /-- Typing is preserved by erasure. -/
  erase_typing : ∀ {Γ : Named.Context N Ty} {t : Tm} {τ : Ty}
      (binders : List N) (Δ : DeBruijn.Context Ty'),
      (∀ x ∈ freeVars t, x ∈ binders) → CtxCompat eraseTy Γ binders Δ →
      Γ ⊢ t : τ → Δ ⊢ erase t binders : eraseTy τ
  /-- …and reflected, at erased types. -/
  erase_typing_reflect : ∀ {Γ : Named.Context N Ty} {t : Tm} {τ : Ty}
      (binders : List N) (Δ : DeBruijn.Context Ty'),
      (∀ x ∈ freeVars t, x ∈ binders) → CtxCompat eraseTy Γ binders Δ →
      Δ ⊢ erase t binders : eraseTy τ → Γ ⊢ t : τ

/-- **Preservation transports**: a named reduct keeps its type because its *erasure* does —
erase the typing, run de Bruijn preservation along the erased steps, reflect. The route
`Stlc/Named/Typing/Preservation.lean` takes concretely, proved once; the named side's whole
subject-reduction obligation shrinks to choosing an enumeration. -/
theorem preservation_via_erase [Atom N] [Step Tm]
    [Named.HasType N Tm Ty] [DeBruijn.LawfulTypeSystem Tm' Ty']
    [TypingBridge N Tm Ty Tm' Ty']
    {Γ : Named.Context N Ty} {t t' : Tm} {τ : Ty}
    (binders : List N) (Δ : DeBruijn.Context Ty')
    (hc : ∀ x ∈ HasFreeVars.freeVars t, x ∈ binders)
    (hcompat : CtxCompat (HasEraseTy.eraseTy (Ty' := Ty')) Γ binders Δ)
    (ht : Γ ⊢ t : τ) (hs : t ⟶ t') : Γ ⊢ t' : τ := by
  have hdb := TypingBridge.erase_typing binders Δ hc hcompat ht
  obtain ⟨d, hd1, hd2⟩ := StepBridge.erase_step_pos binders hc hs
  have hms : HasErase.erase t binders ⟶* (HasErase.erase t' binders : Tm') :=
    RTC.head hd1 hd2
  have hdb' := DeBruijn.preservation_mstep hdb hms
  exact TypingBridge.erase_typing_reflect binders Δ
    (StepBridge.covers_step (fun x hx => hc x hx) hs) hcompat hdb'

end Typing

end LambdaLab.TypeSystem.Bridge
