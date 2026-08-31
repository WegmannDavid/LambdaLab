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

Above the reduction layer: `TypingBridge` transports the judgement both ways over compatible
context triples, `typing_covers` plus the canonical enumeration (`canonScope`/`canonCtx`) make
the transports *unconditional* — `preservation_of_bridge`, `stronglyNormalizing_of_bridge`,
`typing_respects_of_bridge` take a bare typing and nothing else — and `ReflectBridge` carries
reduction back up, yielding `confluent_of_bridge`: named confluence up to the induced `≈α`,
from de Bruijn confluence. With those, everything that is transport material — the reduction
metatheory — flows from a bridge instance; what stays language-native is data (`eval`,
`tsubst`, elaboration), metavariable algebra, and representation trivia, by design.

Still to come: the `eval` commutation theorem (certifying a native normalizer against the
reference), and the categorical capstone (`Bridged.lean` has the category; the localization
statement awaits).
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

/-! ## The reflection bridge — the upward direction

`StepBridge` carries reduction down; this carries it back up, and it is what named confluence
was waiting for: de Bruijn confluence joins the *erasures*, and reflection is what turns the
joined trace into named reducts. Its second law lifts a single-scope agreement of erasures to
the full induced α-equality — the abstraction of `Term.alphaEq_of_toDB`, whose conclusion is
inlined because `ErasureEq` is instance-parameterized and the instance here is the parent under
construction (the `CtxCompat` lesson, again). -/

/-- **The upward laws**: a de Bruijn step out of an erasure lifts to a named reduction with the
matching erasure, and erasure-agreement at one covering scope is α at every one. -/
class ReflectBridge (N Tm Tm' : Type) [Step Tm] [Step Tm']
    extends StepBridge N Tm Tm' where
  /-- A step of the image is the shadow of a reduction of the source. -/
  step_reflect : ∀ {t : Tm} {d : Tm'} (Γ : List N), (∀ x ∈ freeVars t, x ∈ Γ) →
    (erase t Γ ⟶ d) → ∃ t' : Tm, t ⟶* t' ∧ erase t' Γ = d
  /-- One covering scope's agreement is every covering scope's — `ErasureEq`, inlined. -/
  erasureEq_of_agree : ∀ {t u : Tm} {Γ : List N},
    (∀ x ∈ freeVars t, x ∈ Γ) → (∀ x ∈ freeVars u, x ∈ Γ) → erase t Γ = erase u Γ →
    freeVars t = freeVars u ∧
      ∀ Γ' : List N, (∀ x ∈ freeVars t, x ∈ Γ') → erase t Γ' = erase u Γ'

namespace ReflectBridge

open HasFreeVars HasErase StepBridge

variable {N Tm Tm' : Type} [Step Tm] [Step Tm'] [ReflectBridge N Tm Tm']

/-- The packaged form of `erasureEq_of_agree`, once the instances exist to state it. -/
theorem erasureEq_of_agree' {t u : Tm} {Γ : List N}
    (hct : Covers Γ t) (hcu : Covers Γ u) (h : erase (N := N) t Γ = (erase u Γ : Tm')) :
    ErasureEq Tm' (N := N) t u :=
  erasureEq_of_agree hct hcu h

/-- Reflection, folded along a de Bruijn reduction sequence — the generalization of
`Term.mstep_reflect`, by the same head-first induction. -/
theorem mstep_reflect : ∀ {c d : Tm'}, c ⟶* d →
    ∀ (t : Tm) (Γ : List N), erase (N := N) t Γ = c → Covers Γ t →
    ∃ u : Tm, t ⟶* u ∧ erase u Γ = d := by
  intro c d h
  induction h using RTC.head_induction_on with
  | refl => intro t Γ he _; exact ⟨t, RTC.refl, he⟩
  | head hstep _ ih =>
      intro t Γ he hc
      obtain ⟨u₁, hs1, he1⟩ := step_reflect Γ hc (he ▸ hstep)
      obtain ⟨u, hus, hue⟩ := ih u₁ Γ he1 (covers_mstep (Tm' := Tm') hc hs1)
      exact ⟨u, hs1.trans hus, hue⟩

/-- Free variables only shrink along a reduction sequence. -/
theorem preserves_freeVars_mstep {t t' : Tm} (h : t ⟶* t') :
    ∀ x ∈ freeVars t', x ∈ freeVars (N := N) t := by
  induction h with
  | refl => exact fun _ hx => hx
  | tail _ s ih => exact fun x hx => ih x (preserves_freeVars (Tm' := Tm') s x hx)

/-- **Named confluence up to the induced α, from de Bruijn confluence** — the abstraction of
`Stlc/Named/TypeSystem.lean`'s `instConfluent`, scope and all: erase both paths over the term's
own free variables (which cover it by reflexivity), join in the image, reflect both traces, and
lift the single-scope agreement of the reflected reducts to `ErasureEq`. A language whose `≈α`
is the induced one reads this as its `Confluent` field. -/
theorem confluent_of_bridge
    (hconf : ∀ {d d₁ d₂ : Tm'}, d ⟶* d₁ → d ⟶* d₂ → ∃ e, d₁ ⟶* e ∧ d₂ ⟶* e)
    {t t₁ t₂ : Tm} (h₁ : t ⟶* t₁) (h₂ : t ⟶* t₂) :
    ∃ u₁ u₂ : Tm, t₁ ⟶* u₁ ∧ t₂ ⟶* u₂ ∧ ErasureEq Tm' (N := N) u₁ u₂ := by
  have hct : Covers (HasFreeVars.freeVars (N := N) t) t := fun _ hx => hx
  obtain ⟨d, hd₁, hd₂⟩ := hconf
    (erase_mstep (Tm' := Tm') (freeVars t) hct h₁)
    (erase_mstep (Tm' := Tm') (freeVars t) hct h₂)
  have hc1 : Covers (freeVars (N := N) t) t₁ := covers_mstep (Tm' := Tm') hct h₁
  have hc2 : Covers (freeVars (N := N) t) t₂ := covers_mstep (Tm' := Tm') hct h₂
  obtain ⟨u₁, hs₁, he₁⟩ := mstep_reflect hd₁ t₁ _ rfl hc1
  obtain ⟨u₂, hs₂, he₂⟩ := mstep_reflect hd₂ t₂ _ rfl hc2
  refine ⟨u₁, u₂, hs₁, hs₂, ?_⟩
  exact erasureEq_of_agree' (covers_mstep (Tm' := Tm') hc1 hs₁)
    (covers_mstep (Tm' := Tm') hc2 hs₂) (he₁.trans he₂.symm)

end ReflectBridge

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
  /-- **Typed terms are scoped**: every free variable of a typed term is bound. True of any
  judgement worth the name, underivable from the abstract one — and the law that turns the
  enumeration-carrying transport theorems into unconditional ones, via the canonical scope
  below. -/
  typing_covers : ∀ {Γ : Named.Context N Ty} {t : Tm} {τ : Ty},
      Γ ⊢ t : τ → ∀ x ∈ freeVars t, ∃ σ : Ty, Γ.get? x = some σ

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

/-! ### The canonical enumeration

Every transport theorem above carries "choose an enumeration, supply a compatible de Bruijn
context". A context supplies its own: the keys of its `toList`, with the erased values in the
same order. `typing_covers` then puts every typed term inside it, and the enumeration
hypotheses disappear from the statements a named instance actually needs. -/

/-- The canonical scope of a context: its keys, in `toList` order. -/
def canonScope [Atom N] (Γ : Named.Context N Ty) : List N :=
  Γ.toList.map Prod.fst

/-- …and the canonical de Bruijn context: the erased values, in the same order. -/
def canonCtx [Atom N] (eraseTy : Ty → Ty') (Γ : Named.Context N Ty) : DeBruijn.Context Ty' :=
  Γ.toList.map (fun p => eraseTy p.2)

private theorem canon_aligned [Atom N] (eraseTy : Ty → Ty') :
    ∀ (l : List (N × Ty)) (x : N), x ∈ l.map Prod.fst →
      ∃ τ : Ty, (x, τ) ∈ l ∧
        (l.map (fun p => eraseTy p.2))[scopeIdx x (l.map Prod.fst)]? = some (eraseTy τ)
  | [], x, hx => by simp at hx
  | (y, σ) :: l, x, hx => by
      by_cases hxy : y = x
      · subst hxy
        refine ⟨σ, List.mem_cons_self .., ?_⟩
        show (eraseTy σ :: l.map (fun p => eraseTy p.2))[scopeIdx y (y :: l.map Prod.fst)]?
          = some (eraseTy σ)
        rw [show scopeIdx y (y :: l.map Prod.fst) = 0 from by simp [scopeIdx]]
        rfl
      · have hx' : x ∈ l.map Prod.fst := by
          cases List.mem_cons.mp hx with
          | inl h => exact absurd h.symm hxy
          | inr h => exact h
        obtain ⟨τ, hmem, hidx⟩ := canon_aligned eraseTy l x hx'
        refine ⟨τ, List.mem_cons_of_mem _ hmem, ?_⟩
        show (eraseTy σ :: l.map (fun p => eraseTy p.2))[scopeIdx x (y :: l.map Prod.fst)]?
          = some (eraseTy τ)
        rw [show scopeIdx x (y :: l.map Prod.fst) = scopeIdx x (l.map Prod.fst) + 1 from by
          simp [scopeIdx, hxy]]
        simpa using hidx

/-- The canonical pair is compatible — no choice was ever needed. -/
theorem canon_compat [Atom N] (eraseTy : Ty → Ty') (Γ : Named.Context N Ty) :
    CtxCompat eraseTy Γ (canonScope Γ) (canonCtx eraseTy Γ) := by
  intro x hx
  obtain ⟨τ, hmem, hidx⟩ := canon_aligned eraseTy Γ.toList x hx
  refine ⟨τ, ?_, hidx⟩
  rw [Std.HashMap.get?_eq_getElem?]
  exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem

/-- A bound name is enumerated. -/
theorem mem_canonScope [Atom N] {Γ : Named.Context N Ty} {x : N} {σ : Ty}
    (h : Γ.get? x = some σ) : x ∈ canonScope Γ := by
  have hm : (x, σ) ∈ Γ.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact h
  exact List.mem_map.mpr ⟨(x, σ), hm, rfl⟩

variable [Atom N] [Step Tm] [Named.HasType N Tm Ty]

/-- Typed terms are covered by the canonical scope — `typing_covers` composed with
`mem_canonScope`, the hinge of everything below. -/
theorem typed_covers [Step Tm'] [DeBruijn.HasType Tm' Ty'] [TypingBridge N Tm Ty Tm' Ty']
    {Γ : Named.Context N Ty} {t : Tm} {τ : Ty} (ht : Γ ⊢ t : τ) :
    ∀ x ∈ HasFreeVars.freeVars t, x ∈ canonScope Γ := fun x hx =>
  let ⟨_, hσ⟩ := TypingBridge.typing_covers (Tm' := Tm') (Ty' := Ty') ht x hx
  mem_canonScope hσ

/-- **Preservation, unconditionally**: the enumeration hypotheses of `preservation_via_erase`
discharged by the canonical pair. The named subject-reduction obligation is now zero choices. -/
theorem preservation_of_bridge [DeBruijn.LawfulTypeSystem Tm' Ty']
    [TypingBridge N Tm Ty Tm' Ty']
    {Γ : Named.Context N Ty} {t t' : Tm} {τ : Ty}
    (ht : Γ ⊢ t : τ) (hs : t ⟶ t') : Γ ⊢ t' : τ :=
  preservation_via_erase (canonScope Γ) (canonCtx HasEraseTy.eraseTy Γ)
    (typed_covers (Tm' := Tm') (Ty' := Ty') ht) (canon_compat _ Γ) ht hs

/-- **Strong normalization, unconditionally**: erase the typing canonically, take the de Bruijn
tower's SN, reflect along the erasure. The named tower's hardest field, from a bridge and the
positional proof. -/
theorem stronglyNormalizing_of_bridge [DeBruijn.StronglyNormalizing Tm' Ty']
    [TypingBridge N Tm Ty Tm' Ty']
    {Γ : Named.Context N Ty} {t : Tm} {τ : Ty} (ht : Γ ⊢ t : τ) :
    SN (· ⟶ ·) t :=
  StepBridge.sn_of_erase (canonScope Γ) (typed_covers (Tm' := Tm') (Ty' := Ty') ht)
    (DeBruijn.StronglyNormalizing.StronglyNormalizing
      (TypingBridge.erase_typing (canonScope Γ) (canonCtx HasEraseTy.eraseTy Γ)
        (typed_covers (Tm' := Tm') (Ty' := Ty') ht) (canon_compat _ Γ) ht))

/-- **α-respect of typing, unconditionally**: erasure-equal terms type alike — erase, rewrite
along the agreement, reflect. The named tower's `LawfulAlphaEq.typing_respects`, for a language
whose `≈α` is the induced one. -/
theorem typing_respects_of_bridge [Step Tm'] [DeBruijn.HasType Tm' Ty']
    [TypingBridge N Tm Ty Tm' Ty']
    {Γ : Named.Context N Ty} {t u : Tm} {τ : Ty}
    (h : ErasureEq Tm' (N := N) t u) (ht : Γ ⊢ t : τ) : Γ ⊢ u : τ := by
  have hct := typed_covers (Tm' := Tm') (Ty' := Ty') ht
  have hcu : ∀ x ∈ HasFreeVars.freeVars u, x ∈ canonScope Γ := fun x hx =>
    hct x (h.1 ▸ hx)
  apply TypingBridge.erase_typing_reflect (canonScope Γ) (canonCtx HasEraseTy.eraseTy Γ)
    hcu (canon_compat _ Γ)
  rw [← h.2 (canonScope Γ) hct]
  exact TypingBridge.erase_typing (canonScope Γ) (canonCtx HasEraseTy.eraseTy Γ)
    hct (canon_compat _ Γ) ht

end Typing

end LambdaLab.TypeSystem.Bridge
