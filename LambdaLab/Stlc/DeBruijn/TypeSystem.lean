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

/-! ## Stability of typing under type-substitution

Substitution maps over a list context, so `Lookup` commutes with it by its own induction — no
`cong`, no keywise reasoning. -/

theorem Lookup.pSubst {Γ : Ctx} {n : Nat} {τ : Ty} (σ : _root_.Subst Nat Ty) (h : Lookup Γ n τ) :
    Lookup (HasSubst.pSubst Γ σ) n (HasSubst.pSubst τ σ) := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

/-- **Typing is stable under type-substitution** — the induction over the judgement, with
`Ty.pSubst_arrow` opening the arrow at the two rules that mention one. -/
theorem HasType.stability {Γ : Ctx} {e : Term} {τ : Ty} (σ : _root_.Subst Nat Ty)
    (h : HasType Γ e τ) :
    HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst e σ) (HasSubst.pSubst τ σ) := by
  induction h with
  | var hl => exact .var (hl.pSubst σ)
  | lam _ ih =>
      rw [Ty.pSubst_arrow]
      exact .lam ih
  | app _ _ ihf iha =>
      rw [Ty.pSubst_arrow] at ihf
      exact .app ihf iha

/-- Stability and the term-side mixins, all discharged; the type-side mixins come from the
`Signature` machinery, as the named ones do. -/
instance instLawfulMVars : TypeSystem.DeBruijn.LawfulMVars Term Ty where
  Stability := HasType.stability
  tyGroundStable := inferInstance
  tmGroundStable := inferInstance
  tyLawfulComp := inferInstance
  tmLawfulComp := inferInstance
  tyLawfulRestrict := inferInstance
  tmLawfulRestrict := inferInstance

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

/-! ## Reduction never invents a metavariable

Shifting and substituting move term structure around; annotations only travel, so groundness
survives each step and hence the whole reduction `eval` takes. -/

/-- Shifting introduces no annotation. -/
theorem Term.shift_tyIsFree : ∀ {e : Term} {c n : Nat},
    Term.tyIsFree (e.shift c) n → Term.tyIsFree e n := by
  intro e
  induction e with
  | var m =>
      intro c n h
      unfold Term.shift at h
      split at h <;> exact h.elim
  | lam τ b ih =>
      intro c n h
      cases h with
      | inl hτ => exact Or.inl hτ
      | inr hb => exact Or.inr (ih hb)
  | app f a ihf iha =>
      intro c n h
      cases h with
      | inl hf => exact Or.inl (ihf hf)
      | inr ha => exact Or.inr (iha ha)

/-- Substitution's annotations come from its two inputs. -/
theorem Term.subst_tyIsFree : ∀ {e : Term} {j : Nat} {v : Term} {n : Nat},
    Term.tyIsFree (e.subst j v) n → Term.tyIsFree e n ∨ Term.tyIsFree v n := by
  intro e
  induction e with
  | var m =>
      intro j v n h
      unfold Term.subst at h
      split at h
      · exact Or.inr h
      · split at h <;> exact h.elim
  | lam τ b ih =>
      intro j v n h
      cases h with
      | inl hτ => exact Or.inl (Or.inl hτ)
      | inr hb =>
          cases ih hb with
          | inl h' => exact Or.inl (Or.inr h')
          | inr hv => exact Or.inr (Term.shift_tyIsFree hv)
  | app f a ihf iha =>
      intro j v n h
      cases h with
      | inl h' =>
          cases ihf h' with
          | inl hf => exact Or.inl (Or.inl hf)
          | inr hv => exact Or.inr hv
      | inr h' =>
          cases iha h' with
          | inl ha => exact Or.inl (Or.inr ha)
          | inr hv => exact Or.inr hv

/-- A step preserves groundness — β's substitution draws only on the redex's own pieces. -/
theorem Step.ground : ∀ {e e' : Term}, Step e e' →
    HasVars.Ground (A := Nat) e → HasVars.Ground (A := Nat) e' := by
  intro e e' s
  induction s with
  | beta =>
      intro h n hn
      cases Term.subst_tyIsFree hn with
      | inl hb => exact h n (Or.inl (Or.inr hb))
      | inr hv => exact h n (Or.inr hv)
  | lam _ ih =>
      intro h n hn
      cases hn with
      | inl hτ => exact h n (Or.inl hτ)
      | inr hb => exact ih (fun m hm => h m (Or.inr hm)) n hb
  | appL _ ih =>
      intro h n hn
      cases hn with
      | inl h₁ => exact ih (fun m hm => h m (Or.inl hm)) n h₁
      | inr h₂ => exact h n (Or.inr h₂)
  | appR _ ih =>
      intro h n hn
      cases hn with
      | inl h₁ => exact h n (Or.inl h₁)
      | inr h₂ => exact ih (fun m hm => h m (Or.inr hm)) n h₂

/-- …and so does a whole reduction sequence. -/
theorem MStep.ground {e e' : Term} (h : RTC Step e e')
    (hg : HasVars.Ground (A := Nat) e) : HasVars.Ground (A := Nat) e' := by
  induction h with
  | refl => exact hg
  | tail _ s ih => exact Step.ground s ih

/-- The two `eval` laws are `Eval.lean`'s, proved beside the definition; groundness folds
`Step.ground` along the reduction `eval` actually takes. The `have`s re-read each hypothesis at
the concrete judgement — pure defeq through the instance projections, which the elaborator only
performs metavariable-free. -/
instance instLawfulHasEval : TypeSystem.DeBruijn.LawfulHasEval Term Ty :=
  { instHasEval, instStronglyNormalizing, instConfluent with
    evalNormal := fun {Γ t τ} h => by
      have h' : HasType Γ t τ := h
      exact Term.eval_normalForm _ (HasType.sn h')
    evalReachable := fun {Γ t τ} h => by
      have h' : HasType Γ t τ := h
      exact Term.mstep_eval _ (HasType.sn h')
    evalGround := fun {Γ t τ} h hg => by
      have h' : HasType Γ t τ := h
      exact MStep.ground (Term.mstep_eval _ (HasType.sn h')) hg }

/-! ## Closed terms: substitution misses, weakening is free

The two statements the named side needed `Atom.freshFor` gymnastics for are free-variable-bound
arguments here — the de Bruijn dividend, one last time. -/

theorem Lookup.lt_length {Γ : Ctx} {n : Nat} {τ : Ty} (h : Lookup Γ n τ) : n < Γ.length := by
  induction h with
  | here => simp
  | there _ ih => exact Nat.succ_lt_succ ih

theorem Lookup.append {Γ Γ' : Ctx} {n : Nat} {τ : Ty} (h : Lookup Γ n τ) :
    Lookup (Γ ++ Γ') n τ := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

/-- **Weakening on the right is invisible**: the indices a term uses look up the prefix. Not the
named `cong` (the contexts agree nowhere); not the named `weaken_closed` proof either (nothing to
rename). -/
theorem HasType.weaken_append {Γ Γ' : Ctx} {e : Term} {τ : Ty} (h : HasType Γ e τ) :
    HasType (Γ ++ Γ') e τ := by
  induction h with
  | var hl => exact .var hl.append
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha

/-- **Substitution above the context misses**: a term typed in `Γ` has no variable at or past
`Γ.length`, so substituting there is the identity. At `Γ = []` this is `tsubst_closed`, with no
closedness needed of the *value* — there is no capture to protect against. -/
theorem HasType.subst_of_le {Γ : Ctx} {e : Term} {τ : Ty} (h : HasType Γ e τ) :
    ∀ (j : Nat), Γ.length ≤ j → ∀ (v : Term), e.subst j v = e := by
  induction h with
  | @var Γ n τ hl =>
      intro j hj v
      have hn := hl.lt_length
      simp only [Term.subst]
      rw [if_neg (by omega), if_neg (by omega)]
  | lam _ ih =>
      intro j hj v
      simp only [Term.subst]
      rw [ih (j + 1) (Nat.succ_le_succ hj) (v.shift 0)]
  | app _ _ ih₁ ih₂ =>
      intro j hj v
      simp only [Term.subst]
      rw [ih₁ j hj v, ih₂ j hj v]

/-- Term-for-variable substitution at index `0`: the operation is `Basic.lean`'s `subst`, the
typing law is `HasType.subst_lemma` at the head binder, and the closed-term laws are the
free-variable-bound arguments above. -/
instance instHasTermSubst : TypeSystem.DeBruijn.HasTermSubst Term Ty :=
  { instLawfulMVars with
    tsubst := fun t v => t.subst 0 v
    tsubst_typing := fun {Γ σ τ t v} ht hv => by
      have ht' : HasType (σ :: Γ) t τ := ht
      have hv' : HasType [] v σ := hv
      exact HasType.subst_lemma [] ht' (HasType.weaken_append hv')
    tsubst_ground := fun {t v} hgt hgv => by
      have hgt' : ∀ n, ¬ Term.tyIsFree t n := hgt
      have hgv' : ∀ n, ¬ Term.tyIsFree v n := hgv
      intro n hn
      have hn' : Term.tyIsFree (t.subst 0 v) n := hn
      cases Term.subst_tyIsFree hn' with
      | inl h => exact hgt' n h
      | inr h => exact hgv' n h
    tsubst_closed := fun {σ τ t v} hct _ => by
      have hct' : HasType [] t τ := hct
      exact HasType.subst_of_le hct' 0 (Nat.le_refl 0) v
    weaken_closed := fun {Γ t τ} h => by
      have h' : HasType [] t τ := h
      exact HasType.weaken_append h' }

end LambdaLab.Stlc.DeBruijn
