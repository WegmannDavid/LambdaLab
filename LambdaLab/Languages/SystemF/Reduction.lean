import LambdaLab.Languages.SystemF.Typing
import LambdaLab.Relation.Closure
import LambdaLab.Relation.Normalization

/-!
# System F — reduction

**Full** β: a redex is contracted wherever it sits, under `λ` and `Λ` included, so a term in
normal form has no redex anywhere. That is the reduction the evaluator normalizes by, and the one
strong normalization (`Normalization.lean`) is proved for.

    (λ A . t) u  ⟶  t[0 := u]          (Λ . t) [B]  ⟶  t[0 := B]

Collected here: closure of `Step` under both substitutions (`Step.subst`, `Step.tsubst`), the
inversions the reducibility argument takes apart, and the facts that move strong normalization
backwards along a substitution or out of an application. Then **preservation**.
-/

namespace LambdaLab.Languages.SystemF

/-- **One step of full β-reduction.** -/
inductive Step : Tm → Tm → Prop
  | beta {A : Ty} {t u : Tm} : Step (.app (.lam A t) u) (t.inst u)
  | tbeta {t : Tm} {B : Ty} : Step (.tapp (.tlam t) B) (t.tinst B)
  | lam {A : Ty} {t t' : Tm} : Step t t' → Step (.lam A t) (.lam A t')
  | appL {t t' u : Tm} : Step t t' → Step (.app t u) (.app t' u)
  | appR {t u u' : Tm} : Step u u' → Step (.app t u) (.app t u')
  | tlam {t t' : Tm} : Step t t' → Step (.tlam t) (.tlam t')
  | tappL {t t' : Tm} {B : Ty} : Step t t' → Step (.tapp t B) (.tapp t' B)

namespace Step

/-- Reduction survives substituting for the term variables. -/
theorem subst {t t' : Tm} (h : Step t t') : ∀ σ : Nat → Tm, Step (t.subst σ) (t'.subst σ) := by
  induction h with
  | beta => intro σ; rw [Tm.inst_subst]; exact .beta
  | tbeta => intro σ; rw [Tm.tinst_subst]; exact .tbeta
  | lam _ ih => intro σ; exact .lam (ih _)
  | appL _ ih => intro σ; exact .appL (ih σ)
  | appR _ ih => intro σ; exact .appR (ih σ)
  | tlam _ ih => intro σ; exact .tlam (ih _)
  | tappL _ ih => intro σ; exact .tappL (ih σ)

/-- …and substituting for the type variables. -/
theorem tsubst {t t' : Tm} (h : Step t t') : ∀ σ : Nat → Ty, Step (t.tsubst σ) (t'.tsubst σ) := by
  induction h with
  | beta => intro σ; rw [Tm.inst_tsubst]; exact .beta
  | tbeta => intro σ; rw [Tm.tinst_tsubst]; exact .tbeta
  | lam _ ih => intro σ; exact .lam (ih σ)
  | appL _ ih => intro σ; exact .appL (ih σ)
  | appR _ ih => intro σ; exact .appR (ih σ)
  | tlam _ ih => intro σ; exact .tlam (ih _)
  | tappL _ ih => intro σ; exact .tappL (ih σ)

/-! ## Inversions -/

theorem var_inv {n : Nat} {w : Tm} : ¬ Step (.var n) w := by intro h; cases h

theorem lam_inv {A : Ty} {t w : Tm} (h : Step (.lam A t) w) : ∃ t', Step t t' ∧ w = .lam A t' := by
  cases h with
  | lam h => exact ⟨_, h, rfl⟩

theorem tlam_inv {t w : Tm} (h : Step (.tlam t) w) : ∃ t', Step t t' ∧ w = .tlam t' := by
  cases h with
  | tlam h => exact ⟨_, h, rfl⟩

end Step

/-- **Neutral terms**: those that are not abstractions, so that putting one in head position
creates no redex. -/
def Tm.Neutral : Tm → Prop
  | .lam _ _ => False
  | .tlam _ => False
  | _ => True

namespace Step

/-- An application with a neutral head reduces only inside one of its parts. -/
theorem app_neutral {t u w : Tm} (hn : t.Neutral) (h : Step (.app t u) w) :
    (∃ t', Step t t' ∧ w = .app t' u) ∨ (∃ u', Step u u' ∧ w = .app t u') := by
  cases h with
  | beta => exact absurd hn id
  | appL h => exact .inl ⟨_, h, rfl⟩
  | appR h => exact .inr ⟨_, h, rfl⟩

/-- A type application with a neutral head reduces only inside the head. -/
theorem tapp_neutral {t w : Tm} {B : Ty} (hn : t.Neutral) (h : Step (.tapp t B) w) :
    ∃ t', Step t t' ∧ w = .tapp t' B := by
  cases h with
  | tbeta => exact absurd hn id
  | tappL h => exact ⟨_, h, rfl⟩

end Step

/-! ## Strong normalization, transported -/

/-- If a substitution instance normalizes, so does the term: every reduction of the term is
mirrored in the instance. -/
theorem sn_of_subst {t : Tm} {σ : Nat → Tm} (h : SN Step (t.subst σ)) : SN Step t := by
  generalize hx : t.subst σ = x at h
  induction h generalizing t with
  | intro _ ih =>
      subst hx
      exact .intro fun t' hs => ih _ (hs.subst σ) rfl

theorem sn_of_tsubst {t : Tm} {σ : Nat → Ty} (h : SN Step (t.tsubst σ)) : SN Step t := by
  generalize hx : t.tsubst σ = x at h
  induction h generalizing t with
  | intro _ ih =>
      subst hx
      exact .intro fun t' hs => ih _ (hs.tsubst σ) rfl

/-- If an application normalizes, so does its head. -/
theorem sn_app_left {t u : Tm} (h : SN Step (.app t u)) : SN Step t := by
  generalize hx : Tm.app t u = x at h
  induction h generalizing t with
  | intro _ ih =>
      subst hx
      exact .intro fun t' hs => ih _ (.appL hs) rfl

/-- If a type application normalizes, so does its head. -/
theorem sn_tapp_left {t : Tm} {B : Ty} (h : SN Step (.tapp t B)) : SN Step t := by
  generalize hx : Tm.tapp t B = x at h
  induction h generalizing t with
  | intro _ ih =>
      subst hx
      exact .intro fun t' hs => ih _ (.tappL hs) rfl

/-! ## Preservation -/

/-- **Subject reduction**: a step keeps the type. The two β cases are the substitution lemmas of
`Typing.lean`, `HasType.inst` and `HasType.tinst`. -/
theorem HasType.preservation {t t' : Tm} (hs : Step t t') :
    ∀ {Δ : Nat} {Γ : List Ty} {A : Ty}, HasType Δ Γ t A → HasType Δ Γ t' A := by
  induction hs with
  | beta =>
      intro _ _ _ h
      cases h with
      | app h₁ h₂ =>
          cases h₁ with
          | lam _ hb => exact hb.inst h₂
  | tbeta =>
      intro _ _ _ h
      cases h with
      | tapp h₁ hB =>
          cases h₁ with
          | tlam hb => exact hb.tinst hB
  | lam _ ih =>
      intro _ _ _ h
      cases h with
      | lam hA hb => exact .lam hA (ih hb)
  | appL _ ih =>
      intro _ _ _ h
      cases h with
      | app h₁ h₂ => exact .app (ih h₁) h₂
  | appR _ ih =>
      intro _ _ _ h
      cases h with
      | app h₁ h₂ => exact .app h₁ (ih h₂)
  | tlam _ ih =>
      intro _ _ _ h
      cases h with
      | tlam hb => exact .tlam (ih hb)
  | tappL _ ih =>
      intro _ _ _ h
      cases h with
      | tapp h₁ hB => exact .tapp (ih h₁) hB

/-- Preservation along any number of steps. -/
theorem HasType.preservation_rtc {Δ : Nat} {Γ : List Ty} {t t' : Tm} {A : Ty}
    (h : HasType Δ Γ t A) (hs : RTC Step t t') : HasType Δ Γ t' A := by
  induction hs with
  | refl => exact h
  | tail _ s ih => exact HasType.preservation s ih

end LambdaLab.Languages.SystemF
