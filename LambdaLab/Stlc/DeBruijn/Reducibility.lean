import LambdaLab.Stlc.DeBruijn.Typing
import LambdaLab.Stlc.DeBruijn.Step
import LambdaLab.Stlc.DeBruijn.Substitution
import LambdaLab.Stlc.DeBruijn.ParSubst
import LambdaLab.Stlc.DeBruijn.Confluence

/-!
# Strong normalization and Tait's reducibility predicate

`SN e` says `e` has no infinite reduction sequence (equivalently, `e` is in the
well-founded part of the inverse `Step` relation).

`Reducible τ e` is Tait's predicate: a stronger invariant than SN that is
preserved by the operations we care about. It's defined by recursion on the
type. The plan to prove SN for STLC:
1. `Reducible τ e → SN e` (CR1).
2. Every well-typed term is reducible (the fundamental theorem).
3. Conclude SN.
-/

namespace LambdaLab.Stlc.DeBruijn

/-! ## Strong normalization -/

inductive SN : Term → Prop where
  | intro : (∀ e', e ⟶ e' → SN e') → SN e

/-- A reduct of a SN term is SN. -/
theorem SN.unfold : ∀ {e e'}, SN e → e ⟶ e' → SN e'
  | _, _, .intro h, s => h _ s

/-! ## Reducibility predicate -/

def Reducible : Ty → Term → Prop
  | .base,         e => SN e
  | .arrow τ₁ τ₂,  e => SN e ∧ ∀ v, Reducible τ₁ v → Reducible τ₂ (.app e v)
  -- an atom is inert, so reducibility at it is bare strong normalization, as at `base`
  | .mvar _,       e => SN e

/-! ## CR1: reducibility implies strong normalization -/

theorem Reducible.sn : ∀ {τ : Ty} {e : Term}, Reducible τ e → SN e
  | .base,         _, h => h
  | .arrow _ _,    _, ⟨h, _⟩ => h
  | .mvar _,       _, h => h

/-! ## CR2: reducibility is closed under reduction -/

theorem Reducible.preserves : ∀ {τ : Ty} {e e' : Term},
    Reducible τ e → e ⟶ e' → Reducible τ e' := by
  intro τ
  induction τ with
  | base =>
      intro e e' hr hs
      exact SN.unfold hr hs
  | arrow τ₁ τ₂ _ ih₂ =>
      intro e e' hr hs
      exact ⟨SN.unfold hr.1 hs, fun v hv => ih₂ (hr.2 v hv) (Step.appL hs)⟩
  | mvar _ =>
      intro e e' hr hs
      exact SN.unfold hr hs

/-! ## Neutral terms: anything that isn't a lambda -/

inductive Neutral : Term → Prop where
  | var : Neutral (.var n)
  | app : Neutral (.app e₁ e₂)

/-! ## CR3: head expansion for neutrals

If `e` is neutral and every reduct of `e` is reducible, then `e` is reducible.
The arrow case requires inner induction on `SN v` because reductions can occur
on either side of an application.
-/

private theorem Reducible.cr3_arrow {τ₁ τ₂ : Ty}
    (cr2_τ₁ : ∀ {a a' : Term}, Reducible τ₁ a → a ⟶ a' → Reducible τ₁ a')
    (cr3_τ₂ : ∀ {a : Term}, Neutral a →
              (∀ a', a ⟶ a' → Reducible τ₂ a') → Reducible τ₂ a)
    {e : Term} (hne : Neutral e)
    (h : ∀ e', e ⟶ e' → Reducible (τ₁ ⇒ τ₂) e')
    {v : Term} (hvSN : SN v) (hv : Reducible τ₁ v) :
    Reducible τ₂ (.app e v) := by
  induction hvSN with
  | intro _ ih =>
      apply cr3_τ₂ Neutral.app
      intro w hw
      cases hw with
      | beta     => cases hne
      | appL hsL => exact (h _ hsL).2 _ hv
      | appR hsR => exact ih _ hsR (cr2_τ₁ hv hsR)

theorem Reducible.cr3 : ∀ {τ : Ty} {e : Term},
    Neutral e → (∀ e', e ⟶ e' → Reducible τ e') → Reducible τ e := by
  intro τ
  induction τ with
  | base =>
      intro e _ h
      exact SN.intro h
  | arrow τ₁ τ₂ _ ih₂ =>
      intro e hne h
      refine ⟨?_, fun v hv => ?_⟩
      · exact SN.intro fun e' hs => (h e' hs).1
      · exact Reducible.cr3_arrow (@Reducible.preserves τ₁) ih₂ hne h hv.sn hv
  | mvar _ =>
      intro e _ h
      exact SN.intro h

/-! ## Variables are reducible at every type -/

theorem Reducible.var (τ : Ty) (n : Nat) : Reducible τ (.var n) := by
  apply Reducible.cr3 Neutral.var
  intro e' hs
  cases hs

/-! ## Substitution-step congruence: a step in `e` lifts to a step in `e.subst k v` -/

theorem Step.subst_congr : ∀ {e e' : Term}, e ⟶ e' →
    ∀ (k : Nat) (v : Term), e.subst k v ⟶ e'.subst k v := by
  intro e e' hs
  induction hs with
  | @beta τ e₁ e₂ =>
      intro k v
      simp only [Term.subst]
      have hb : (Term.app (.lam τ (e₁.subst (k+1) (v.shift 0))) (e₂.subst k v)) ⟶
                ((e₁.subst (k+1) (v.shift 0)).subst 0 (e₂.subst k v)) := Step.beta
      rw [Term.subst_subst_distrib e₁ e₂ v (Nat.zero_le k)]
      exact hb
  | lam _ ih =>
      intro k v
      simp only [Term.subst]
      exact .lam (ih (k+1) (v.shift 0))
  | appL _ ih =>
      intro k v
      simp only [Term.subst]
      exact .appL (ih k v)
  | appR _ ih =>
      intro k v
      simp only [Term.subst]
      exact .appR (ih k v)

/-! ## SN reverse: if `e.subst k v` is SN, so is `e` -/

private theorem SN.of_subst_aux : ∀ {a : Term}, SN a →
    ∀ {e : Term} {k : Nat} {v : Term}, e.subst k v = a → SN e := by
  intro a h
  induction h with
  | @intro a' _ ih =>
      intro e k v heq
      apply SN.intro
      intro e' hs
      have h_step_a' : a' ⟶ e'.subst k v := by
        rw [← heq]; exact Step.subst_congr hs k v
      exact ih _ h_step_a' rfl

theorem SN.of_subst {e : Term} (k : Nat) (v : Term)
    (h : SN (e.subst k v)) : SN e :=
  SN.of_subst_aux h rfl

/-! ## CR2 lifted to multi-step reduction -/

theorem Reducible.preserves_mstep {τ : Ty} {e e' : Term}
    (hm : e ⟶* e') : Reducible τ e → Reducible τ e' := by
  induction hm with
  | refl => exact id
  | head s _ ih => intro h; exact ih (Reducible.preserves h s)

/-! ## Head expansion for β-redexes

If `body` and `v` are SN and `body[0:=v]` is reducible at `τ₂`, then
`(.lam τ₁ body) v` is reducible at `τ₂`. The proof uses CR3 plus a
nested induction on `SN body` and `SN v`.
-/

theorem Reducible.head_exp_beta {τ₁ τ₂ : Ty} :
    ∀ {body : Term}, SN body → ∀ {v : Term}, SN v →
    Reducible τ₂ (body.subst 0 v) →
    Reducible τ₂ (.app (.lam τ₁ body) v) := by
  intro body hbSN
  induction hbSN with
  | @intro body hb_step hb_ih =>
      intro v hvSN
      induction hvSN with
      | @intro v hv_step hv_ih =>
          intro h_subst
          apply Reducible.cr3 Neutral.app
          intro w hw
          cases hw with
          | beta => exact h_subst
          | appL hsL =>
              cases hsL with
              | lam s =>
                  rename_i body'
                  exact hb_ih body' s (SN.intro hv_step)
                    (Reducible.preserves h_subst (Step.subst_congr s 0 v))
          | appR hsR =>
              rename_i v'
              apply hv_ih v' hsR
              exact Reducible.preserves_mstep
                (PStep.toMStep (PStep.subst (PStep.refl body) (Step.toPStep hsR) 0))
                h_subst

/-! ## SN of a lambda from SN of its body -/

theorem SN.lam : ∀ {body : Term} {τ : Ty}, SN body → SN (.lam τ body) := by
  intro body τ h
  induction h with
  | intro _ ih =>
      apply SN.intro
      intro e' hs
      cases hs with
      | lam s =>
          rename_i body'
          exact ih body' s

/-! ## Good substitutions -/

def RedSubst (Γ : Ctx) (σ : Subst) : Prop :=
  ∀ n τ, Lookup Γ n τ → Reducible τ (σ n)

theorem RedSubst.cons {τ : Ty} {Γ : Ctx} {σ : Subst} {v : Term}
    (hσ : RedSubst Γ σ) (hv : Reducible τ v) :
    RedSubst (τ :: Γ) (Subst.cons v σ) := by
  intro n τ' hl
  cases hl with
  | here     => exact hv
  | there hl' => exact hσ _ _ hl'

theorem RedSubst.id (Γ : Ctx) : RedSubst Γ Subst.id := by
  intro n τ _
  exact Reducible.var τ n

/-! ## Fundamental theorem: every well-typed term is reducible

The lambda case is the meat: it uses `Reducible.head_exp_beta` together with
`Term.psubst_lift_beta` to bridge between the parallel-substitution form
`body.psubst (cons v σ)` and the β-redex form `(.lam τ (body.psubst σ.lift)) v`.
-/

theorem HasType.fundamental : ∀ {Γ : Ctx} {e : Term} {τ : Ty},
    HasType Γ e τ → ∀ (σ : Subst), RedSubst Γ σ → Reducible τ (e.psubst σ) := by
  intro Γ e τ ht
  induction ht with
  | var hl =>
      intro σ hσ
      exact hσ _ _ hl
  | @lam τ₁ Γ body τ₂ _ ih =>
      intro σ hσ
      simp only [Term.psubst]
      have h_body_sn : SN (body.psubst σ.lift) := by
        have h_red := ih (Subst.cons (.var 0) σ) (RedSubst.cons hσ (Reducible.var τ₁ 0))
        rw [← Term.psubst_lift_beta] at h_red
        exact SN.of_subst 0 (.var 0) (Reducible.sn h_red)
      refine ⟨SN.lam h_body_sn, fun v hv => ?_⟩
      have h_red := ih (Subst.cons v σ) (RedSubst.cons hσ hv)
      rw [← Term.psubst_lift_beta] at h_red
      exact Reducible.head_exp_beta h_body_sn (Reducible.sn hv) h_red
  | app _ _ ih_f ih_a =>
      intro σ hσ
      simp only [Term.psubst]
      exact (ih_f σ hσ).2 _ (ih_a σ hσ)

/-! ## Strong normalization for STLC -/

theorem HasType.sn : ∀ {Γ : Ctx} {e : Term} {τ : Ty}, HasType Γ e τ → SN e := by
  intro Γ e τ ht
  have h := HasType.fundamental ht Subst.id (RedSubst.id Γ)
  rw [Term.psubst_id] at h
  exact Reducible.sn h

end LambdaLab.Stlc.DeBruijn
