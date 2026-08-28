import LambdaLab.Stlc.Named.Basic
import LambdaLab.TypeSystem.Named.Basic

/-!
# Full single-step beta reduction (named variables)

Same shape as the de Bruijn variant, but the β-rule names the bound
variable explicitly: `(λx:τ. body) v ⟶ body[x := v]` using the naive
substitution from `Basic.lean`.
-/

namespace LambdaLab.Stlc.Named

inductive Step {N : Type} [LambdaLab.Nominal.Atom N] : Term N → Term N → Prop where
  | beta : Step (.app (.lam x τ body) v) (body.subst x v)
  | lam  : Step e e' → Step (.lam x τ e) (.lam x τ e')
  | appL : Step e₁ e₁' → Step (.app e₁ e₂) (.app e₁' e₂)
  | appR : Step e₂ e₂' → Step (.app e₁ e₂) (.app e₁ e₂')

instance instStep {N : Type} [LambdaLab.Nominal.Atom N] :
    LambdaLab.TypeSystem.Named.Step (Term N) where
  Step := Step

/-! ## Reduction does not invent metavariables

`Vernacular.HasTypeGround` demands `Ground` of every declaration body, so a stage that *reduces*
those bodies has to know that reduction keeps them ground. Nothing in the `TypeSystem` tower says
so — `Preservation` is about the judgement and `GroundStable` is about `pSubst`, neither about
`⟶` — and it is proved here, where the reduction relation is.

`Ground` for a term is `AnnotsGround`: no type annotation mentions a metavariable
(`Term.annotsGround_iff_ground`). β discards the binder's annotation and copies the argument into
the body, so the annotations of the reduct are a *subset* of the redex's — which is why this holds
at all, and why it needs the substitution lemma below rather than a bare induction on `Step`. -/

variable {N : Type} [LambdaLab.Nominal.Atom N]

/-- Renaming touches variables, never annotations. -/
theorem Term.annotsGround_rename (e : Term N) (y z : N) :
    (e.rename y z).AnnotsGround ↔ e.AnnotsGround := by
  induction e with
  | var x => by_cases h : x = y <;> simp [Term.rename, Term.AnnotsGround, h]
  | lam x τ body ih =>
      by_cases h : x = y <;> simp [Term.rename, Term.AnnotsGround, h, ih]
  | app e₁ e₂ ih₁ ih₂ => simp [Term.rename, Term.AnnotsGround, ih₁, ih₂]

/-- Substituting a ground term into a ground term leaves it ground. Proved by the substitution
function's own induction: the capture-avoiding case renames the binder first, which
`annotsGround_rename` says is invisible here. -/
theorem Term.annotsGround_subst {v : Term N} {x : N} (hv : v.AnnotsGround) :
    ∀ e : Term N, e.AnnotsGround → (e.subst x v).AnnotsGround := by
  intro e
  induction e using Term.subst.induct (x := x) (v := v) with
  | case1 => intro _; simpa [Term.subst] using hv
  | case2 a h => intro _; simp [Term.subst, h, Term.AnnotsGround]
  | case3 τ body => intro he; rw [Term.subst]; simpa using he
  | case4 y τ body hne hmem _z ih =>
      intro he
      simp only [Term.AnnotsGround] at he
      rw [Term.subst]; simp only [if_neg hne, if_pos hmem, Term.AnnotsGround]
      exact ⟨he.1, ih ((Term.annotsGround_rename body y _).mpr he.2)⟩
  | case5 y τ body hne hmem ih =>
      intro he
      simp only [Term.AnnotsGround] at he
      rw [Term.subst]; simp only [if_neg hne, if_neg hmem, Term.AnnotsGround]
      exact ⟨he.1, ih he.2⟩
  | case6 e₁ e₂ ih₁ ih₂ =>
      intro he
      simp only [Term.AnnotsGround] at he
      rw [Term.subst]; simp only [Term.AnnotsGround]
      exact ⟨ih₁ he.1, ih₂ he.2⟩

/-- **One step keeps a term ground.** -/
theorem Step.annotsGround {e e' : Term N} (s : Step e e') (he : e.AnnotsGround) :
    e'.AnnotsGround := by
  induction s with
  | beta =>
      simp only [Term.AnnotsGround] at he
      exact Term.annotsGround_subst he.2 _ he.1.2
  | lam _ ih =>
      simp only [Term.AnnotsGround] at he ⊢
      exact ⟨he.1, ih he.2⟩
  | appL _ ih =>
      simp only [Term.AnnotsGround] at he ⊢
      exact ⟨ih he.1, he.2⟩
  | appR _ ih =>
      simp only [Term.AnnotsGround] at he ⊢
      exact ⟨he.1, ih he.2⟩

end LambdaLab.Stlc.Named
