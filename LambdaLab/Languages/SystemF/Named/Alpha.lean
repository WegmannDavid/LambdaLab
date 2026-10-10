import LambdaLab.Languages.SystemF.Named.Typing

/-!
# System F, named — α-equivalence

Two named types, or terms, are **α-equivalent** when they differ only in the names of their
bound variables: when they translate to the same de Bruijn type or term, against every list of
binders. That is an equivalence relation by construction, and everything the metatheory says is
invariant under it:

* typing (`HasType.alpha`, and `conv` for the type);
* reduction (`Step.alpha`): an α-variant of a term that steps can take a step to an α-variant of
  the result, against any binders;
* normality (`Tm.Normal.alpha`).

The facts are one-liners, because the translation already identifies what α-equivalence
identifies; the work is in `Translation.lean` and `Step.lean`, which show the translation commutes
with substitution and with reduction.
-/

namespace LambdaLab.Languages.SystemF.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N]

/-- **α-equivalent types**: the same up to the names of their bound variables. -/
def Ty.AlphaEq (A B : Ty N) : Prop := ∀ Θ : List N, A.toDB Θ = B.toDB Θ

/-- **α-equivalent terms**: the same up to the names of their bound variables. -/
def Tm.AlphaEq (t u : Tm N) : Prop := ∀ Θ Γ : List N, t.toDB Θ Γ = u.toDB Θ Γ

theorem Ty.AlphaEq.refl (A : Ty N) : A.AlphaEq A := fun _ => rfl
theorem Ty.AlphaEq.symm {A B : Ty N} (h : A.AlphaEq B) : B.AlphaEq A := fun Θ => (h Θ).symm
theorem Ty.AlphaEq.trans {A B C : Ty N} (h₁ : A.AlphaEq B) (h₂ : B.AlphaEq C) : A.AlphaEq C :=
  fun Θ => (h₁ Θ).trans (h₂ Θ)

theorem Tm.AlphaEq.refl (t : Tm N) : t.AlphaEq t := fun _ _ => rfl
theorem Tm.AlphaEq.symm {t u : Tm N} (h : t.AlphaEq u) : u.AlphaEq t := fun Θ Γ => (h Θ Γ).symm
theorem Tm.AlphaEq.trans {t u v : Tm N} (h₁ : t.AlphaEq u) (h₂ : u.AlphaEq v) : t.AlphaEq v :=
  fun Θ Γ => (h₁ Θ Γ).trans (h₂ Θ Γ)

/-- **Typing does not see bound names.** -/
theorem HasType.alpha {Θ : List N} {Γ : Ctx N} {t u : Tm N} {A : Ty N}
    (h : HasType Θ Γ t A) (htu : t.AlphaEq u) : HasType Θ Γ u A := by
  have hd := h.toDB
  rw [htu Θ Γ.names] at hd
  exact hasType_iff_toDB.mpr hd

/-- …nor do types. -/
theorem HasType.alpha_ty {Θ : List N} {Γ : Ctx N} {t : Tm N} {A B : Ty N}
    (h : HasType Θ Γ t A) (hAB : A.AlphaEq B) : HasType Θ Γ t B :=
  .conv h (hAB Θ)

/-- **Reduction does not see bound names**: what one α-variant reduces to, the other reduces to
up to bound names, against any binders. -/
theorem Step.alpha {t u t' : Tm N} (htu : t.AlphaEq u) (hs : Step t t') (Θ Γ : List N) :
    ∃ u', Step u u' ∧ u'.toDB Θ Γ = t'.toDB Θ Γ :=
  Step.reflect u Θ Γ _ (htu Θ Γ ▸ hs.toDB Θ Γ)

/-- **Normality does not see bound names.** -/
theorem Tm.Normal.alpha {t u : Tm N} (h : t.Normal) (htu : t.AlphaEq u) : u.Normal :=
  (normal_iff_toDB u [] []).mpr (htu [] [] ▸ (normal_iff_toDB t [] []).mp h)

end LambdaLab.Languages.SystemF.Named
