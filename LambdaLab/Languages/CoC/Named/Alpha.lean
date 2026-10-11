import LambdaLab.Languages.CoC.Named.Typing

/-!
# CoC, named — α-equivalence

Two named terms are **α-equivalent** when they differ only in the names of their bound
variables: when they translate to the same de Bruijn term, against every list of binders. That is
an equivalence relation by construction, and everything the metatheory says is invariant under
it:

* typing, of the term (`HasType.alpha_tm`) and of the type (the `alpha` rule);
* reduction (`Step.alpha`): an α-variant of a term that steps can take a step to an α-variant of
  the result;
* normality (`Tm.Normal.alpha`).

The facts are one-liners, because the translation already identifies what α-equivalence
identifies; the work is in `Translation.lean`, `Step.lean` and `Typing.lean`.
-/

namespace LambdaLab.Languages.CoC.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N]

/-- **α-equivalent terms**: the same up to the names of their bound variables. -/
def Tm.AlphaEq (t u : Tm N) : Prop := ∀ ns : List N, t.toDB ns = u.toDB ns

theorem Tm.AlphaEq.refl (t : Tm N) : t.AlphaEq t := fun _ => rfl
theorem Tm.AlphaEq.symm {t u : Tm N} (h : t.AlphaEq u) : u.AlphaEq t := fun ns => (h ns).symm
theorem Tm.AlphaEq.trans {t u v : Tm N} (h₁ : t.AlphaEq u) (h₂ : u.AlphaEq v) : t.AlphaEq v :=
  fun ns => (h₁ ns).trans (h₂ ns)

/-- **Typing does not see bound names**, of the term… -/
theorem HasType.alpha_tm {Γ : Ctx N} {t u T : Tm N} (h : HasType Γ t T) (hΓ : Ctx.Wf Γ)
    (htu : t.AlphaEq u) : HasType Γ u T := by
  have hd := h.toDB hΓ
  rw [htu Γ.names] at hd
  exact (hasType_iff_toDB hΓ).mpr hd

/-- …nor of the type. -/
theorem HasType.alpha_ty {Γ : Ctx N} {t A B : Tm N} (h : HasType Γ t A) (hAB : A.AlphaEq B) :
    HasType Γ t B :=
  .alpha h (hAB Γ.names)

/-- **Reduction does not see bound names**: what one α-variant reduces to, the other reduces to up
to bound names, against any binders. -/
theorem Step.alpha {t u t' : Tm N} (htu : t.AlphaEq u) (hs : Step t t') (ns : List N) :
    ∃ u', Step u u' ∧ u'.toDB ns = t'.toDB ns :=
  Step.reflect u ns _ (htu ns ▸ hs.toDB ns)

/-- **Normality does not see bound names.** -/
theorem Tm.Normal.alpha {t u : Tm N} (h : t.Normal) (htu : t.AlphaEq u) : u.Normal :=
  (normal_iff_toDB u []).mpr (htu [] ▸ (normal_iff_toDB t []).mp h)

end LambdaLab.Languages.CoC.Named
