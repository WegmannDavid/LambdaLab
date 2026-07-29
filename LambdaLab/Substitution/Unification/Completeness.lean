import LambdaLab.Substitution.Unification.Basic
import LambdaLab.Substitution.Unification.Soundness

/-! # Completeness of `unifyList`

If any unifier exists, the algorithm succeeds. Carries over from the
fat-typeclass version on `archive/fat-unification`. -/

/-- Pull the head equation out of a `Subst`-form unifier, in the `Signature.pSubst` spelling the
helper lemmas use. -/
theorem Subst.Unifies.head_eq {α : Type} [Signature α] {σ : Subst α} {x y : α}
    {eqs' : Equations α} (hσ : Subst.Unifies σ ((x, y) :: eqs')) :
    Signature.pSubst x σ = Signature.pSubst y σ :=
  hσ (x, y) List.mem_cons_self

/-- **Completeness of `unifyList`.** If any unifier exists for `eqs`, then
`unifyList eqs` succeeds. Equivalently — and more usefully in this
contrapositive form — if `unifyList eqs = none`, no unifier exists. Proved by
induction on `unifyList.induct`: success branches close trivially; failure
branches each contradict the unifier-exists hypothesis using one of
`occurs_no_unifier`, `decomp_none_no_unifier`, or `unifier_absorb`. The
mechanical `unifyList` case-split is dispatched by `grind [unifyList]`. -/
theorem unifyList_complete {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (σ : Subst α),
      Subst.Unifies σ eqs → unifyList eqs ≠ none := by
  intro eqs
  induction eqs using unifyList.induct with
  | case1 => intro σ _ heq; rw [unifyList] at heq; cases heq
  | case2 x y eqs' m hxv hyv ih =>
      intro σ hσ heq
      have heq : unifyList eqs' = none := by grind [unifyList]
      exact ih σ (fun p hp => hσ p (List.mem_cons_of_mem _ hp)) heq
  | case3 x y eqs' m hxv hyv hocc =>
      intro σ hσ _
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hxeq : x = Signature.var m := Signature.var_of_isVar x m hxv
      rw [hxeq] at hxy
      exact Signature.occurs_no_unifier y m σ hocc hyv hxy
  | case4 _ _ _ _ _ _ _ _ _ _ => intro _ _ heq; grind [unifyList]
  | case5 x y eqs' m hxv hyv hocc hnone ih =>
      intro σ hσ _
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hxeq : x = Signature.var m := Signature.var_of_isVar x m hxv
      rw [hxeq] at hxy
      have hσ_sub : Subst.Unifies σ (HasSubst.single eqs' m y) := by
        intro p hp
        rw [Equations.single_eq] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, hqeq⟩
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        simp only [Signature.hasSubst_pSubst_eq]
        rw [Signature.unifier_absorb σ q.1 m y hxy,
            Signature.unifier_absorb σ q.2 m y hxy]
        exact hq_unif
      exact ih σ hσ_sub hnone
  | case6 x y eqs' hxv m hyv hocc =>
      intro σ hσ _
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hyeq : y = Signature.var m := Signature.var_of_isVar y m hyv
      rw [hyeq] at hxy
      have hxv' : Signature.isVar x ≠ some m := by rw [hxv]; intro h; cases h
      exact Signature.occurs_no_unifier x m σ hocc hxv' hxy.symm
  | case7 _ _ _ _ _ _ _ _ _ _ => intro _ _ heq; grind [unifyList]
  | case8 x y eqs' hxv m hyv hocc hnone ih =>
      intro σ hσ _
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hyeq : y = Signature.var m := Signature.var_of_isVar y m hyv
      rw [hyeq] at hxy
      have hxy' : Signature.pSubst (Signature.var m) σ = Signature.pSubst x σ := hxy.symm
      have hσ_sub : Subst.Unifies σ (HasSubst.single eqs' m x) := by
        intro p hp
        rw [Equations.single_eq] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, hqeq⟩
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        simp only [Signature.hasSubst_pSubst_eq]
        rw [Signature.unifier_absorb σ q.1 m x hxy',
            Signature.unifier_absorb σ q.2 m x hxy']
        exact hq_unif
      exact ih σ hσ_sub hnone
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro σ hσ heq
      have heq : unifyList (xs ++ eqs') = none := by grind [unifyList]
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hσ' : Subst.Unifies σ (xs ++ eqs') := by
        intro p hp
        rcases List.mem_append.mp hp with hp_xs | hp_eqs'
        · exact Signature.decomp_unifier_sound x y xs σ hdec hxy p hp_xs
        · exact hσ p (List.mem_cons_of_mem _ hp_eqs')
      exact ih σ hσ' heq
  | case10 x y eqs' hxv hyv hdec =>
      intro σ hσ _
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      exact Signature.decomp_none_no_unifier x y σ hxv hyv hdec hxy

/-! ## Public completeness. -/

/-- **Completeness of `unify`.** If *any* substitution unifies `eqs`, then `unify eqs` succeeds.

The witness is an arbitrary parallel `Subst α`, matching the textbook definition of a unifier
(any substitution σ with Eσ = Dσ). It used to be a list-form `Unifier α`, which forced callers
to convert — and an arbitrary `Subst α` cannot be converted: `Unifier.toSubst`'s image contains
only the acyclic substitutions, so e.g. the swap `{0 ↦ ?1, 1 ↦ ?0}` is not in it. The induction
never needed the list structure, only the action, which is why generalising the hypothesis was
the fix. -/
theorem unify_complete {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (σ : Subst α),
      Subst.Unifies σ eqs → unify eqs ≠ none := by
  intro eqs σ hσ heq
  rw [unify, Option.map_eq_none_iff] at heq
  exact unifyList_complete eqs σ hσ heq

/-- List-form corollary, for callers holding a `Unifier α` (e.g. the empty unifier for trivially
unifiable equations). This direction is the easy one — `toSubst` always exists. -/
theorem unify_complete_unifier {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (u : Unifier α),
      u.Unifies eqs → unify eqs ≠ none := by
  intro eqs u hu
  refine unify_complete eqs u.toSubst (fun p hp => ?_)
  have h := hu p hp
  rwa [Unifier.apply_eq_pSubst_toSubst, Unifier.apply_eq_pSubst_toSubst] at h
