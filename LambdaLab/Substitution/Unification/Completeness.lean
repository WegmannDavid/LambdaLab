import LambdaLab.Substitution.Unification.Basic

/-! # Completeness of `unify`

If any unifier exists, the algorithm succeeds. Carries over from the
fat-typeclass version on `archive/fat-unification`. -/

/-- **Completeness of `unify`.** If any unifier exists for `eqs`, then
`unify eqs` succeeds. Equivalently — and more usefully in this
contrapositive form — if `unify eqs = none`, no unifier exists. Proved by
induction on `unify.induct`: success branches close trivially; failure
branches each contradict the unifier-exists hypothesis using one of
`occurs_no_unifier`, `decomp_none_no_unifier`, or `unifier_absorb`. The
mechanical `unify` case-split is dispatched by `grind [unify]`. -/
theorem unify_complete {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (σ : Unifier α),
      σ.Unifies eqs → unify eqs ≠ none := by
  intro eqs
  induction eqs using unify.induct with
  | case1 => intro σ _ heq; rw [unify] at heq; cases heq
  | case2 x y eqs' m hxv hyv ih =>
      intro σ hσ heq
      have heq : unify eqs' = none := by grind [unify]
      exact ih σ (fun p hp => hσ p (List.mem_cons_of_mem _ hp)) heq
  | case3 x y eqs' m hxv hyv hocc =>
      intro σ hσ _
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hxeq : x = Signature.var m := Signature.var_of_isVar x m hxv
      rw [hxeq] at hxy
      exact Signature.occurs_no_unifier y m σ hocc hyv hxy
  | case4 _ _ _ _ _ _ _ _ _ _ => intro _ _ heq; grind [unify]
  | case5 x y eqs' m hxv hyv hocc hnone ih =>
      intro σ hσ _
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hxeq : x = Signature.var m := Signature.var_of_isVar x m hxv
      rw [hxeq] at hxy
      have hσ_sub : σ.Unifies (HasSubst.single eqs' m y) := by
        intro p hp
        rw [Equations.single_eq] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, hqeq⟩
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        rw [Signature.unifier_absorb σ q.1 m y hxy,
            Signature.unifier_absorb σ q.2 m y hxy]
        exact hq_unif
      exact ih σ hσ_sub hnone
  | case6 x y eqs' hxv m hyv hocc =>
      intro σ hσ _
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hyeq : y = Signature.var m := Signature.var_of_isVar y m hyv
      rw [hyeq] at hxy
      have hxv' : Signature.isVar x ≠ some m := by rw [hxv]; intro h; cases h
      exact Signature.occurs_no_unifier x m σ hocc hxv' hxy.symm
  | case7 _ _ _ _ _ _ _ _ _ _ => intro _ _ heq; grind [unify]
  | case8 x y eqs' hxv m hyv hocc hnone ih =>
      intro σ hσ _
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hyeq : y = Signature.var m := Signature.var_of_isVar y m hyv
      rw [hyeq] at hxy
      have hxy' : σ.apply (Signature.var m) = σ.apply x := hxy.symm
      have hσ_sub : σ.Unifies (HasSubst.single eqs' m x) := by
        intro p hp
        rw [Equations.single_eq] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, hqeq⟩
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        rw [Signature.unifier_absorb σ q.1 m x hxy',
            Signature.unifier_absorb σ q.2 m x hxy']
        exact hq_unif
      exact ih σ hσ_sub hnone
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro σ hσ heq
      have heq : unify (xs ++ eqs') = none := by grind [unify]
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hσ' : σ.Unifies (xs ++ eqs') := by
        intro p hp
        rcases List.mem_append.mp hp with hp_xs | hp_eqs'
        · exact Signature.decomp_unifier_sound x y xs σ hdec hxy p hp_xs
        · exact hσ p (List.mem_cons_of_mem _ hp_eqs')
      exact ih σ hσ' heq
  | case10 x y eqs' hxv hyv hdec =>
      intro σ hσ _
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      exact Signature.decomp_none_no_unifier x y σ hxv hyv hdec hxy
