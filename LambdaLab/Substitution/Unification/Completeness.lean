import LambdaLab.Substitution.Unification.Basic

/-! # Completeness of `unify` (Fin-form Term)

If any unifier exists for `eqs`, then `unify eqs` succeeds. -/

namespace LambdaLab.Substitution.Unification

theorem unify_complete {C : Type} [DecidableEq C] :
    ∀ (eqs : Equations C) (σ : Unifier C),
      σ.Unifies eqs → unify eqs ≠ none := by
  intro eqs
  induction eqs using unify.induct with
  | case1 => intro σ _ heq; rw [unify] at heq; cases heq
  | case2 x y eqs' m hxv hyv ih =>
      intro σ hσ heq
      rw [unify_cons_delete x y eqs' hxv hyv] at heq
      exact ih σ (fun p hp => hσ p (List.mem_cons_of_mem _ hp)) heq
  | case3 x y eqs' m hxv hyv hocc =>
      intro σ hσ _
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hxeq : x = .var m := Term.var_of_isVar x m hxv
      rw [hxeq] at hxy
      exact Unifier.occurs_no_unifier y m σ hocc hyv hxy
  | case4 x y eqs' m hxv hyv hocc rest hrest _ =>
      intro _ _ heq
      rw [unify_cons_elim_l_some x y eqs' hxv hyv hocc
        (by have h := hrest
            rw [unify_attach_map_single_eq] at h
            exact h)] at heq
      cases heq
  | case5 x y eqs' m hxv hyv hocc hnone ih =>
      intro σ hσ _
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hxeq : x = .var m := Term.var_of_isVar x m hxv
      rw [hxeq] at hxy
      have hσ_sub : σ.Unifies (eqs'.attach.map
          (fun (x : Subtype (Membership.mem eqs')) =>
            match x with | ⟨p, _⟩ => (Term.single p.1 m y, Term.single p.2 m y))) := by
        intro p hp
        simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hp
        obtain ⟨q, hq, hqeq⟩ := hp
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        rw [Unifier.absorb σ q.1 m y hxy, Unifier.absorb σ q.2 m y hxy]
        exact hq_unif
      exact ih σ hσ_sub hnone
  | case6 x y eqs' hxv m hyv hocc =>
      intro σ hσ _
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hyeq : y = .var m := Term.var_of_isVar y m hyv
      rw [hyeq] at hxy
      have hxv' : Term.isVar x ≠ some m := by rw [hxv]; intro h; cases h
      exact Unifier.occurs_no_unifier x m σ hocc hxv' hxy.symm
  | case7 x y eqs' hxv m hyv hocc rest hrest _ =>
      intro _ _ heq
      rw [unify_cons_elim_r_some x y eqs' hxv hyv hocc
        (by have h := hrest
            rw [unify_attach_map_single_eq] at h
            exact h)] at heq
      cases heq
  | case8 x y eqs' hxv m hyv hocc hnone ih =>
      intro σ hσ _
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hyeq : y = .var m := Term.var_of_isVar y m hyv
      rw [hyeq] at hxy
      have hxy' : σ.apply (.var m) = σ.apply x := hxy.symm
      have hσ_sub : σ.Unifies (eqs'.attach.map
          (fun (x' : Subtype (Membership.mem eqs')) =>
            match x' with | ⟨p, _⟩ => (Term.single p.1 m x, Term.single p.2 m x))) := by
        intro p hp
        simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hp
        obtain ⟨q, hq, hqeq⟩ := hp
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        rw [Unifier.absorb σ q.1 m x hxy', Unifier.absorb σ q.2 m x hxy']
        exact hq_unif
      exact ih σ hσ_sub hnone
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro σ hσ heq
      rw [unify_cons_decomp x y eqs' hxv hyv hdec] at heq
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hσ' : σ.Unifies (xs ++ eqs') := by
        intro p hp
        rcases List.mem_append.mp hp with hp_xs | hp_eqs'
        · exact Unifier.decomp_unifier_sound x y xs σ hdec hxy p hp_xs
        · exact hσ p (List.mem_cons_of_mem _ hp_eqs')
      exact ih σ hσ' heq
  | case10 x y eqs' hxv hyv hdec =>
      intro σ hσ _
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      exact Unifier.decomp_none_no_unifier x y σ hxv hyv hdec hxy

end LambdaLab.Substitution.Unification
