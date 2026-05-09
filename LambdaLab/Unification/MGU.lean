import LambdaLab.Unification.Basic

/-! # Most-generality of `unify` (Fin-form Term)

When `unify` succeeds, the returned unifier is at least as general as
any other unifier of the same equation set. -/

namespace LambdaLab.Unification

namespace Unifier

/-- `Unifier.MoreGeneral u₁ u₂`: u₁ is at least as general as u₂ —
there exists τ such that applying u₂ is the same as applying u₁ then τ. -/
def MoreGeneral {C : Type} (u₁ u₂ : Unifier C) : Prop :=
  ∃ τ : Unifier C, ∀ t : Term C, u₂.apply t = τ.apply (u₁.apply t)

end Unifier

theorem unify_mgu {C : Type} [DecidableEq C] :
    ∀ (eqs : Equations C) (u : Unifier C),
      unify eqs = some u →
      ∀ (σ : Unifier C), σ.Unifies eqs →
      Unifier.MoreGeneral u σ := by
  intro eqs
  induction eqs using unify.induct with
  | case1 =>
      intro u hu σ _
      rw [unify] at hu
      have hueq : ([] : Unifier C) = u := Option.some.inj hu
      subst hueq
      exact ⟨σ, fun t => by simp [Unifier.apply]⟩
  | case2 x y eqs' m hxv hyv ih =>
      intro u hu σ hσ
      rw [unify_cons_delete x y eqs' hxv hyv] at hu
      exact ih u hu σ (fun p hp => hσ p (List.mem_cons_of_mem _ hp))
  | case3 x y eqs' m hxv hyv hocc =>
      intro u hu _ _
      rw [unify_cons_occurs_l x y eqs' hxv hyv hocc] at hu
      cases hu
  | case4 x y eqs' m hxv hyv hocc rest hrest ih =>
      intro u hu σ hσ
      have hrest' : unify (eqs'.map (fun p => (Term.single p.1 m y, Term.single p.2 m y))) =
          some rest := by
        have h := hrest
        rw [unify_attach_map_single_eq] at h
        exact h
      rw [unify_cons_elim_l_some x y eqs' hxv hyv hocc hrest'] at hu
      have hueq : (m, y) :: rest = u := Option.some.inj hu
      subst hueq
      have hxeq : x = .var m := Term.var_of_isVar x m hxv
      have hxy : σ.apply (.var m) = σ.apply y := hxeq ▸ hσ.head_eq
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
      obtain ⟨τ, hτ⟩ := ih rest hrest σ hσ_sub
      refine ⟨τ, fun t => ?_⟩
      have habs : σ.apply (Term.single t m y) = σ.apply t :=
        Unifier.absorb σ t m y hxy
      have hrec := hτ (Term.single t m y)
      simp only [Unifier.apply_cons]
      rw [← habs, hrec]
  | case5 x y eqs' m hxv hyv hocc hnone _ =>
      intro u hu _ _
      have hnone' : unify (eqs'.map (fun p => (Term.single p.1 m y, Term.single p.2 m y))) =
          none := by
        have h := hnone
        rw [unify_attach_map_single_eq] at h
        exact h
      rw [unify_cons_elim_l_none x y eqs' hxv hyv hocc hnone'] at hu
      cases hu
  | case6 x y eqs' hxv m hyv hocc =>
      intro u hu _ _
      rw [unify_cons_occurs_r x y eqs' hxv hyv hocc] at hu
      cases hu
  | case7 x y eqs' hxv m hyv hocc rest hrest ih =>
      intro u hu σ hσ
      have hrest' : unify (eqs'.map (fun p => (Term.single p.1 m x, Term.single p.2 m x))) =
          some rest := by
        have h := hrest
        rw [unify_attach_map_single_eq] at h
        exact h
      rw [unify_cons_elim_r_some x y eqs' hxv hyv hocc hrest'] at hu
      have hueq : (m, x) :: rest = u := Option.some.inj hu
      subst hueq
      have hyeq : y = .var m := Term.var_of_isVar y m hyv
      have hxy : σ.apply (.var m) = σ.apply x := (hyeq ▸ hσ.head_eq).symm
      have hσ_sub : σ.Unifies (eqs'.attach.map
          (fun (x' : Subtype (Membership.mem eqs')) =>
            match x' with | ⟨p, _⟩ => (Term.single p.1 m x, Term.single p.2 m x))) := by
        intro p hp
        simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hp
        obtain ⟨q, hq, hqeq⟩ := hp
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        rw [Unifier.absorb σ q.1 m x hxy, Unifier.absorb σ q.2 m x hxy]
        exact hq_unif
      obtain ⟨τ, hτ⟩ := ih rest hrest σ hσ_sub
      refine ⟨τ, fun t => ?_⟩
      have habs : σ.apply (Term.single t m x) = σ.apply t :=
        Unifier.absorb σ t m x hxy
      have hrec := hτ (Term.single t m x)
      simp only [Unifier.apply_cons]
      rw [← habs, hrec]
  | case8 x y eqs' hxv m hyv hocc hnone _ =>
      intro u hu _ _
      have hnone' : unify (eqs'.map (fun p => (Term.single p.1 m x, Term.single p.2 m x))) =
          none := by
        have h := hnone
        rw [unify_attach_map_single_eq] at h
        exact h
      rw [unify_cons_elim_r_none x y eqs' hxv hyv hocc hnone'] at hu
      cases hu
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro u hu σ hσ
      rw [unify_cons_decomp x y eqs' hxv hyv hdec] at hu
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hσ' : σ.Unifies (xs ++ eqs') := by
        intro p hp
        rcases List.mem_append.mp hp with hp_xs | hp_eqs'
        · exact Unifier.decomp_unifier_sound x y xs σ hdec hxy p hp_xs
        · exact hσ p (List.mem_cons_of_mem _ hp_eqs')
      exact ih u hu σ hσ'
  | case10 x y eqs' hxv hyv hdec =>
      intro u hu _ _
      rw [unify_cons_clash x y eqs' hxv hyv hdec] at hu
      cases hu

end LambdaLab.Unification
