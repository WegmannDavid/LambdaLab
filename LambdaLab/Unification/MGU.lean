import LambdaLab.Unification.Basic

/-! # Most-generality of `unify`

When `unify` succeeds, the returned unifier is at least as general as
any other unifier of the same equation set. -/

namespace Unifier

/-- `Unifier.MoreGeneral u₁ u₂` says `u₁` is at least as general as `u₂`:
there exists `τ` such that, on every term, applying `u₂` is the same as
applying `u₁` then `τ`. -/
def MoreGeneral {α : Type} [Signature α] (u₁ u₂ : Unifier α) : Prop :=
  ∃ τ : Unifier α, ∀ t : α, u₂.apply t = τ.apply (u₁.apply t)

end Unifier

/-- **Most-generality of `unify`.** When `unify eqs = some u`, `u` is at
least as general as any other unifier of `eqs`. Proved by induction on
`unify.induct`, using `Signature.unifier_absorb` in the var-elim cases
and `Signature.decomp_unifier_sound` in the decompose case. -/
theorem unify_mgu {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (u : Unifier α),
      unify eqs = some u →
      ∀ (σ : Unifier α), σ.Unifies eqs →
      Unifier.MoreGeneral u σ := by
  intro eqs
  induction eqs using unify.induct with
  | case1 =>
      intro u hu σ _
      have hueq : ([] : Unifier α) = u := by grind [unify]
      subst hueq
      exact ⟨σ, fun t => by simp [Unifier.apply]⟩
  | case2 x y eqs' m hxv hyv ih =>
      intro u hu σ hσ
      have hu : unify eqs' = some u := by grind [unify]
      exact ih u hu σ (fun p hp => hσ p (List.mem_cons_of_mem _ hp))
  | case3 _ _ _ _ _ _ _ => intro u hu _ _; grind [unify]
  | case4 x y eqs' m hxv hyv hocc rest hrest ih =>
      intro u hu σ hσ
      have hueq : (m, y) :: rest = u := by grind [unify]
      subst hueq
      have hxeq : x = Signature.var m := Signature.var_of_isVar x m hxv
      have hxy : σ.apply (Signature.var m) = σ.apply y := hxeq ▸ hσ.head_eq
      have hσ_sub : σ.Unifies (HasSubst.single eqs' m y) := by
        intro p hp
        rw [Equations.single_eq] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, hqeq⟩
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        rw [Signature.unifier_absorb σ q.1 m y hxy,
            Signature.unifier_absorb σ q.2 m y hxy]
        exact hq_unif
      obtain ⟨τ, hτ⟩ := ih rest hrest σ hσ_sub
      refine ⟨τ, fun t => ?_⟩
      have habs : σ.apply (HasSubst.single t m y) = σ.apply t :=
        Signature.unifier_absorb σ t m y hxy
      have hrec := hτ (HasSubst.single t m y)
      simp only [Unifier.apply_cons]
      rw [← habs, hrec]
  | case5 _ _ _ _ _ _ _ _ _ => intro u hu _ _; grind [unify]
  | case6 _ _ _ _ _ _ _ => intro u hu _ _; grind [unify]
  | case7 x y eqs' hxv m hyv hocc rest hrest ih =>
      intro u hu σ hσ
      have hueq : (m, x) :: rest = u := by grind [unify]
      subst hueq
      have hyeq : y = Signature.var m := Signature.var_of_isVar y m hyv
      have hxy : σ.apply (Signature.var m) = σ.apply x := (hyeq ▸ hσ.head_eq).symm
      have hσ_sub : σ.Unifies (HasSubst.single eqs' m x) := by
        intro p hp
        rw [Equations.single_eq] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, hqeq⟩
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        rw [Signature.unifier_absorb σ q.1 m x hxy,
            Signature.unifier_absorb σ q.2 m x hxy]
        exact hq_unif
      obtain ⟨τ, hτ⟩ := ih rest hrest σ hσ_sub
      refine ⟨τ, fun t => ?_⟩
      have habs : σ.apply (HasSubst.single t m x) = σ.apply t :=
        Signature.unifier_absorb σ t m x hxy
      have hrec := hτ (HasSubst.single t m x)
      simp only [Unifier.apply_cons]
      rw [← habs, hrec]
  | case8 _ _ _ _ _ _ _ _ _ => intro u hu _ _; grind [unify]
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro u hu σ hσ
      have hu : unify (xs ++ eqs') = some u := by grind [unify]
      have hxy : σ.apply x = σ.apply y := hσ.head_eq
      have hσ' : σ.Unifies (xs ++ eqs') := by
        intro p hp
        rcases List.mem_append.mp hp with hp_xs | hp_eqs'
        · exact Signature.decomp_unifier_sound x y xs σ hdec hxy p hp_xs
        · exact hσ p (List.mem_cons_of_mem _ hp_eqs')
      exact ih u hu σ hσ'
  | case10 _ _ _ _ _ _ => intro u hu _ _; grind [unify]
