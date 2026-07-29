import LambdaLab.Substitution.Unification.Basic
import LambdaLab.Substitution.Unification.Soundness
import LambdaLab.Substitution.Unification.Completeness

/-! # Most-generality of `unifyList`

When `unifyList` succeeds, the returned unifier is at least as general as any other unifier of
the same equation set — where "unifier" means *any* substitution making the equations hold, as in
the standard definition, not merely one in the algorithm's own list format.

Generality is measured by `MoreGeneral` on `Subst α` (`Substitution/Basic.lean`). A list-form
counterpart was dropped: the algorithm's output converts to a `Subst` via `toSubst`, and the
hypothetical unifier is a `Subst` to begin with, so nothing needs the list-level notion. -/

/-- **Most-generality of `unifyList`.** When `unifyList eqs = some u`, `u` is at
least as general as any other unifier of `eqs`. Proved by induction on
`unifyList.induct`, using `Signature.unifier_absorb` in the var-elim cases
and `Signature.decomp_unifier_sound` in the decompose case. -/
theorem unifyList_mgu {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (u : Unifier α),
      unifyList eqs = some u →
      ∀ (σ : Subst α), Subst.Unifies σ eqs →
      MoreGeneral u.toSubst σ := by
  intro eqs
  induction eqs using unifyList.induct with
  | case1 =>
      intro u hu σ _
      have hueq : ([] : Unifier α) = u := by grind [unifyList]
      subst hueq
      exact ⟨σ, fun t => by simp [Unifier.toSubst_nil, Signature.hasSubst_pSubst_eq,
        Signature.pSubst_empty]⟩
  | case2 x y eqs' m hxv hyv ih =>
      intro u hu σ hσ
      have hu : unifyList eqs' = some u := by grind [unifyList]
      exact ih u hu σ (fun p hp => hσ p (List.mem_cons_of_mem _ hp))
  | case3 _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case4 x y eqs' m hxv hyv hocc rest hrest ih =>
      intro u hu σ hσ
      have hueq : (m, y) :: rest = u := by grind [unifyList]
      subst hueq
      have hxeq : x = Signature.var m := Signature.var_of_isVar x m hxv
      have hxy : Signature.pSubst (Signature.var m) σ = Signature.pSubst y σ := hxeq ▸ Subst.Unifies.head_eq hσ
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
      obtain ⟨τ, hτ⟩ := ih rest hrest σ hσ_sub
      refine ⟨τ, fun t => ?_⟩
      have habs : HasSubst.pSubst (HasSubst.single t m y) σ = HasSubst.pSubst t σ :=
        Signature.unifier_absorb σ t m y hxy
      have hrec := hτ (HasSubst.single t m y)
      rw [Unifier.toSubst_cons_pSubst, ← habs]
      exact hrec
  | case5 _ _ _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case6 _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case7 x y eqs' hxv m hyv hocc rest hrest ih =>
      intro u hu σ hσ
      have hueq : (m, x) :: rest = u := by grind [unifyList]
      subst hueq
      have hyeq : y = Signature.var m := Signature.var_of_isVar y m hyv
      have hxy : Signature.pSubst (Signature.var m) σ = Signature.pSubst x σ := (hyeq ▸ Subst.Unifies.head_eq hσ).symm
      have hσ_sub : Subst.Unifies σ (HasSubst.single eqs' m x) := by
        intro p hp
        rw [Equations.single_eq] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, hqeq⟩
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        simp only [Signature.hasSubst_pSubst_eq]
        rw [Signature.unifier_absorb σ q.1 m x hxy,
            Signature.unifier_absorb σ q.2 m x hxy]
        exact hq_unif
      obtain ⟨τ, hτ⟩ := ih rest hrest σ hσ_sub
      refine ⟨τ, fun t => ?_⟩
      have habs : HasSubst.pSubst (HasSubst.single t m x) σ = HasSubst.pSubst t σ :=
        Signature.unifier_absorb σ t m x hxy
      have hrec := hτ (HasSubst.single t m x)
      rw [Unifier.toSubst_cons_pSubst, ← habs]
      exact hrec
  | case8 _ _ _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro u hu σ hσ
      have hu : unifyList (xs ++ eqs') = some u := by grind [unifyList]
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hσ' : Subst.Unifies σ (xs ++ eqs') := by
        intro p hp
        rcases List.mem_append.mp hp with hp_xs | hp_eqs'
        · exact Signature.decomp_unifier_sound x y xs σ hdec hxy p hp_xs
        · exact hσ p (List.mem_cons_of_mem _ hp_eqs')
      exact ih u hu σ hσ'
  | case10 _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]

/-! ## Public MGU.

Both `unify_complete` (in `Completeness.lean`) and `unify_mgu` now quantify over an arbitrary
parallel `Subst α`, which is the textbook notion of a unifier — any substitution making the
equations hold. There used to be a `Subst`→`Unifier` bridge here, `exists_equivalent_unifier`,
turning an arbitrary parallel substitution into a list with the same action. **That is
impossible**: `Unifier.toSubst` collapses a list by pushing the tail into each value, so its
image consists only of acyclic substitutions, and a cyclic one like `{0 ↦ ?1, 1 ↦ ?0}` has no
preimage. Since the inductions only ever used the *action* of the hypothetical unifier and never
its list structure, generalising them was both possible and simpler.
-/

/-- **Most-generality of `unify`.** When `unify eqs = some σ`, `σ` is at least as general as any
substitution unifying `eqs`. -/
theorem unify_mgu {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (σ : Subst α),
      unify eqs = some σ →
      ∀ (σ' : Subst α), Subst.Unifies σ' eqs →
      MoreGeneral σ σ' := by
  intro eqs σ hu σ' hσ'
  rw [unify, Option.map_eq_some_iff] at hu
  obtain ⟨u₁, hul, rfl⟩ := hu
  exact unifyList_mgu eqs u₁ hul σ' hσ'

/-- List-form corollary, mirroring `unify_complete_unifier`. -/
theorem unify_mgu_unifier {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (σ : Subst α),
      unify eqs = some σ →
      ∀ (u : Unifier α), u.Unifies eqs →
      MoreGeneral σ u.toSubst := by
  intro eqs σ hu u hunif
  refine unify_mgu eqs σ hu u.toSubst (fun p hp => ?_)
  have h := hunif p hp
  rwa [Unifier.apply_eq_pSubst_toSubst, Unifier.apply_eq_pSubst_toSubst] at h
