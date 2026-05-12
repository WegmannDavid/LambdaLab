import LambdaLab.Substitution.Unification.Basic

/-! # Soundness of `unifyList`

When the algorithm succeeds, the returned unifier actually unifies every
equation. Carries over from the fat-typeclass world: the proof structure
is identical, but the bridge lemmas it appeals to are now theorems on the
slim typeclass (see `Unification/Bridge.lean`). -/

/-- **Soundness of `unifyList`.** When `unifyList eqs` returns `some u`, the
unifier `u` actually unifies every equation in `eqs`. Proved by
induction on `unifyList.induct`; failure branches close by contradiction
via `grind`. -/
theorem unifyList_unifies {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (u : Unifier α),
      unifyList eqs = some u → u.Unifies eqs := by
  intro eqs
  induction eqs using unifyList.induct with
  | case1 => intro u _ p hp; cases hp
  | case2 x y eqs' m hxv hyv ih =>
      intro u hu p hp
      have hu : unifyList eqs' = some u := by grind [unifyList]
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        have hx := Signature.var_of_isVar x m hxv
        have hy := Signature.var_of_isVar y m hyv
        simp [hx, hy]
      · exact ih u hu p hp
  | case3 _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case4 x y eqs' m hxv hyv hocc rest hrest ih =>
      intro u hu p hp
      have hueq : (m, y) :: rest = u := by grind [unifyList]
      subst hueq
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        simp only [Unifier.apply_cons]
        have hx := Signature.var_of_isVar x m hxv
        have hsx : HasSubst.single x m y = y := by
          rw [hx]; exact Signature.pSubst_var_eq m y
        have hsy : HasSubst.single y m y = y :=
          Signature.single_off y m y hocc
        rw [hsx, hsy]
      · simp only [Unifier.apply_cons]
        have hpsub : (HasSubst.single p.1 m y, HasSubst.single p.2 m y) ∈
            HasSubst.single eqs' m y := by
          rw [Equations.single_eq]
          exact List.mem_map_of_mem hp
        exact ih rest hrest _ hpsub
  | case5 _ _ _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case6 _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case7 x y eqs' hxv m hyv hocc rest hrest ih =>
      intro u hu p hp
      have hueq : (m, x) :: rest = u := by grind [unifyList]
      subst hueq
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        simp only [Unifier.apply_cons]
        have hy := Signature.var_of_isVar y m hyv
        have hsx : HasSubst.single x m x = x :=
          Signature.single_off x m x hocc
        have hsy : HasSubst.single y m x = x := by
          rw [hy]; exact Signature.pSubst_var_eq m x
        rw [hsx, hsy]
      · simp only [Unifier.apply_cons]
        have hpsub : (HasSubst.single p.1 m x, HasSubst.single p.2 m x) ∈
            HasSubst.single eqs' m x := by
          rw [Equations.single_eq]
          exact List.mem_map_of_mem hp
        exact ih rest hrest _ hpsub
  | case8 _ _ _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro u hu p hp
      have hu : unifyList (xs ++ eqs') = some u := by grind [unifyList]
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        apply Signature.decomp_apply_sound u x y xs hdec
        intro q hq
        exact ih u hu q (List.mem_append_left _ hq)
      · exact ih u hu p (List.mem_append_right _ hp)
  | case10 _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]

/-! ## Public, `Subst α`-form soundness. -/

/-- A `Subst α` unifies a set of equations in parallel form. -/
abbrev Subst.Unifies {α : Type} [Signature α]
    (σ : Subst α) (eqs : Equations α) : Prop :=
  ∀ p ∈ eqs, HasSubst.pSubst p.1 σ = HasSubst.pSubst p.2 σ

/-- **Soundness of `unify`.** When `unify eqs` returns `some σ`, the
returned `Subst α` makes every equation hold under parallel substitution.
Corollary of `unifyList_unifies` via `Unifier.apply_eq_pSubst_toSubst`. -/
theorem unify_unifies {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (σ : Subst α),
      unify eqs = some σ → σ.Unifies eqs := by
  intro eqs σ hu p hp
  rw [unify, Option.map_eq_some_iff] at hu
  obtain ⟨u, hul, rfl⟩ := hu
  rw [← Unifier.apply_eq_pSubst_toSubst,
      ← Unifier.apply_eq_pSubst_toSubst]
  exact unifyList_unifies eqs u hul p hp
