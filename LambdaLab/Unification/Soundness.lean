import LambdaLab.Unification.Basic

/-! # Soundness of `unify`

When the algorithm succeeds, the returned unifier actually unifies every
equation. Carries over from the fat-typeclass world: the proof structure
is identical, but the bridge lemmas it appeals to are now theorems on the
slim typeclass (see `Unification/Bridge.lean`). -/

/-- **Soundness of `unify`.** When `unify eqs` returns `some u`, the
unifier `u` actually unifies every equation in `eqs`. Proved by
induction on `unify.induct`; failure branches dispatch by contradiction
with the `some u` hypothesis. -/
theorem unify_unifies {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (u : Unifier α),
      unify eqs = some u → u.Unifies eqs := by
  intro eqs
  induction eqs using unify.induct with
  | case1 =>
      intro u _ p hp
      cases hp
  | case2 x y eqs' m hxv hyv ih =>
      intro u hu p hp
      rw [unify_cons_delete x y eqs' hxv hyv] at hu
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        have hx := Signature.var_of_isVar x m hxv
        have hy := Signature.var_of_isVar y m hyv
        simp [hx, hy]
      · exact ih u hu p hp
  | case3 x y eqs' m hxv hyv hocc =>
      intro u hu _ _
      rw [unify_cons_occurs_l x y eqs' hxv hyv hocc] at hu
      cases hu
  | case4 x y eqs' m hxv hyv hocc rest hrest ih =>
      intro u hu p hp
      rw [unify_cons_elim_l_some x y eqs' hxv hyv hocc hrest] at hu
      have hueq : (m, y) :: rest = u := Option.some.inj hu
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
  | case5 x y eqs' m hxv hyv hocc hnone _ =>
      intro u hu _ _
      rw [unify_cons_elim_l_none x y eqs' hxv hyv hocc hnone] at hu
      cases hu
  | case6 x y eqs' hxv m hyv hocc =>
      intro u hu _ _
      rw [unify_cons_occurs_r x y eqs' hxv hyv hocc] at hu
      cases hu
  | case7 x y eqs' hxv m hyv hocc rest hrest ih =>
      intro u hu p hp
      rw [unify_cons_elim_r_some x y eqs' hxv hyv hocc hrest] at hu
      have hueq : (m, x) :: rest = u := Option.some.inj hu
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
  | case8 x y eqs' hxv m hyv hocc hnone _ =>
      intro u hu _ _
      rw [unify_cons_elim_r_none x y eqs' hxv hyv hocc hnone] at hu
      cases hu
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro u hu p hp
      rw [unify_cons_decomp x y eqs' hxv hyv hdec] at hu
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        apply Signature.decomp_apply_sound u x y xs hdec
        intro q hq
        exact ih u hu q (List.mem_append_left _ hq)
      · exact ih u hu p (List.mem_append_right _ hp)
  | case10 x y eqs' hxv hyv hdec =>
      intro u hu _ _
      rw [unify_cons_clash x y eqs' hxv hyv hdec] at hu
      cases hu
