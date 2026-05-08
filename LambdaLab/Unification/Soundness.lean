import LambdaLab.Unification.Basic

/-! # Soundness of `unify`

When the algorithm succeeds, the returned unifier actually unifies every
equation. -/

/-- **Soundness of `unify`.** When `unify eqs` returns `some u`, the
unifier `u` actually unifies every equation in `eqs`. Proved by induction
on `unify.induct`; failure branches are dispatched by contradiction with
the `some u` hypothesis. -/
theorem unify_unifies {α : Type} [Signature α] :
    ∀ (eqs : Equations α) (u : Unifier α),
      unify eqs = some u → ∀ p ∈ eqs, u.apply p.1 = u.apply p.2 := by
  intro eqs
  induction eqs using unify.induct with
  | case1 =>
      intro u hu p hp
      cases hp
  | case2 x y eqs' m hxv hyv ih =>
      intro u hu p hp
      have hbody : unify ((x, y) :: eqs') = unify eqs' := by
        rw [unify, hxv]; simp [hyv]
      rw [hbody] at hu
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        have hx := Signature.var_of_isVar x m hxv
        have hy := Signature.var_of_isVar y m hyv
        simp [hx, hy]
      · exact ih u hu p hp
  | case3 x y eqs' m hxv hyv hocc =>
      intro u hu _ _
      exfalso
      have hbody : unify ((x, y) :: eqs') = (none : Option (Unifier α)) := by
        rw [unify, hxv]; simp [hyv, hocc]
      rw [hbody] at hu
      cases hu
  | case4 x y eqs' m hxv hyv hocc rest hrest ih =>
      intro u hu p hp
      have hbody : unify ((x, y) :: eqs') = some ((m, y) :: rest) := by
        rw [unify, hxv]; simp [hyv, hocc, hrest]
      rw [hbody] at hu
      have hueq : (m, y) :: rest = u := Option.some.inj hu
      subst hueq
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        simp only [Unifier.apply_cons]
        have hx := Signature.var_of_isVar x m hxv
        have hsx : HasSubst.single x m y = y := by
          rw [hx]; exact Signature.pSubst_var_eq m y
        have hsy : HasSubst.single y m y = y := by
          apply Signature.single_off
          intro hfree
          have := (Signature.occurs_iff_isFree m y).mpr hfree
          exact hocc this
        rw [hsx, hsy]
      · simp only [Unifier.apply_cons]
        have hpsub : (HasSubst.single p.1 m y, HasSubst.single p.2 m y) ∈
            HasSubst.single eqs' m y := by
          rw [Equations.single_eq]
          exact List.mem_map_of_mem hp
        exact ih rest hrest _ hpsub
  | case5 x y eqs' m hxv hyv hocc hnone _ =>
      intro u hu _ _
      exfalso
      have hbody : unify ((x, y) :: eqs') = (none : Option (Unifier α)) := by
        rw [unify, hxv]; simp [hyv, hocc, hnone]
      rw [hbody] at hu
      cases hu
  | case6 x y eqs' hxv m hyv hocc =>
      intro u hu _ _
      exfalso
      have hbody : unify ((x, y) :: eqs') = (none : Option (Unifier α)) := by
        rw [unify, hxv, hyv]; simp [hocc]
      rw [hbody] at hu
      cases hu
  | case7 x y eqs' hxv m hyv hocc rest hrest ih =>
      intro u hu p hp
      have hbody : unify ((x, y) :: eqs') = some ((m, x) :: rest) := by
        rw [unify, hxv, hyv]; simp [hocc, hrest]
      rw [hbody] at hu
      have hueq : (m, x) :: rest = u := Option.some.inj hu
      subst hueq
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        simp only [Unifier.apply_cons]
        have hy := Signature.var_of_isVar y m hyv
        have hsx : HasSubst.single x m x = x := by
          apply Signature.single_off
          intro hfree
          have := (Signature.occurs_iff_isFree m x).mpr hfree
          exact hocc this
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
      exfalso
      have hbody : unify ((x, y) :: eqs') = (none : Option (Unifier α)) := by
        rw [unify, hxv, hyv]; simp [hocc, hnone]
      rw [hbody] at hu
      cases hu
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro u hu p hp
      have hbody : unify ((x, y) :: eqs') = unify (xs ++ eqs') := by
        rw [unify, hxv, hyv, hdec]
      rw [hbody] at hu
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        apply decomp_apply_sound u x y xs hdec
        intro q hq
        exact ih u hu q (List.mem_append_left _ hq)
      · exact ih u hu p (List.mem_append_right _ hp)
  | case10 x y eqs' hxv hyv hdec =>
      intro u hu _ _
      exfalso
      have hbody : unify ((x, y) :: eqs') = (none : Option (Unifier α)) := by
        rw [unify, hxv, hyv, hdec]
      rw [hbody] at hu
      cases hu
