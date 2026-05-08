import LambdaLab.Unification2.Basic

/-! # Soundness of `unify` (Fin-form Term) -/

namespace LambdaLab.Unification2

theorem unify_unifies {C : Type} [DecidableEq C] :
    ∀ (eqs : Equations C) (u : Unifier C),
      unify eqs = some u → u.Unifies eqs := by
  intro eqs
  induction eqs using unify.induct with
  | case1 => intro u _ p hp; cases hp
  | case2 x y eqs' m hxv hyv ih =>
      intro u hu p hp
      rw [unify_cons_delete x y eqs' hxv hyv] at hu
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        have hx := Term.var_of_isVar x m hxv
        have hy := Term.var_of_isVar y m hyv
        simp [hx, hy]
      · exact ih u hu p hp
  | case3 x y eqs' m hxv hyv hocc =>
      intro u hu _ _
      rw [unify_cons_occurs_l x y eqs' hxv hyv hocc] at hu
      cases hu
  | case4 x y eqs' m hxv hyv hocc rest hrest ih =>
      intro u hu p hp
      have hrest' : unify (eqs'.map (fun p => (Term.single p.1 m y, Term.single p.2 m y))) =
          some rest := by
        have : eqs'.attach.map (fun (x : Subtype (Membership.mem eqs')) =>
            (Term.single x.val.1 m y, Term.single x.val.2 m y)) =
          eqs'.map (fun p => (Term.single p.1 m y, Term.single p.2 m y)) := by simp
        rw [this] at hrest; exact hrest
      rw [unify_cons_elim_l_some x y eqs' hxv hyv hocc hrest'] at hu
      have hueq : (m, y) :: rest = u := Option.some.inj hu
      subst hueq
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        simp only [Unifier.apply_cons]
        have hx := Term.var_of_isVar x m hxv
        have hsx : Term.single x m y = y := by
          rw [hx]; exact Term.pSubst_var_eq m y
        have hsy : Term.single y m y = y :=
          Term.single_off y m y (by
            cases hb : Term.occurs m y
            · rfl
            · exact absurd hb hocc)
        rw [hsx, hsy]
      · simp only [Unifier.apply_cons]
        apply ih rest hrest
        simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
        exact ⟨p, hp, rfl⟩
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
        have hy := Term.var_of_isVar y m hyv
        have hsx : Term.single x m x = x :=
          Term.single_off x m x (by
            cases hb : Term.occurs m x
            · rfl
            · exact absurd hb hocc)
        have hsy : Term.single y m x = x := by
          rw [hy]; exact Term.pSubst_var_eq m x
        rw [hsx, hsy]
      · simp only [Unifier.apply_cons]
        apply ih rest hrest
        simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
        exact ⟨p, hp, rfl⟩
  | case8 x y eqs' hxv m hyv hocc hnone _ =>
      intro u hu _ _
      rw [unify_cons_elim_r_none x y eqs' hxv hyv hocc hnone] at hu
      cases hu
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro u hu p hp
      rw [unify_cons_decomp x y eqs' hxv hyv hdec] at hu
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        apply Unifier.decomp_apply_sound u x y xs hdec
        intro q hq
        exact ih u hu q (List.mem_append_left _ hq)
      · exact ih u hu p (List.mem_append_right _ hp)
  | case10 x y eqs' hxv hyv hdec =>
      intro u hu _ _
      rw [unify_cons_clash x y eqs' hxv hyv hdec] at hu
      cases hu

end LambdaLab.Unification2
