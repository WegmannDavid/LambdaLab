import LambdaLab.Substitution.Unification.Measure

/-! # The unification algorithm (Fin-function term form) -/

namespace LambdaLab.Substitution.Unification

set_option linter.unusedVariables false in
def unify {C : Type} [DecidableEq C] (eqs : Equations C) : Option (Unifier C) :=
  match eqs with
  | [] => some []
  | (x, y) :: eqs' =>
      match hx : Term.isVar x with
      | some n =>
          if Term.isVar y = some n then
            unify eqs'
          else if Term.occurs n y then
            none
          else
            match unify (eqs'.map fun p => (Term.single p.1 n y, Term.single p.2 n y)) with
            | some rest => some ((n, y) :: rest)
            | none => none
      | none =>
          match hy : Term.isVar y with
          | some m =>
              if Term.occurs m x then
                none
              else
                match unify (eqs'.map fun p => (Term.single p.1 m x, Term.single p.2 m x)) with
                | some rest => some ((m, x) :: rest)
                | none => none
          | none =>
              match hd : Term.decomp x y with
              | some xs => unify (xs ++ eqs')
              | none => none
termination_by (eqs.mvarCount, eqs.size)
decreasing_by
  -- delete: x = var n, y = var n, recurse on eqs'
  · rename_i hy_eq
    refine Prod.Lex.ofNat_le_lt (Equations.mvarCount_cons_le (x, y) eqs') ?_
    intro _
    rw [Equations.size_cons]
    show Equations.size eqs' < _
    have hx_var : x = .var n := by
      cases x with
      | var k => simp [Term.isVar] at hx; rw [hx]
      | app _ _ _ => simp [Term.isVar] at hx
    have hy_var' : y = .var n := by
      cases y with
      | var k => simp [Term.isVar] at hy_eq; rw [hy_eq]
      | app _ _ _ => simp [Term.isVar] at hy_eq
    rw [hx_var, hy_var']
    show Equations.size eqs' < Equations.size eqs' + 1 + 1
    omega
  -- var-elim left
  · rename_i hyne hocc
    have hxeq : x = Term.var n := by
      cases x with
      | var k => simp [Term.isVar] at hx; rw [hx]
      | app _ _ _ => simp [Term.isVar] at hx
    refine Prod.Lex.left _ _ ?_
    apply Equations.mvarCount_lt_of_isFree_subset_strict n
    · intro m hm
      obtain ⟨p, hp_mem, hp_or⟩ := hm
      -- termination context: hp_mem uses eqs'.attach. Extract the underlying value.
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hp_mem
      obtain ⟨q, hq_mem, hq_eq⟩ := hp_mem
      subst hq_eq
      have hpor : Term.occurs m q.1 = true ∨ Term.occurs m q.2 = true ∨
                  Term.occurs m y = true := by
        rcases hp_or with h1 | h2
        · rcases (Term.single_isFree q.1 n y m).mp h1 with ⟨_, hfm⟩ | ⟨_, hym⟩
          · exact Or.inl hfm
          · exact Or.inr (Or.inr hym)
        · rcases (Term.single_isFree q.2 n y m).mp h2 with ⟨_, hfm⟩ | ⟨_, hym⟩
          · exact Or.inr (Or.inl hfm)
          · exact Or.inr (Or.inr hym)
      rcases hpor with hq1 | hq2 | hy_m
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inl hq1⟩
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inr hq2⟩
      · exact ⟨(x, y), List.mem_cons_self, Or.inr hy_m⟩
    · intro hex
      obtain ⟨p, hp_mem, hp_or⟩ := hex
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hp_mem
      obtain ⟨q, _, hq_eq⟩ := hp_mem
      subst hq_eq
      have hocc' : ¬ Term.occurs n y = true := fun hf => hocc hf
      rcases hp_or with h1 | h2
      · rcases (Term.single_isFree q.1 n y n).mp h1 with ⟨hne, _⟩ | ⟨_, hyn⟩
        · exact hne rfl
        · exact hocc' hyn
      · rcases (Term.single_isFree q.2 n y n).mp h2 with ⟨hne, _⟩ | ⟨_, hyn⟩
        · exact hne rfl
        · exact hocc' hyn
    · refine ⟨(x, y), List.mem_cons_self, Or.inl ?_⟩
      rw [hxeq]
      simp [Term.occurs_var]
  -- var-elim right
  · rename_i hocc
    have hyeq : y = Term.var m := by
      cases y with
      | var k => simp [Term.isVar] at hy; rw [hy]
      | app _ _ _ => simp [Term.isVar] at hy
    refine Prod.Lex.left _ _ ?_
    apply Equations.mvarCount_lt_of_isFree_subset_strict m
    · intro k hex
      obtain ⟨p, hp_mem, hp_or⟩ := hex
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hp_mem
      obtain ⟨q, hq_mem, hq_eq⟩ := hp_mem
      subst hq_eq
      have hpor : Term.occurs k q.1 = true ∨ Term.occurs k q.2 = true ∨
                  Term.occurs k x = true := by
        rcases hp_or with h1 | h2
        · rcases (Term.single_isFree q.1 m x k).mp h1 with ⟨_, hfm⟩ | ⟨_, hxm⟩
          · exact Or.inl hfm
          · exact Or.inr (Or.inr hxm)
        · rcases (Term.single_isFree q.2 m x k).mp h2 with ⟨_, hfm⟩ | ⟨_, hxm⟩
          · exact Or.inr (Or.inl hfm)
          · exact Or.inr (Or.inr hxm)
      rcases hpor with hq1 | hq2 | hx_k
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inl hq1⟩
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inr hq2⟩
      · exact ⟨(x, y), List.mem_cons_self, Or.inl hx_k⟩
    · intro hex
      obtain ⟨p, hp_mem, hp_or⟩ := hex
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hp_mem
      obtain ⟨q, _, hq_eq⟩ := hp_mem
      subst hq_eq
      have hocc' : ¬ Term.occurs m x = true := fun hf => hocc hf
      rcases hp_or with h1 | h2
      · rcases (Term.single_isFree q.1 m x m).mp h1 with ⟨hne, _⟩ | ⟨_, hxm⟩
        · exact hne rfl
        · exact hocc' hxm
      · rcases (Term.single_isFree q.2 m x m).mp h2 with ⟨hne, _⟩ | ⟨_, hxm⟩
        · exact hne rfl
        · exact hocc' hxm
    · refine ⟨(x, y), List.mem_cons_self, Or.inr ?_⟩
      rw [hyeq]
      simp [Term.occurs_var]
  -- decompose
  · refine Prod.Lex.ofNat_le_lt ?_ ?_
    · apply Equations.mvarCount_le_of_isFree_subset
      intro n hex
      obtain ⟨p, hp_mem, hp_or⟩ := hex
      rcases List.mem_append.mp hp_mem with hp_in_xs | hp_in_eqs'
      · have hxs : ∃ q ∈ xs, Term.occurs n q.1 = true ∨ Term.occurs n q.2 = true :=
          ⟨p, hp_in_xs, hp_or⟩
        rcases Term.decomp_isFree x y xs n hd hxs with hx_free | hy_free
        · exact ⟨(x, y), List.mem_cons_self, Or.inl hx_free⟩
        · exact ⟨(x, y), List.mem_cons_self, Or.inr hy_free⟩
      · exact ⟨p, List.mem_cons_of_mem _ hp_in_eqs', hp_or⟩
    · intro _
      rw [Equations.size_append, Equations.size_cons]
      have hsize := Term.size_decomp x y xs hd
      have heq : Equations.size xs =
          xs.foldr (fun p acc => acc + Term.size p.1 + Term.size p.2) 0 := rfl
      rw [heq]
      show xs.foldr _ 0 + Equations.size eqs' <
        Equations.size eqs' + Term.size x + Term.size y
      omega

/-! ## Step lemmas: one-shot unfold for each branch of `unify` on cons. -/

variable {C : Type} [DecidableEq C]

theorem unify_cons_delete (x y : Term C) (eqs' : Equations C) {n : Nat}
    (hxv : Term.isVar x = some n) (hyv : Term.isVar y = some n) :
    unify ((x, y) :: eqs') = unify eqs' := by
  rw [unify, hxv]; simp [hyv]

theorem unify_cons_occurs_l (x y : Term C) (eqs' : Equations C) {n : Nat}
    (hxv : Term.isVar x = some n) (hyv : ¬ Term.isVar y = some n)
    (hocc : Term.occurs n y = true) :
    unify ((x, y) :: eqs') = none := by
  rw [unify, hxv]; simp [hyv, hocc]

theorem unify_cons_elim_l_some (x y : Term C) (eqs' : Equations C) {n : Nat}
    {rest : Unifier C}
    (hxv : Term.isVar x = some n) (hyv : ¬ Term.isVar y = some n)
    (hocc : ¬ Term.occurs n y = true)
    (hrest : unify (eqs'.map (fun p => (Term.single p.1 n y, Term.single p.2 n y)))
             = some rest) :
    unify ((x, y) :: eqs') = some ((n, y) :: rest) := by
  rw [unify, hxv]; simp [hyv, hocc, hrest]

theorem unify_cons_elim_l_none (x y : Term C) (eqs' : Equations C) {n : Nat}
    (hxv : Term.isVar x = some n) (hyv : ¬ Term.isVar y = some n)
    (hocc : ¬ Term.occurs n y = true)
    (hnone : unify (eqs'.map (fun p => (Term.single p.1 n y, Term.single p.2 n y)))
             = none) :
    unify ((x, y) :: eqs') = none := by
  rw [unify, hxv]; simp [hyv, hocc, hnone]

theorem unify_cons_occurs_r (x y : Term C) (eqs' : Equations C) {m : Nat}
    (hxv : Term.isVar x = none) (hyv : Term.isVar y = some m)
    (hocc : Term.occurs m x = true) :
    unify ((x, y) :: eqs') = none := by
  rw [unify, hxv, hyv]; simp [hocc]

theorem unify_cons_elim_r_some (x y : Term C) (eqs' : Equations C) {m : Nat}
    {rest : Unifier C}
    (hxv : Term.isVar x = none) (hyv : Term.isVar y = some m)
    (hocc : ¬ Term.occurs m x = true)
    (hrest : unify (eqs'.map (fun p => (Term.single p.1 m x, Term.single p.2 m x)))
             = some rest) :
    unify ((x, y) :: eqs') = some ((m, x) :: rest) := by
  rw [unify, hxv, hyv]; simp [hocc, hrest]

theorem unify_cons_elim_r_none (x y : Term C) (eqs' : Equations C) {m : Nat}
    (hxv : Term.isVar x = none) (hyv : Term.isVar y = some m)
    (hocc : ¬ Term.occurs m x = true)
    (hnone : unify (eqs'.map (fun p => (Term.single p.1 m x, Term.single p.2 m x)))
             = none) :
    unify ((x, y) :: eqs') = none := by
  rw [unify, hxv, hyv]; simp [hocc, hnone]

theorem unify_cons_decomp (x y : Term C) (eqs' : Equations C) {xs : Equations C}
    (hxv : Term.isVar x = none) (hyv : Term.isVar y = none)
    (hd : Term.decomp x y = some xs) :
    unify ((x, y) :: eqs') = unify (xs ++ eqs') := by
  rw [unify, hxv, hyv, hd]

theorem unify_cons_clash (x y : Term C) (eqs' : Equations C)
    (hxv : Term.isVar x = none) (hyv : Term.isVar y = none)
    (hd : Term.decomp x y = none) :
    unify ((x, y) :: eqs') = none := by
  rw [unify, hxv, hyv, hd]

end LambdaLab.Substitution.Unification
