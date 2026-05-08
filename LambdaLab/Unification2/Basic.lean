import LambdaLab.Unification2.Measure

/-! # The unification algorithm

Martelli–Montanari `unify` over the generic `Term C`. Termination: lex
`(mvarCount, size)` decrease. -/

namespace LambdaLab.Unification2

set_option linter.unusedVariables false in
/-- Standard Martelli–Montanari unification. -/
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
  · refine Prod.Lex.ofNat_le_lt (Equations.mvarCount_cons_le (x, y) eqs') ?_
    intro _
    rw [Equations.size_cons]
    show Equations.size eqs' < _
    omega
  -- var-elim left: recurse on substituted eqs'
  · rename_i hyne hocc
    have hx_isvar : Term.isVar x = some n := hx
    have hxeq : x = Term.var n := by
      cases x with
      | var m => simp [Term.isVar] at hx; rw [hx]
      | app _ _ => simp [Term.isVar] at hx
    refine Prod.Lex.left _ _ ?_
    apply Equations.mvarCount_lt_of_isFree_subset_strict n
    · intro m hm
      let p := hm.1
      have hp_mem : p ∈ eqs'.map (fun q => (Term.single q.1 n y, Term.single q.2 n y)) :=
        hm.2.1
      have hp_or := hm.2.2
      rw [List.mem_map] at hp_mem
      let q := hp_mem.choose
      have hq_mem : q ∈ eqs' := hp_mem.choose_spec.1
      have hq_eq : (Term.single q.1 n y, Term.single q.2 n y) = p := hp_mem.choose_spec.2
      subst hq_eq
      have hpor : Term.occurs m q.fst = true ∨ Term.occurs m q.snd = true ∨
                  Term.occurs m y = true := by
        rcases hp_or with h1 | h2
        · rcases (Term.single_isFree q.fst n y m).mp h1 with ⟨_, hfm⟩ | ⟨_, hym⟩
          · exact Or.inl hfm
          · exact Or.inr (Or.inr hym)
        · rcases (Term.single_isFree q.snd n y m).mp h2 with ⟨_, hfm⟩ | ⟨_, hym⟩
          · exact Or.inr (Or.inl hfm)
          · exact Or.inr (Or.inr hym)
      rcases hpor with hq1 | hq2 | hy_m
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inl hq1⟩
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inr hq2⟩
      · exact ⟨(x, y), List.mem_cons_self, Or.inr hy_m⟩
    · intro hex
      obtain ⟨p, hp_mem, hp_or⟩ := hex
      rw [List.mem_map] at hp_mem
      obtain ⟨(q : Equation C), _, hq_eq⟩ := hp_mem
      subst hq_eq
      have hocc' : ¬ Term.occurs n y = true := fun hf => hocc hf
      rcases hp_or with h1 | h2
      · rcases (Term.single_isFree q.fst n y n).mp h1 with ⟨hne, _⟩ | ⟨_, hyn⟩
        · exact hne rfl
        · exact hocc' hyn
      · rcases (Term.single_isFree q.snd n y n).mp h2 with ⟨hne, _⟩ | ⟨_, hyn⟩
        · exact hne rfl
        · exact hocc' hyn
    · refine ⟨(x, y), List.mem_cons_self, Or.inl ?_⟩
      rw [hxeq]
      simp [Term.occurs_var]
  -- var-elim right
  · rename_i hocc
    have hy_isvar : Term.isVar y = some m := hy
    have hyeq : y = Term.var m := by
      cases y with
      | var k => simp [Term.isVar] at hy; rw [hy]
      | app _ _ => simp [Term.isVar] at hy
    refine Prod.Lex.left _ _ ?_
    apply Equations.mvarCount_lt_of_isFree_subset_strict m
    · intro k hex; obtain ⟨p, hp_mem, hp_or⟩ := hex
      rw [List.mem_map] at hp_mem; obtain ⟨(q : Equation C), hq_mem, hq_eq⟩ := hp_mem
      subst hq_eq
      have hpor : Term.occurs k q.fst = true ∨ Term.occurs k q.snd = true ∨
                  Term.occurs k x = true := by
        rcases hp_or with h1 | h2
        · rcases (Term.single_isFree q.fst m x k).mp h1 with ⟨_, hfm⟩ | ⟨_, hxm⟩
          · exact Or.inl hfm
          · exact Or.inr (Or.inr hxm)
        · rcases (Term.single_isFree q.snd m x k).mp h2 with ⟨_, hfm⟩ | ⟨_, hxm⟩
          · exact Or.inr (Or.inl hfm)
          · exact Or.inr (Or.inr hxm)
      rcases hpor with hq1 | hq2 | hx_k
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inl hq1⟩
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inr hq2⟩
      · exact ⟨(x, y), List.mem_cons_self, Or.inl hx_k⟩
    · intro hex
      obtain ⟨p, hp_mem, hp_or⟩ := hex
      rw [List.mem_map] at hp_mem
      obtain ⟨(q : Equation C), _, hq_eq⟩ := hp_mem
      subst hq_eq
      have hocc' : ¬ Term.occurs m x = true := fun hf => hocc hf
      rcases hp_or with h1 | h2
      · rcases (Term.single_isFree q.fst m x m).mp h1 with ⟨hne, _⟩ | ⟨_, hxm⟩
        · exact hne rfl
        · exact hocc' hxm
      · rcases (Term.single_isFree q.snd m x m).mp h2 with ⟨hne, _⟩ | ⟨_, hxm⟩
        · exact hne rfl
        · exact hocc' hxm
    · refine ⟨(x, y), List.mem_cons_self, Or.inr ?_⟩
      rw [hyeq]
      simp [Term.occurs_var]
  -- decompose: decomp x y = some xs, recurse on xs ++ eqs'
  · refine Prod.Lex.ofNat_le_lt ?_ ?_
    · apply Equations.mvarCount_le_of_isFree_subset
      intro n ⟨p, hp_mem, hp_or⟩
      rcases List.mem_append.mp hp_mem with hp_in_xs | hp_in_eqs'
      · have hxs : ∃ q ∈ xs, Term.occurs n q.fst = true ∨ Term.occurs n q.snd = true :=
          ⟨p, hp_in_xs, hp_or⟩
        rcases Term.decomp_isFree x y xs n hd hxs with hx_free | hy_free
        · exact ⟨(x, y), List.mem_cons_self, Or.inl hx_free⟩
        · exact ⟨(x, y), List.mem_cons_self, Or.inr hy_free⟩
      · exact ⟨p, List.mem_cons_of_mem _ hp_in_eqs', hp_or⟩
    · intro _
      rw [Equations.size_append, Equations.size_cons]
      have hsize := Term.size_decomp x y xs hd
      show _ < _
      omega

end LambdaLab.Unification2
