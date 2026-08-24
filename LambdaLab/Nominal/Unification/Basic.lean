import LambdaLab.Nominal.Unification.Bridge
import LambdaLab.Nominal.Unification.Measure

open LambdaLab.Nominal

/-! # The unification algorithm

Defines the Martelli–Montanari `unify` and its termination proof, on top
of the slim `Signature` typeclass. The four rules are: delete (var ≐
same var), variable elimination left/right (with occurs check), and
decomposition. Termination is by lexicographic decrease in
`(mvarCount, size)`, the same measure as `Unification/Basic.lean`. -/

set_option linter.unusedVariables false in
/-- The standard Martelli–Montanari unification algorithm. -/
def unifyList {A α : Type} [Atom A] [Signature A α] (eqs : Equations α) : Option (Unifier A α) :=
  match eqs with
  | [] => some []
  | (x, y) :: eqs' =>
      match hx : Signature.isVar x with
      | some n =>
          if Signature.isVar y = some n then
            unifyList eqs'
          else if Signature.occurs n y then
            none
          else
            match unifyList (HasSubst.single eqs' n y) with
            | some rest => some ((n, y) :: rest)
            | none => none
      | none =>
          match hy : Signature.isVar y with
          | some m =>
              if Signature.occurs m x then
                none
              else
                match unifyList (HasSubst.single eqs' m x) with
                | some rest => some ((m, x) :: rest)
                | none => none
          | none =>
              match hd : Signature.decomp x y with
              | some xs => unifyList (xs ++ eqs')
              | none => none
termination_by (eqs.mvarCount, eqs.size)
decreasing_by
  -- delete: x = var n, y = var n, recurse on eqs'
  · rename_i hy
    refine Prod.Lex.ofNat_le_lt (Equations.mvarCount_cons_le (x, y) eqs') ?_
    intro _
    rw [Equations.size_cons]
    have hxeq := Signature.var_of_isVar x n hx
    have hyeq := Signature.var_of_isVar y n hy
    show _ < Equations.size eqs' + Signature.size (x, y).1 + Signature.size (x, y).2
    rw [hxeq, hyeq, Signature.size_var]
    omega
  -- var-elim left: x = var n, ¬ occurs n y, recurse on single eqs' n y
  · rename_i hyne hocc
    have hocc' : ¬ HasVars.isFree y n := fun hf => hocc hf
    have hxeq : x = Signature.var n := Signature.var_of_isVar x n hx
    refine Prod.Lex.left _ _ ?_
    apply Equations.mvarCount_lt_of_isFree_subset_strict n
    · intro m ⟨p, hp_mem, hp_free⟩
      rcases List.mem_map.mp hp_mem with ⟨q, hq_mem, hq_eq⟩
      subst hq_eq
      have hpor : HasVars.isFree q.1 m ∨ HasVars.isFree q.2 m ∨ HasVars.isFree y m := by
        rcases hp_free with h1 | h2
        · rcases (Signature.single_isFree q.1 n y m).mp h1 with ⟨_, hfm⟩ | ⟨_, hym⟩
          · exact Or.inl hfm
          · exact Or.inr (Or.inr hym)
        · rcases (Signature.single_isFree q.2 n y m).mp h2 with ⟨_, hfm⟩ | ⟨_, hym⟩
          · exact Or.inr (Or.inl hfm)
          · exact Or.inr (Or.inr hym)
      rcases hpor with hq1 | hq2 | hy_m
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inl hq1⟩
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inr hq2⟩
      · exact ⟨(x, y), List.mem_cons_self, Or.inr hy_m⟩
    · intro ⟨p, hp_mem, hp_free⟩
      rcases List.mem_map.mp hp_mem with ⟨q, _, hq_eq⟩
      subst hq_eq
      rcases hp_free with h1 | h2
      · rcases (Signature.single_isFree q.1 n y n).mp h1 with ⟨hne, _⟩ | ⟨_, hyn⟩
        · exact hne rfl
        · exact hocc' hyn
      · rcases (Signature.single_isFree q.2 n y n).mp h2 with ⟨hne, _⟩ | ⟨_, hyn⟩
        · exact hne rfl
        · exact hocc' hyn
    · refine ⟨(x, y), List.mem_cons_self, Or.inl ?_⟩
      rw [hxeq]
      exact (Signature.var_isFree n n).mpr rfl
  -- var-elim right: y = var m, ¬ occurs m x, recurse on single eqs' m x
  · rename_i hocc
    have hocc' : ¬ HasVars.isFree x m := fun hf => hocc hf
    have hyeq : y = Signature.var m := Signature.var_of_isVar y m hy
    refine Prod.Lex.left _ _ ?_
    apply Equations.mvarCount_lt_of_isFree_subset_strict m
    · intro k ⟨p, hp_mem, hp_free⟩
      rcases List.mem_map.mp hp_mem with ⟨q, hq_mem, hq_eq⟩
      subst hq_eq
      have hpor : HasVars.isFree q.1 k ∨ HasVars.isFree q.2 k ∨ HasVars.isFree x k := by
        rcases hp_free with h1 | h2
        · rcases (Signature.single_isFree q.1 m x k).mp h1 with ⟨_, hfk⟩ | ⟨_, hxk⟩
          · exact Or.inl hfk
          · exact Or.inr (Or.inr hxk)
        · rcases (Signature.single_isFree q.2 m x k).mp h2 with ⟨_, hfk⟩ | ⟨_, hxk⟩
          · exact Or.inr (Or.inl hfk)
          · exact Or.inr (Or.inr hxk)
      rcases hpor with hq1 | hq2 | hx_k
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inl hq1⟩
      · exact ⟨q, List.mem_cons_of_mem _ hq_mem, Or.inr hq2⟩
      · exact ⟨(x, y), List.mem_cons_self, Or.inl hx_k⟩
    · intro ⟨p, hp_mem, hp_free⟩
      rcases List.mem_map.mp hp_mem with ⟨q, _, hq_eq⟩
      subst hq_eq
      rcases hp_free with h1 | h2
      · rcases (Signature.single_isFree q.1 m x m).mp h1 with ⟨hne, _⟩ | ⟨_, hxm⟩
        · exact hne rfl
        · exact hocc' hxm
      · rcases (Signature.single_isFree q.2 m x m).mp h2 with ⟨hne, _⟩ | ⟨_, hxm⟩
        · exact hne rfl
        · exact hocc' hxm
    · refine ⟨(x, y), List.mem_cons_self, Or.inr ?_⟩
      rw [hyeq]
      exact (Signature.var_isFree m m).mpr rfl
  -- decompose: decomp x y = some xs, recurse on xs ++ eqs'
  · refine Prod.Lex.ofNat_le_lt ?_ ?_
    · apply Equations.mvarCount_le_of_isFree_subset
      intro n ⟨p, hp_mem, hp_free⟩
      rcases List.mem_append.mp hp_mem with hp_in_xs | hp_in_eqs'
      · have hxs : HasVars.isFree xs n := ⟨p, hp_in_xs, hp_free⟩
        rcases Signature.decomp_isFree x y xs n hd hxs with hx_free | hy_free
        · exact ⟨(x, y), List.mem_cons_self, Or.inl hx_free⟩
        · exact ⟨(x, y), List.mem_cons_self, Or.inr hy_free⟩
      · exact ⟨p, List.mem_cons_of_mem _ hp_in_eqs', hp_free⟩
    · intro _
      rw [Equations.size_append, Equations.size_cons]
      have hsize : Equations.size xs < Signature.size x + Signature.size y :=
        Signature.size_decomp x y xs hd
      show _ < Equations.size eqs' + Signature.size x + Signature.size y
      omega

/-! ## Public interface: compressed `Subst A α` form.

`unifyList` returns the unifier as a `List (Nat × α)` to make the
algorithm's structure (and its proofs) easy to talk about. Callers
generally want a single parallel `Subst A α`, obtained by composing all
the bindings via `Unifier.toSubst`. -/

/-- Most-general unifier of `eqs` as a parallel `Subst A α`, or `none`
if no unifier exists. Wraps `unifyList` with `Unifier.toSubst`; see
`Unifier.apply_eq_pSubst_toSubst` for the semantic bridge. -/
def unify {A α : Type} [Atom A] [Signature A α] (eqs : Equations α) : Option (Subst A α) :=
  (unifyList eqs).map Unifier.toSubst

