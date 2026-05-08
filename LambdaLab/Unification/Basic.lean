import LambdaLab.Unification.Measure

/-! # The unification algorithm

Defines the Martelli–Montanari `unify`, its termination proof, and the
`Unifier.apply` operation along with the small set of bridge lemmas
shared by the soundness, MGU, and completeness proofs. -/

/-- The standard Martelli–Montanari unification algorithm. The four
rules are: delete (var ≐ same var), variable elimination (with occurs
check), and decomposition. Termination is by lexicographic decrease in
`(mvarCount, size)`. -/
def unify {α : Type} [Signature α] (eqs : Equations α) : Option (Unifier α) :=
  match eqs with
  | [] => some []
  | (x, y) :: eqs' =>
      match hx : Signature.isVar x with
      | some n =>
          if Signature.isVar y = some n then
            unify eqs'
          else if Signature.occurs n y then
            none
          else
            match unify (HasSubst.single eqs' n y) with
            | some rest => some ((n, y) :: rest)
            | none => none
      | none =>
          match hy : Signature.isVar y with
          | some m =>
              if Signature.occurs m x then
                none
              else
                match unify (HasSubst.single eqs' m x) with
                | some rest => some ((m, x) :: rest)
                | none => none
          | none =>
              match hd : Signature.decomp x y with
              | some xs => unify (xs ++ eqs')
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
    have hocc' : ¬ HasVars.isFree y n := by
      intro hf
      exact hocc ((Signature.occurs_iff_isFree n y).mpr hf)
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
    have hocc' : ¬ HasVars.isFree x m := by
      intro hf
      exact hocc ((Signature.occurs_iff_isFree m x).mpr hf)
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
      simp only [Prod.fst, Prod.snd]
      omega

/-! ## Unifier application -/

namespace Unifier

/-- Apply a unifier to a term: each `(n, s)` binding is applied as a
single substitution, in order from the head. -/
def apply {α : Type} [Signature α] (u : Unifier α) (t : α) : α :=
  u.foldl (fun acc p => HasSubst.single acc p.1 p.2) t

@[simp] theorem apply_nil {α : Type} [Signature α] (t : α) :
    apply [] t = t := rfl

@[simp] theorem apply_cons {α : Type} [Signature α] (n : Nat) (s : α)
    (rest : Unifier α) (t : α) :
    apply ((n, s) :: rest) t = apply rest (HasSubst.single t n s) := rfl

@[simp] theorem apply_append {α : Type} [Signature α]
    (u₁ u₂ : Unifier α) (t : α) :
    (u₁ ++ u₂).apply t = u₂.apply (u₁.apply t) := by
  show List.foldl _ _ _ = _
  rw [List.foldl_append]
  rfl

end Unifier

/-- A unifier (in the algebraic sense) of an equation set: makes every
equation true under `Unifier.apply`. -/
abbrev Unifier.Unifies {α : Type} [Signature α]
    (σ : Unifier α) (eqs : Equations α) : Prop :=
  ∀ p ∈ eqs, σ.apply p.1 = σ.apply p.2

/-! ## Bridge lemmas

The two `unifier_*` axioms in `Signature` are stated in `foldl` form so
that they don't require `Unifier.apply` to be defined yet. These thin
wrappers rephrase them in terms of `Unifier.apply` for use by the
soundness, MGU, and completeness proofs. -/

/-- Substitution on an equation set is pointwise on each component. -/
theorem Equations.single_eq {α : Type} [Signature α]
    (eqs : Equations α) (n : Nat) (s : α) :
    HasSubst.single eqs n s =
      eqs.map (fun p => (HasSubst.single p.1 n s, HasSubst.single p.2 n s)) :=
  rfl

/-- Absorption rephrased for `Unifier.apply` directly. -/
theorem unifier_apply_absorb {α : Type} [Signature α]
    (σ : Unifier α) (t : α) (n : Nat) (s : α)
    (hns : σ.apply (Signature.var n) = σ.apply s) :
    σ.apply (HasSubst.single t n s) = σ.apply t :=
  Signature.unifier_absorb σ t n s hns

/-- Reverse decomposition for `Unifier.apply`: same as the axiom but
phrased on `apply` directly. -/
theorem decomp_unifier_apply_sound {α : Type} [Signature α]
    (σ : Unifier α) (x y : α) (xs : Equations α)
    (hd : Signature.decomp x y = some xs) (hxy : σ.apply x = σ.apply y) :
    ∀ p ∈ xs, σ.apply p.1 = σ.apply p.2 :=
  Signature.decomp_unifier_sound x y xs σ hd hxy

/-- If `decomp x y = some xs` and a unifier `u` unifies every pair in
`xs`, then it also unifies `(x, y)`. Proved by induction on the unifier
list, using `decomp_single` to push each binding through `decomp` and
`decomp_struct_sound` for the base case. -/
theorem decomp_apply_sound {α : Type} [Signature α] :
    ∀ (u : Unifier α) (x y : α) (xs : Equations α),
      Signature.decomp x y = some xs →
      (∀ p ∈ xs, u.apply p.1 = u.apply p.2) →
      u.apply x = u.apply y := by
  intro u
  induction u with
  | nil =>
      intro x y xs hd hu
      have heqs : ∀ p ∈ xs, p.1 = p.2 := by
        intro p hp
        have := hu p hp
        simp [Unifier.apply_nil] at this
        exact this
      exact Signature.decomp_struct_sound x y xs hd heqs
  | cons head rest ih =>
      intro x y xs hd hu
      obtain ⟨n, s⟩ := head
      have hd' : Signature.decomp (HasSubst.single x n s) (HasSubst.single y n s) =
          some (xs.map (fun p =>
            (HasSubst.single p.1 n s, HasSubst.single p.2 n s))) :=
        Signature.decomp_single x y xs n s hd
      have hu' : ∀ q ∈ xs.map (fun p =>
          (HasSubst.single p.1 n s, HasSubst.single p.2 n s)),
          Unifier.apply rest q.1 = Unifier.apply rest q.2 := by
        intro q hq
        rw [List.mem_map] at hq
        obtain ⟨p, hp, hpeq⟩ := hq
        subst hpeq
        have := hu p hp
        simp [Unifier.apply_cons] at this
        exact this
      have h := ih _ _ _ hd' hu'
      simp [Unifier.apply_cons]
      exact h
