import LambdaLab.Unification.Signature

/-! # Bridge lemmas: structural results about substitution and decomposition.

In `Unification/Signature`, lemmas like `single_isFree`, `decomp_isFree`,
`size_decomp`, etc. are *axioms* baked into the typeclass — every
instance must provide them. Here, in the slim-typeclass setup, they
become *theorems* derived from the structural laws (`construct`/
`deconstruct` bijection, `size_construct`). The induction is over the
well-founded `Signature.size` measure. -/

namespace Signature
variable {α : Type} [Signature α]

/-! ## Structural induction on terms.

Any property that holds for variables and is preserved by constructor
application (assuming it holds for all children) holds for every term.
The "subterms have strictly smaller size" fact (`size_lt_of_get`) makes
this well-founded. -/

theorem term_ind {motive : α → Prop}
    (var_case : ∀ n, motive (var n))
    (construct_case : ∀ (c : Constructor α) (args : Vector α (arity c)),
       (∀ i : Fin (arity c), motive (args.get i)) →
       motive (construct (Sum.inr ⟨c, args⟩))) :
    ∀ t : α, motive t := by
  intro t
  induction hk : size t using Nat.strongRecOn generalizing t with
  | _ k ih =>
    match hd : deconstruct t with
    | Sum.inl m =>
        have ht : t = var m := by
          have := deconstruct_construct (α := α) t
          rw [hd] at this
          exact this.symm
        rw [ht]
        exact var_case m
    | Sum.inr ⟨c, args⟩ =>
        have ht : t = construct (Sum.inr ⟨c, args⟩) := by
          have := deconstruct_construct (α := α) t
          rw [hd] at this
          exact this.symm
        rw [ht]
        apply construct_case
        intro i
        have hsz : size (args.get i) < size t := size_lt_of_get hd i
        have hsz' : size (args.get i) < k := hk ▸ hsz
        exact ih _ hsz' _ rfl

/-! ## Vector helper: when a function agrees with `Vector.get`,
    `ofFn` returns the original vector. -/

theorem Vector.ofFn_get_eq_self {β : Type} {n : Nat}
    {v : _root_.Vector β n} {f : Fin n → β}
    (h : ∀ i, f i = v.get i) :
    _root_.Vector.ofFn f = v := by
  have heq : f = (fun i : Fin n => v[i.val]) := funext h
  rw [heq, _root_.Vector.ofFn_getElem]

/-! ## `pSubst` of a variable through a singleton -/

theorem pSubst_var_eq (n : Nat) (s : α) :
    pSubst (var n) ((∅ : Subst α).insert n s) = s := by
  rw [pSubst_var]
  exact Std.HashMap.getD_insert_self

/-! ## `single` lemmas -/

/-- Substituting a variable `n` for itself is the identity. -/
theorem single_var_self (t : α) (n : Nat) :
    HasSubst.single t n (var n) = t := by
  show pSubst t ((∅ : Subst α).insert n (var n)) = t
  induction t using term_ind with
  | var_case m =>
      rw [pSubst_var, Std.HashMap.getD_insert]
      by_cases hnm : n = m
      · subst hnm; simp [var]
      · simp [hnm, Std.HashMap.getD_empty]
  | construct_case c args ih =>
      rw [pSubst_construct]
      congr 3
      exact Vector.ofFn_get_eq_self ih

/-- A singleton substitution at an off-free-vars index is the identity. -/
theorem single_off (t : α) (n : Nat) (s : α)
    (hf : ¬ HasVars.isFree t n) :
    HasSubst.single t n s = t := by
  show pSubst t ((∅ : Subst α).insert n s) = t
  induction t using term_ind with
  | var_case m =>
      rw [pSubst_var, Std.HashMap.getD_insert]
      have hnm : n ≠ m := by
        intro hnm
        subst hnm
        exact hf ((var_isFree n n).mpr rfl)
      simp [hnm, Std.HashMap.getD_empty]
  | construct_case c args ih =>
      rw [pSubst_construct]
      congr 3
      apply Vector.ofFn_get_eq_self
      intro i
      apply ih i
      intro hfi
      apply hf
      show occurs n (construct (Sum.inr ⟨c, args⟩)) = true
      rw [occurs_construct, List.any_eq_true]
      exact ⟨i, List.mem_finRange i, hfi⟩

/-! ## `decomp` shape and structural lemmas. -/

/-- When `decomp x y = some xs`, both `x` and `y` are constructors of
    the same head, and `xs` is the per-argument zip. -/
theorem decomp_eq_some {x y : α} {xs : Equations α}
    (hd : decomp x y = some xs) :
    ∃ (c : Constructor α) (ax ay : Vector α (arity c)),
      x = construct (Sum.inr ⟨c, ax⟩) ∧
      y = construct (Sum.inr ⟨c, ay⟩) ∧
      xs = (List.finRange (arity c)).map (fun i => (ax.get i, ay.get i)) := by
  unfold decomp at hd
  split at hd
  · rename_i cx ax cy ay heqx heqy
    split at hd
    · rename_i hcc
      subst hcc
      cases hd
      refine ⟨cx, ax, ay, ?_, ?_, rfl⟩
      · have := deconstruct_construct (α := α) x
        rw [heqx] at this
        exact this.symm
      · have := deconstruct_construct (α := α) y
        rw [heqy] at this
        exact this.symm
    · cases hd
  all_goals (cases hd)

/-- **Decomposition strictly reduces total size.** -/
theorem size_decomp (x y : α) (xs : Equations α) (hd : decomp x y = some xs) :
    xs.foldr (fun p acc => acc + size p.1 + size p.2) 0 < size x + size y := by
  obtain ⟨c, ax, ay, hxc, hyc, hxs⟩ := decomp_eq_some hd
  subst hxs
  rw [List.foldr_map]
  rw [hxc, hyc, size_construct, size_construct]
  -- Uniform-ize the foldr by replacing the lambda over pairs with a lambda over indices.
  show List.foldr (fun i acc => acc + size (ax.get i) + size (ay.get i)) 0
        (List.finRange (arity c)) <
      1 + List.foldr (fun i acc => acc + size (ax.get i)) 0 (List.finRange (arity c)) +
        (1 + List.foldr (fun i acc => acc + size (ay.get i)) 0 (List.finRange (arity c)))
  generalize List.finRange (arity c) = L
  induction L with
  | nil => simp
  | cons j js ih =>
      simp only [List.foldr]
      omega

/-! ## `isFree` on constructor terms unfolds to a disjunction. -/

theorem isFree_var (n m : Nat) :
    HasVars.isFree (var n : α) m ↔ m = n :=
  var_isFree n m

theorem isFree_construct (c : Constructor α) (args : Vector α (arity c)) (m : Nat) :
    HasVars.isFree (construct (Sum.inr ⟨c, args⟩)) m ↔
      ∃ i : Fin (arity c), HasVars.isFree (args.get i) m := by
  show occurs m (construct (Sum.inr ⟨c, args⟩)) = true ↔ _
  rw [occurs_construct, List.any_eq_true]
  constructor
  · rintro ⟨i, _, hi⟩; exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, List.mem_finRange i, hi⟩

/-! ## Free-variable behavior of `single`. -/

/-- The standard "free-variables-after-substitution" characterization. -/
theorem single_isFree (t : α) (n : Nat) (s : α) (m : Nat) :
    HasVars.isFree (HasSubst.single t n s) m ↔
      (m ≠ n ∧ HasVars.isFree t m) ∨ (HasVars.isFree t n ∧ HasVars.isFree s m) := by
  show HasVars.isFree (pSubst t ((∅ : Subst α).insert n s)) m ↔ _
  induction t using term_ind with
  | var_case k =>
      rw [pSubst_var, Std.HashMap.getD_insert]
      by_cases hnk : n = k
      · subst hnk
        simp only [BEq.rfl, ↓reduceIte]
        constructor
        · intro hsm
          right
          exact ⟨(isFree_var n n).mpr rfl, hsm⟩
        · rintro (⟨hmn, hfm⟩ | ⟨_, hsm⟩)
          · exfalso; exact hmn ((isFree_var n m).mp hfm)
          · exact hsm
      · have hbeq : (n == k) = false := by simp [hnk]
        rw [hbeq]
        simp only [Bool.false_eq_true, ↓reduceIte, Std.HashMap.getD_empty]
        rw [isFree_var, isFree_var]
        constructor
        · intro hmk
          left
          refine ⟨?_, hmk⟩
          intro hmn
          exact hnk (hmn.symm.trans hmk)
        · rintro (⟨_, hmk⟩ | ⟨hkn, _⟩)
          · exact hmk
          · exfalso; exact hnk hkn
  | construct_case c args ih =>
      rw [pSubst_construct]
      rw [isFree_construct, isFree_construct, isFree_construct]
      have hget : ∀ (f : Fin (arity c) → α) (i : Fin (arity c)),
          (Vector.ofFn f).get i = f i := by
        intro f i
        show (Vector.ofFn f)[i.val]'i.isLt = f i
        simp
      constructor
      · rintro ⟨i, hi⟩
        rw [hget] at hi
        rcases (ih i).mp hi with ⟨hmn, hfm⟩ | ⟨hfn, hsm⟩
        · exact Or.inl ⟨hmn, ⟨i, hfm⟩⟩
        · exact Or.inr ⟨⟨i, hfn⟩, hsm⟩
      · rintro (⟨hmn, ⟨i, hfm⟩⟩ | ⟨⟨i, hfn⟩, hsm⟩)
        · refine ⟨i, ?_⟩
          rw [hget]
          exact (ih i).mpr (Or.inl ⟨hmn, hfm⟩)
        · refine ⟨i, ?_⟩
          rw [hget]
          exact (ih i).mpr (Or.inr ⟨hfn, hsm⟩)

/-! ## `decomp` does not introduce free variables. -/

theorem decomp_isFree (x y : α) (xs : Equations α) (n : Nat)
    (hd : decomp x y = some xs) (hf : HasVars.isFree xs n) :
    HasVars.isFree x n ∨ HasVars.isFree y n := by
  obtain ⟨c, ax, ay, hxc, hyc, hxs⟩ := decomp_eq_some hd
  subst hxs
  obtain ⟨p, hp_mem, hp_or⟩ := hf
  rw [List.mem_map] at hp_mem
  obtain ⟨i, _, hpi⟩ := hp_mem
  subst hpi
  rw [hxc, hyc]
  rw [isFree_construct, isFree_construct]
  rcases hp_or with h | h
  · exact Or.inl ⟨i, h⟩
  · exact Or.inr ⟨i, h⟩

/-! ## Structural soundness of decomp -/

/-- If `decomp x y = some xs` and every pair in `xs` is propositionally
    equal, then `x = y`. -/
theorem decomp_struct_sound (x y : α) (xs : Equations α)
    (hd : decomp x y = some xs) (heq : ∀ p ∈ xs, p.1 = p.2) :
    x = y := by
  obtain ⟨c, ax, ay, hxc, hyc, hxs⟩ := decomp_eq_some hd
  subst hxs
  -- Each `ax.get i = ay.get i` by `heq` on the corresponding pair.
  have hgeti : ∀ i : Fin (arity c), ax.get i = ay.get i := by
    intro i
    have hmem : (ax.get i, ay.get i) ∈
        (List.finRange (arity c)).map (fun i => (ax.get i, ay.get i)) :=
      List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    exact heq _ hmem
  -- Hence `ax = ay`.
  have hax_eq_ay : ax = ay := by
    apply Vector.ext
    intro i hi
    exact hgeti ⟨i, hi⟩
  rw [hxc, hyc, hax_eq_ay]

/-! ## `decomp` commutes with single-binding substitution. -/

theorem decomp_single (x y : α) (xs : Equations α) (n : Nat) (s : α)
    (hd : decomp x y = some xs) :
    decomp (HasSubst.single x n s) (HasSubst.single y n s) =
      some (xs.map (fun p => (HasSubst.single p.1 n s, HasSubst.single p.2 n s))) := by
  obtain ⟨c, ax, ay, hxc, hyc, hxs⟩ := decomp_eq_some hd
  subst hxs
  rw [hxc, hyc]
  show decomp (pSubst _ ((∅ : Subst α).insert n s))
              (pSubst _ ((∅ : Subst α).insert n s)) = _
  rw [pSubst_construct, pSubst_construct]
  unfold decomp
  simp only [construct_deconstruct, ↓reduceDIte]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  -- Goal: ((Vector.ofFn _).get i, (Vector.ofFn _).get i) = ((fun p => ...) ∘ ...) i
  -- The (Vector.ofFn _).get i unfolds to the function applied at i.
  have hax : (Vector.ofFn (fun j : Fin (arity c) =>
                pSubst (ax.get j) ((∅ : Subst α).insert n s))).get i =
              pSubst (ax.get i) ((∅ : Subst α).insert n s) := by
    show ((Vector.ofFn _)[i.val]'i.isLt) = _; simp
  have hay : (Vector.ofFn (fun j : Fin (arity c) =>
                pSubst (ay.get j) ((∅ : Subst α).insert n s))).get i =
              pSubst (ay.get i) ((∅ : Subst α).insert n s) := by
    show ((Vector.ofFn _)[i.val]'i.isLt) = _; simp
  rw [hax, hay]
  rfl

end Signature

/-! ## Unifier-level bridges.

The structural results proved above (`pSubst_construct`, `decomp_eq_some`,
…) lift to facts about `Unifier.apply` — the iterated single-binding fold
that the algorithm builds. The key technical step is that `Unifier.apply`
distributes over `construct`: applying a unifier to a constructor term is
the same as constructing from the per-argument applications. Once that
is in hand, the four unifier-level bridges follow as either structural
inductions (`unifier_absorb`), constructor injectivity
(`decomp_unifier_sound`, `decomp_none_no_unifier`), or a size-monotonicity
argument (`occurs_no_unifier`). -/

namespace Unifier
variable {α : Type} [Signature α]

/-- Pointwise read on a `Vector.ofFn`. Bridge.lean line 207–211 already
inlines this as a `have`; named here so it can be reused. -/
private theorem getElem_ofFn {β : Type} {n : Nat}
    (f : Fin n → β) (i : Nat) (hi : i < n) :
    (Vector.ofFn f)[i]'hi = f ⟨i, hi⟩ := by
  simp

/-- **`Unifier.apply` distributes over `construct`.** Applying `u` to a
constructor term yields the constructor with the same head over the
per-argument applications.

This is the lemma the deferred unifier-level bridges all hinge on; once
in hand, those bridges become structural inductions or constructor
injectivity. -/
theorem apply_construct (u : Unifier α) (c : Signature.Constructor α)
    (args : Vector α (Signature.arity c)) :
    u.apply (Signature.construct (Sum.inr ⟨c, args⟩)) =
      Signature.construct (Sum.inr ⟨c,
        Vector.ofFn (fun i => u.apply (args.get i))⟩) := by
  induction u generalizing args with
  | nil =>
      rw [apply_nil]
      have hself : Vector.ofFn (fun i : Fin (Signature.arity c) =>
                  Unifier.apply (α := α) [] (args.get i)) = args := by
        apply Signature.Vector.ofFn_get_eq_self
        intro i; rw [apply_nil]
      rw [hself]
  | cons p rest ih =>
      obtain ⟨n, s⟩ := p
      rw [apply_cons]
      show Unifier.apply rest
        (Signature.pSubst (Signature.construct (Sum.inr ⟨c, args⟩))
          ((∅ : Subst α).insert n s)) = _
      rw [Signature.pSubst_construct, ih]
      congr 3
      apply Vector.ext
      intro i hi
      rw [getElem_ofFn, getElem_ofFn]
      show Unifier.apply rest ((Vector.ofFn _).get ⟨i, hi⟩) =
        Unifier.apply ((n, s) :: rest) (args.get ⟨i, hi⟩)
      rw [apply_cons]
      congr 1
      show (Vector.ofFn (fun j : Fin (Signature.arity c) =>
              Signature.pSubst (args.get j) ((∅ : Subst α).insert n s))).get ⟨i, hi⟩ =
            HasSubst.single (args.get ⟨i, hi⟩) n s
      show ((Vector.ofFn _)[i]'hi) = _
      rw [getElem_ofFn]
      rfl

end Unifier

/-- **Decomposition under unifier.** If a unifier `l` equates `x` and `y`,
and `decomp x y = some xs`, then `l` also equates each pair in `xs`.
The reverse direction of `decomp_apply_sound`: in the fat typeclass this
is the field `decomp_unifier_sound`; here it is a theorem from
`apply_construct` and constructor injectivity. -/
theorem Signature.decomp_unifier_sound {α : Type} [Signature α]
    (x y : α) (xs : Equations α) (l : Unifier α)
    (hd : Signature.decomp x y = some xs)
    (hxy : l.apply x = l.apply y) :
    ∀ p ∈ xs, l.apply p.1 = l.apply p.2 := by
  obtain ⟨c, ax, ay, hxc, hyc, hxs⟩ := decomp_eq_some hd
  subst hxs
  rw [hxc, hyc] at hxy
  rw [Unifier.apply_construct, Unifier.apply_construct] at hxy
  -- Constructor injectivity: heads agree, vectors agree.
  have hsigma : (⟨c, Vector.ofFn (fun i => l.apply (ax.get i))⟩ : Σ c : Constructor α,
                  Vector α (Signature.arity c)) =
                ⟨c, Vector.ofFn (fun i => l.apply (ay.get i))⟩ := by
    have hde := congrArg Signature.deconstruct hxy
    simp only [Signature.construct_deconstruct] at hde
    exact Sum.inr.inj hde
  have hvec : Vector.ofFn (fun i => l.apply (ax.get i)) =
              Vector.ofFn (fun i => l.apply (ay.get i)) := by
    have := Sigma.mk.inj hsigma
    exact eq_of_heq this.2
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _, hpi⟩
  subst hpi
  show l.apply (ax.get i) = l.apply (ay.get i)
  have h1 : (Vector.ofFn (fun j => l.apply (ax.get j))).get i = l.apply (ax.get i) := by
    show ((Vector.ofFn _)[i.val]'i.isLt) = _; simp
  have h2 : (Vector.ofFn (fun j => l.apply (ay.get j))).get i = l.apply (ay.get i) := by
    show ((Vector.ofFn _)[i.val]'i.isLt) = _; simp
  rw [← h1, ← h2, hvec]

/-- A non-variable term is a constructor application. Inverse of
`Signature.isVar` failing. -/
private theorem isVar_none_construct {α : Type} [Signature α] {t : α}
    (h : Signature.isVar t = none) :
    ∃ (c : Signature.Constructor α) (args : Vector α (Signature.arity c)),
      t = Signature.construct (Sum.inr ⟨c, args⟩) := by
  match hd : Signature.deconstruct t with
  | Sum.inl n =>
      exfalso
      have : Signature.isVar t = some n := by
        unfold Signature.isVar
        rw [hd]
      rw [this] at h
      cases h
  | Sum.inr ⟨c, args⟩ =>
      refine ⟨c, args, ?_⟩
      have := Signature.deconstruct_construct (α := α) t
      rw [hd] at this
      exact this.symm

/-- **Decomposition-failure completeness.** When `x` and `y` are both
non-variables with mismatched outermost constructors, no unifier can
equate them. The negative half of the decomposition trichotomy. -/
theorem Signature.decomp_none_no_unifier {α : Type} [Signature α]
    (x y : α) (l : Unifier α)
    (hxv : Signature.isVar x = none)
    (hyv : Signature.isVar y = none)
    (hd : Signature.decomp x y = none) :
    l.apply x ≠ l.apply y := by
  obtain ⟨cx, ax, hxc⟩ := isVar_none_construct hxv
  obtain ⟨cy, ay, hyc⟩ := isVar_none_construct hyv
  have hcxcy : cx ≠ cy := by
    intro hc
    subst hc
    rw [hxc, hyc] at hd
    unfold Signature.decomp at hd
    simp only [Signature.construct_deconstruct, ↓reduceDIte] at hd
    cases hd
  intro heq
  rw [hxc, hyc] at heq
  rw [Unifier.apply_construct, Unifier.apply_construct] at heq
  have hde := congrArg Signature.deconstruct heq
  simp only [Signature.construct_deconstruct] at hde
  have hsig := Sum.inr.inj hde
  exact hcxcy (Sigma.mk.inj hsig).1

/-- **Unifier absorption.** If a unifier `l` already equates `var n` with
`s`, then prepending the single binding `[n ↦ s]` to any term `t` doesn't
change `l`'s result. The fundamental lemma behind the variable-elimination
rules of `unify`. -/
theorem Signature.unifier_absorb {α : Type} [Signature α]
    (l : Unifier α) (t : α) (n : Nat) (s : α)
    (hns : l.apply (Signature.var n) = l.apply s) :
    l.apply (HasSubst.single t n s) = l.apply t := by
  show l.apply (Signature.pSubst t ((∅ : Subst α).insert n s)) = l.apply t
  induction t using Signature.term_ind with
  | var_case m =>
      rw [Signature.pSubst_var, Std.HashMap.getD_insert]
      by_cases hnm : n = m
      · subst hnm
        simp only [BEq.rfl, ↓reduceIte]
        exact hns.symm
      · have hbeq : (n == m) = false := by simp [hnm]
        rw [hbeq]
        simp [Std.HashMap.getD_empty]
  | construct_case c args ih =>
      rw [Signature.pSubst_construct]
      rw [Unifier.apply_construct, Unifier.apply_construct]
      congr 3
      apply Signature.Vector.ofFn_get_eq_self
      intro i
      have hget1 : (Vector.ofFn (fun j : Fin (Signature.arity c) =>
                      Signature.pSubst (args.get j) ((∅ : Subst α).insert n s))).get i =
                   Signature.pSubst (args.get i) ((∅ : Subst α).insert n s) := by
        show ((Vector.ofFn _)[i.val]'i.isLt) = _; simp
      have hget2 : (Vector.ofFn (fun j : Fin (Signature.arity c) =>
                      l.apply (args.get j))).get i =
                   l.apply (args.get i) := by
        show ((Vector.ofFn _)[i.val]'i.isLt) = _; simp
      rw [hget1, hget2]
      exact ih i

/-! ### `occurs_no_unifier`: occurs-check completeness.

A term `t` that strictly contains `var n` (i.e. mentions it but isn't
just `var n`) cannot be unified with `var n` by any unifier. The
intuition is that applying any unifier to such a `t` produces a
constructor whose size strictly dominates the size of the unifier's
value at `var n`, so the two cannot coincide. -/

/-- The foldr that defines `size_construct` is at least as large as any
single summand. -/
private theorem foldr_sum_ge {β : Type} (f : β → Nat) :
    ∀ (l : List β) (a : β), a ∈ l →
      f a ≤ l.foldr (fun i acc => acc + f i) 0 := by
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons x xs ih =>
      intro a h
      rcases List.mem_cons.mp h with rfl | hxs
      · simp only [List.foldr]; omega
      · have := ih a hxs
        simp only [List.foldr]; omega

/-- The size of `l.apply (construct ⟨c, args⟩)` written in terms of the
per-argument applied sizes — the form needed for size-monotonicity
arguments. -/
private theorem size_apply_construct {α : Type} [Signature α]
    (l : Unifier α) (c : Signature.Constructor α)
    (args : Vector α (Signature.arity c)) :
    Signature.size (l.apply (Signature.construct (Sum.inr ⟨c, args⟩))) =
      1 + (List.finRange (Signature.arity c)).foldr
        (fun i acc => acc + Signature.size (l.apply (args.get i))) 0 := by
  rw [Unifier.apply_construct, Signature.size_construct]
  congr 1
  generalize List.finRange (Signature.arity c) = L
  induction L with
  | nil => rfl
  | cons j js ih =>
      simp only [List.foldr]
      rw [ih]
      congr 1
      show Signature.size ((Vector.ofFn _)[j.val]'j.isLt) = _
      simp

/-- If `var n` is free in `t`, then under any unifier `l` the size of
`l.apply (var n)` is bounded by the size of `l.apply t`. -/
private theorem size_apply_le_of_isFree {α : Type} [Signature α]
    (l : Unifier α) (t : α) (n : Nat) (h : HasVars.isFree t n) :
    Signature.size (l.apply (Signature.var n)) ≤ Signature.size (l.apply t) := by
  induction t using Signature.term_ind with
  | var_case m =>
      have hmn : n = m := (Signature.var_isFree m n).mp h
      subst hmn
      exact Nat.le_refl _
  | construct_case c args ih =>
      rw [Signature.isFree_construct] at h
      obtain ⟨i, hi⟩ := h
      have ihi := ih i hi
      rw [size_apply_construct]
      have hbound :
          Signature.size (l.apply (args.get i)) ≤
            (List.finRange (Signature.arity c)).foldr
              (fun j acc => acc + Signature.size (l.apply (args.get j))) 0 :=
        foldr_sum_ge (fun j : Fin (Signature.arity c) =>
            Signature.size (l.apply (args.get j)))
          _ i (List.mem_finRange i)
      omega

/-- **Occurs-check completeness.** If `t` mentions `var n` but is not
just `var n` itself, no unifier can equate `var n` with `t`. The
structural fact that justifies the `occurs` rule of `unify`. -/
theorem Signature.occurs_no_unifier {α : Type} [Signature α]
    (t : α) (n : Nat) (l : Unifier α)
    (hf : HasVars.isFree t n)
    (hnv : Signature.isVar t ≠ some n) :
    l.apply (Signature.var n) ≠ l.apply t := by
  match hd : Signature.deconstruct t with
  | Sum.inl m =>
      have htm : t = Signature.var m := by
        have := Signature.deconstruct_construct (α := α) t
        rw [hd] at this
        exact this.symm
      have hisv : Signature.isVar t = some m := by
        unfold Signature.isVar
        rw [hd]
      rw [htm] at hf
      have hmn : n = m := (Signature.var_isFree m n).mp hf
      subst hmn
      exact absurd hisv hnv
  | Sum.inr ⟨c, args⟩ =>
      have htc : t = Signature.construct (Sum.inr ⟨c, args⟩) := by
        have := Signature.deconstruct_construct (α := α) t
        rw [hd] at this
        exact this.symm
      rw [htc] at hf
      rw [Signature.isFree_construct] at hf
      obtain ⟨i, hi⟩ := hf
      have ihi : Signature.size (l.apply (Signature.var n)) ≤
                 Signature.size (l.apply (args.get i)) :=
        size_apply_le_of_isFree l (args.get i) n hi
      have hbound :
          Signature.size (l.apply (args.get i)) ≤
            (List.finRange (Signature.arity c)).foldr
              (fun j acc => acc + Signature.size (l.apply (args.get j))) 0 :=
        foldr_sum_ge (fun j : Fin (Signature.arity c) =>
            Signature.size (l.apply (args.get j)))
          _ i (List.mem_finRange i)
      have hstrict : Signature.size (l.apply (Signature.var n)) <
                     Signature.size (l.apply t) := by
        rw [htc, size_apply_construct]
        omega
      intro heq
      rw [heq] at hstrict
      exact Nat.lt_irrefl _ hstrict

