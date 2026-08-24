import LambdaLab.Substitution.Unification.Signature

/-! # Bridge lemmas: structural results about substitution and decomposition.

In `Unification/Signature`, lemmas like `single_isFree`, `decomp_isFree`,
`size_decomp`, etc. are *axioms* baked into the typeclass — every
instance must provide them. Here, in the slim-typeclass setup, they
become *theorems* derived from the structural laws (`construct`/
`deconstruct` bijection, `size_construct`). The induction is over the
well-founded `Signature.size` measure. -/

namespace Signature
variable {α : Type} [Signature α]

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

/-! ## `pSubst` on the empty substitution and composition law. -/

/-- Applying the empty substitution is the identity. -/
theorem pSubst_empty (t : α) : pSubst t (∅ : Subst α) = t := by
  induction t using term_ind with
  | var_case n =>
      rw [pSubst_var, Std.HashMap.getD_empty]
  | construct_case c args ih =>
      rw [pSubst_construct]
      congr 3
      exact Vector.ofFn_get_eq_self ih

/-- **Substituting into a ground term is the identity.** A term with no free variable has nothing
for `σ` to replace: the `var` case cannot arise, and the constructor case is congruence.

This is `GroundStable` for every `Signature`, and it is why that class is stateable at all — the
law is a theorem here, so no instance has to be trusted with it. -/
theorem pSubst_ground {t : α} (σ : Subst α) (h : HasVars.Ground t) : pSubst t σ = t := by
  induction t using term_ind with
  | var_case n => exact absurd ((var_isFree n n).mpr rfl) (h n)
  | construct_case c args ih =>
      rw [pSubst_construct]
      congr 3
      refine Vector.ofFn_get_eq_self (fun i => ih i (fun n hn => h n ?_))
      show occurs n (construct (Sum.inr ⟨c, args⟩)) = true
      rw [occurs_construct, List.any_eq_true]
      exact ⟨i, List.mem_finRange i, hn⟩

instance instGroundStable : GroundStable α α where
  pSubst_ground σ h := by
    show Signature.pSubst _ σ = _
    exact pSubst_ground σ h

/-! `LawfulComp` for a signature's own type is `Signature.pSubst_comp`, proved below; the instance
is declared there, once the theorem exists. -/

/-- **Composition law for parallel substitution.** Substituting through a
singleton `{n ↦ s}` and then through `σ` is the same as one parallel
pass through `σ` extended with `n ↦ pSubst s σ`. This is the equation
that converts an iterated `Unifier.apply` into a single `pSubst`. -/
theorem pSubst_single_compose (t : α) (n : Nat) (s : α) (σ : Subst α) :
    pSubst (HasSubst.single t n s) σ
      = pSubst t (σ.insert n (pSubst s σ)) := by
  show pSubst (pSubst t ((∅ : Subst α).insert n s)) σ
      = pSubst t (σ.insert n (pSubst s σ))
  induction t using term_ind with
  | var_case k =>
      rw [pSubst_var, Std.HashMap.getD_insert]
      by_cases hk : n = k
      · subst hk
        simp only [BEq.rfl, ↓reduceIte]
        rw [pSubst_var, Std.HashMap.getD_insert_self]
      · have hbeq : (n == k) = false := by simp [hk]
        rw [hbeq]
        simp only [Bool.false_eq_true, ↓reduceIte, Std.HashMap.getD_empty]
        rw [pSubst_var, pSubst_var, Std.HashMap.getD_insert, hbeq]
        simp
  | construct_case c args ih =>
      show pSubst (pSubst (Signature.construct (Sum.inr ⟨c, args⟩))
              ((∅ : Subst α).insert n s)) σ
          = pSubst (Signature.construct (Sum.inr ⟨c, args⟩))
              (σ.insert n (pSubst s σ))
      rw [pSubst_construct, pSubst_construct, pSubst_construct]
      congr 3
      apply Vector.ext
      intro i hi
      have hget : ∀ (f : Fin (arity c) → α),
          (Vector.ofFn f)[i]'hi = f ⟨i, hi⟩ := fun _ => by simp
      rw [hget, hget]
      -- LHS now: pSubst ((Vector.ofFn (fun j => pSubst (args.get j) (∅.insert n s))).get ⟨i, hi⟩) σ
      show pSubst ((Vector.ofFn (fun j : Fin (arity c) =>
                  pSubst (args.get j) ((∅ : Subst α).insert n s))).get ⟨i, hi⟩) σ
            = pSubst (args.get ⟨i, hi⟩) (σ.insert n (pSubst s σ))
      have hget' : (Vector.ofFn (fun j : Fin (arity c) =>
                  pSubst (args.get j) ((∅ : Subst α).insert n s))).get ⟨i, hi⟩ =
                pSubst (args.get ⟨i, hi⟩) ((∅ : Subst α).insert n s) := by
        show ((Vector.ofFn _)[i]'hi) = _; simp
      rw [hget']
      exact ih ⟨i, hi⟩

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
  have hget : ∀ a : Vector α (arity c),
      (Vector.ofFn (fun j : Fin (arity c) =>
          pSubst (a.get j) ((∅ : Subst α).insert n s))).get i =
        pSubst (a.get i) ((∅ : Subst α).insert n s) := fun _ => by
    show ((Vector.ofFn _)[i.val]'i.isLt) = _; simp
  rw [hget ax, hget ay]
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

/-! ## Bridge between iterated `apply` and one-shot `pSubst toSubst`.

`Unifier.apply` applies the bindings one at a time, left-to-right. The
`toSubst` conversion compresses the list into one parallel `Subst α` by
pushing every later binding's effect into earlier values. The next
theorem proves these two views agree on every term — letting the public
`unify` API return `Option (Subst α)` while the internal proofs continue
to work with the list form. -/

theorem apply_eq_pSubst_toSubst (u : Unifier α) (t : α) :
    u.apply t = HasSubst.pSubst t u.toSubst := by
  induction u generalizing t with
  | nil =>
      rw [apply_nil, toSubst_nil]
      exact (Signature.pSubst_empty t).symm
  | cons p rest ih =>
      obtain ⟨n, s⟩ := p
      rw [apply_cons, ih, toSubst_cons]
      exact Signature.pSubst_single_compose t n s (toSubst rest)

end Unifier

/-- **Decomposition under unifier (forward direction).** If
`decomp x y = some xs` and a unifier `l` already unifies every pair in
`xs`, then it also unifies `(x, y)`. Used in the soundness proof of
`unify` for the decomposition case. The reverse direction is
`decomp_unifier_sound`. -/
theorem Signature.decomp_apply_sound {α : Type} [Signature α] :
    ∀ (l : Unifier α) (x y : α) (xs : Equations α),
      Signature.decomp x y = some xs →
      (∀ p ∈ xs, l.apply p.1 = l.apply p.2) →
      l.apply x = l.apply y := by
  intro l
  induction l with
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

/-- `HasSubst.pSubst` at the derived instance *is* `Signature.pSubst`. The lemmas below are
stated in the `Signature` spelling, where `pSubst_var`/`pSubst_construct` apply; callers holding a
`HasSubst` goal rewrite with this first. -/
theorem Signature.hasSubst_pSubst_eq {α : Type} [Signature α] (t : α) (σ : Subst α) :
    HasSubst.pSubst t σ = Signature.pSubst t σ := rfl

/-- **Decomposition under unifier.** If a substitution `σ` equates `x` and `y`,
and `decomp x y = some xs`, then `l` also equates each pair in `xs`.
The reverse direction of `decomp_apply_sound`: in the fat typeclass this
is the field `decomp_unifier_sound`; here it is a theorem from
`apply_construct` and constructor injectivity. -/
theorem Signature.decomp_unifier_sound {α : Type} [Signature α]
    (x y : α) (xs : Equations α) (σ : Subst α)
    (hd : Signature.decomp x y = some xs)
    (hxy : Signature.pSubst x σ = Signature.pSubst y σ) :
    ∀ p ∈ xs, Signature.pSubst p.1 σ = Signature.pSubst p.2 σ := by
  obtain ⟨c, ax, ay, hxc, hyc, hxs⟩ := decomp_eq_some hd
  subst hxs
  rw [hxc, hyc] at hxy
  rw [Signature.pSubst_construct, Signature.pSubst_construct] at hxy
  -- Constructor injectivity: heads agree, vectors agree.
  have hsigma : (⟨c, Vector.ofFn (fun i => Signature.pSubst (ax.get i) σ)⟩ : Σ c : Constructor α,
                  Vector α (Signature.arity c)) =
                ⟨c, Vector.ofFn (fun i => Signature.pSubst (ay.get i) σ)⟩ := by
    have hde := congrArg Signature.deconstruct hxy
    simp only [Signature.construct_deconstruct] at hde
    exact Sum.inr.inj hde
  have hvec : Vector.ofFn (fun i => Signature.pSubst (ax.get i) σ) =
              Vector.ofFn (fun i => Signature.pSubst (ay.get i) σ) := by
    have := Sigma.mk.inj hsigma
    exact eq_of_heq this.2
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _, hpi⟩
  subst hpi
  show Signature.pSubst (ax.get i) σ = Signature.pSubst (ay.get i) σ
  have h1 : (Vector.ofFn (fun j => Signature.pSubst (ax.get j) σ)).get i = Signature.pSubst (ax.get i) σ := by
    show ((Vector.ofFn _)[i.val]'i.isLt) = _; simp
  have h2 : (Vector.ofFn (fun j => Signature.pSubst (ay.get j) σ)).get i = Signature.pSubst (ay.get i) σ := by
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
    (x y : α) (σ : Subst α)
    (hxv : Signature.isVar x = none)
    (hyv : Signature.isVar y = none)
    (hd : Signature.decomp x y = none) :
    Signature.pSubst x σ ≠ Signature.pSubst y σ := by
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
  rw [Signature.pSubst_construct, Signature.pSubst_construct] at heq
  have hde := congrArg Signature.deconstruct heq
  simp only [Signature.construct_deconstruct] at hde
  have hsig := Sum.inr.inj hde
  exact hcxcy (Sigma.mk.inj hsig).1

/-- **Unifier absorption.** If a substitution `σ` already equates `var n` with
`s`, then prepending the single binding `[n ↦ s]` to any term `t` doesn't
change `l`'s result. The fundamental lemma behind the variable-elimination
rules of `unify`. -/
theorem Signature.unifier_absorb {α : Type} [Signature α]
    (σ : Subst α) (t : α) (n : Nat) (s : α)
    (hns : Signature.pSubst (Signature.var n) σ = Signature.pSubst s σ) :
    Signature.pSubst (HasSubst.single t n s) σ = Signature.pSubst t σ := by
  show Signature.pSubst (Signature.pSubst t ((∅ : Subst α).insert n s)) σ = Signature.pSubst t σ
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
      rw [Signature.pSubst_construct, Signature.pSubst_construct]
      congr 3
      apply Signature.Vector.ofFn_get_eq_self
      intro i
      have hget1 : (Vector.ofFn (fun j : Fin (Signature.arity c) =>
                      Signature.pSubst (args.get j) ((∅ : Subst α).insert n s))).get i =
                   Signature.pSubst (args.get i) ((∅ : Subst α).insert n s) := by
        show ((Vector.ofFn _)[i.val]'i.isLt) = _; simp
      have hget2 : (Vector.ofFn (fun j : Fin (Signature.arity c) =>
                      Signature.pSubst (args.get j) σ)).get i =
                   Signature.pSubst (args.get i) σ := by
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

/-- The size of `Signature.pSubst (construct ⟨c, args⟩) σ` written in terms of the
per-argument applied sizes — the form needed for size-monotonicity
arguments. -/
private theorem size_pSubst_construct {α : Type} [Signature α]
    (σ : Subst α) (c : Signature.Constructor α)
    (args : Vector α (Signature.arity c)) :
    Signature.size (Signature.pSubst (Signature.construct (Sum.inr ⟨c, args⟩)) σ) =
      1 + (List.finRange (Signature.arity c)).foldr
        (fun i acc => acc + Signature.size (Signature.pSubst (args.get i) σ)) 0 := by
  rw [Signature.pSubst_construct, Signature.size_construct]
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

/-- If `var n` is free in `t`, then under any substitution `σ` the size of
`Signature.pSubst (var n) σ` is bounded by the size of `Signature.pSubst t σ`. -/
private theorem size_pSubst_le_of_isFree {α : Type} [Signature α]
    (σ : Subst α) (t : α) (n : Nat) (h : HasVars.isFree t n) :
    Signature.size (Signature.pSubst (Signature.var n) σ) ≤ Signature.size (Signature.pSubst t σ) := by
  induction t using Signature.term_ind with
  | var_case m =>
      have hmn : n = m := (Signature.var_isFree m n).mp h
      subst hmn
      exact Nat.le_refl _
  | construct_case c args ih =>
      rw [Signature.isFree_construct] at h
      obtain ⟨i, hi⟩ := h
      have ihi := ih i hi
      rw [size_pSubst_construct]
      have hbound :
          Signature.size (Signature.pSubst (args.get i) σ) ≤
            (List.finRange (Signature.arity c)).foldr
              (fun j acc => acc + Signature.size (Signature.pSubst (args.get j) σ)) 0 :=
        foldr_sum_ge (fun j : Fin (Signature.arity c) =>
            Signature.size (Signature.pSubst (args.get j) σ))
          _ i (List.mem_finRange i)
      omega

/-- **Occurs-check completeness.** If `t` mentions `var n` but is not
just `var n` itself, no unifier can equate `var n` with `t`. The
structural fact that justifies the `occurs` rule of `unify`. -/
theorem Signature.occurs_no_unifier {α : Type} [Signature α]
    (t : α) (n : Nat) (σ : Subst α)
    (hf : HasVars.isFree t n)
    (hnv : Signature.isVar t ≠ some n) :
    Signature.pSubst (Signature.var n) σ ≠ Signature.pSubst t σ := by
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
      have ihi : Signature.size (Signature.pSubst (Signature.var n) σ) ≤
                 Signature.size (Signature.pSubst (args.get i) σ) :=
        size_pSubst_le_of_isFree σ (args.get i) n hi
      have hbound :
          Signature.size (Signature.pSubst (args.get i) σ) ≤
            (List.finRange (Signature.arity c)).foldr
              (fun j acc => acc + Signature.size (Signature.pSubst (args.get j) σ)) 0 :=
        foldr_sum_ge (fun j : Fin (Signature.arity c) =>
            Signature.size (Signature.pSubst (args.get j) σ))
          _ i (List.mem_finRange i)
      have hstrict : Signature.size (Signature.pSubst (Signature.var n) σ) <
                     Signature.size (Signature.pSubst t σ) := by
        rw [htc, size_pSubst_construct]
        omega
      intro heq
      rw [heq] at hstrict
      exact Nat.lt_irrefl _ hstrict


/-- Consing a binding onto a unifier, in parallel form: `toSubst ((n,s) :: rest)` acts as "apply
the single binding, then the rest". The `toSubst` transcription of `Unifier.apply_cons`. -/
theorem Unifier.toSubst_cons_pSubst {α : Type} [Signature α] (n : Nat) (s : α)
    (rest : Unifier α) (t : α) :
    HasSubst.pSubst t (Unifier.toSubst ((n, s) :: rest)) =
      HasSubst.pSubst (HasSubst.single t n s) (Unifier.toSubst rest) := by
  rw [← Unifier.apply_eq_pSubst_toSubst, ← Unifier.apply_eq_pSubst_toSubst, Unifier.apply_cons]

/-- Free variables of a substituted term: every one comes from *some* variable of the original,
routed through what σ puts there. When σ leaves `k` alone the witness is `k = m` itself. -/
theorem Signature.isFree_pSubst {α : Type} [Signature α] (t : α) (σ : Subst α) (m : Nat) :
    HasVars.isFree (Signature.pSubst t σ) m →
      ∃ k, HasVars.isFree t k ∧ HasVars.isFree (σ.getD k (Signature.var k)) m := by
  induction t using Signature.term_ind with
  | var_case n =>
      intro h
      rw [Signature.pSubst_var] at h
      exact ⟨n, (Signature.var_isFree n n).mpr rfl, h⟩
  | construct_case c args ih =>
      intro h
      rw [Signature.pSubst_construct, Signature.isFree_construct] at h
      obtain ⟨i, hi⟩ := h
      have hi' : HasVars.isFree (Signature.pSubst (args.get i) σ) m := by
        have : (Vector.ofFn (fun j => Signature.pSubst (args.get j) σ)).get i
             = Signature.pSubst (args.get i) σ := by
          show ((Vector.ofFn _)[i.val]'i.isLt) = _; simp
        rwa [this] at hi
      obtain ⟨k, hk, hkm⟩ := ih i hi'
      exact ⟨k, (Signature.isFree_construct _ _ _).mpr ⟨i, hk⟩, hkm⟩

/-- A `max`-fold is bounded by any common bound on its summands. -/
private theorem foldr_max_le {β : Type} (f : β → Nat) (n : Nat) :
    ∀ (l : List β), (∀ i ∈ l, f i ≤ n) →
      l.foldr (fun i acc => max acc (f i)) 0 ≤ n
  | [], _ => Nat.zero_le n
  | j :: js, h => by
      simp only [List.foldr]
      exact Nat.max_le.mpr ⟨foldr_max_le f n js (fun i hi => h i (List.mem_cons_of_mem _ hi)),
        h j List.mem_cons_self⟩

/-- **Converse of `fresh_gt_free`.** If every free variable of `t` is below `n`, then `fresh t ≤ n`.
The class only provides the forward direction; the bounds derived from `unify_keys`/`unify_range`
are phrased with `isFree`, and inductions want them as `fresh ≤ n`. -/
theorem Signature.fresh_le_of_free_lt {α : Type} [Signature α] (t : α) (n : Nat)
    (h : ∀ m, HasVars.isFree t m → m < n) : HasVars.fresh t ≤ n := by
  induction t using Signature.term_ind with
  | var_case k =>
      show Signature.fresh (Signature.var k : α) ≤ n
      rw [Signature.fresh_var]
      exact h k ((Signature.var_isFree k k).mpr rfl)
  | construct_case c args ih =>
      show Signature.fresh (Signature.construct (Sum.inr ⟨c, args⟩)) ≤ n
      rw [Signature.fresh_construct]
      refine foldr_max_le _ n _ (fun i _ => ?_)
      exact ih i (fun m hm => h m ((Signature.isFree_construct _ _ _).mpr ⟨i, hm⟩))

/-! ## Composition law for `Subst.comp` (generic for `Signature α`)

The named-STLC instance proves `Ty.pSubst_comp` in
`Stlc/Named/Unification.lean` by structural induction on `Ty`; here we
prove the same fact abstractly for any `Signature α` using `term_ind`.
Stated with `HasSubst.pSubst` so downstream `rw`s work without `show`. -/

theorem Signature.pSubst_comp {α : Type} [Signature α]
    (σ τ : Subst α) (t : α) :
    HasSubst.pSubst t (Subst.comp σ τ) =
      HasSubst.pSubst (HasSubst.pSubst t τ) σ := by
  show Signature.pSubst t (Subst.comp σ τ) =
       Signature.pSubst (Signature.pSubst t τ) σ
  induction t using Signature.term_ind with
  | var_case n =>
      rw [Signature.pSubst_var, Subst.comp_getD, Signature.pSubst_var]
      cases hτ : τ.get? n with
      | none =>
          have h₁ : τ.getD n (Signature.var n) = Signature.var n := by
            rw [Std.HashMap.getD_eq_getD_getElem?,
                ← Std.HashMap.get?_eq_getElem?, hτ]
            rfl
          rw [h₁, Signature.pSubst_var]
      | some t' =>
          have h₁ : τ.getD n (Signature.var n) = t' := by
            rw [Std.HashMap.getD_eq_getD_getElem?,
                ← Std.HashMap.get?_eq_getElem?, hτ]
            rfl
          rw [h₁]
          rfl
  | construct_case c args ih =>
      rw [Signature.pSubst_construct, Signature.pSubst_construct,
          Signature.pSubst_construct]
      congr 3
      apply Vector.ext
      intro i hi
      have hget : ∀ (f : Fin (Signature.arity c) → α),
          (Vector.ofFn f)[i]'hi = f ⟨i, hi⟩ := fun _ => by simp
      rw [hget, hget]
      have hget' : (Vector.ofFn (fun j : Fin (Signature.arity c) =>
                Signature.pSubst (args.get j) τ)).get ⟨i, hi⟩ =
              Signature.pSubst (args.get ⟨i, hi⟩) τ := by
        show ((Vector.ofFn _)[i]'hi) = _; simp
      rw [hget']
      exact ih ⟨i, hi⟩

/-- `LawfulComp` for a signature's own type: the theorem just proved, packaged so that clients
accumulating substitutions can ask for the law by class rather than by name. -/
instance instLawfulComp {α : Type} [Signature α] : LawfulComp α α where
  pSubst_comp := fun t σ τ => Signature.pSubst_comp σ τ t

/-! ## `MoreGeneral` algebra (generic for `Signature α`).

`MoreGeneral` from `Substitution/Basic.lean` is generic in `HasSubst α α`,
but its useful algebraic laws need `Signature.pSubst_empty` (for `refl`)
and `Signature.pSubst_comp` (for `trans`). -/

/-- Reflexivity of `MoreGeneral`: every substitution is at least as
general as itself. Witness τ = `∅`. -/
theorem MoreGeneral.refl {α : Type} [Signature α] (σ : Subst α) :
    MoreGeneral σ σ :=
  ⟨(∅ : Subst α),
   fun t => (Signature.pSubst_empty (HasSubst.pSubst t σ)).symm⟩

/-- Transitivity of `MoreGeneral`: chains compose via `Subst.comp`. -/
theorem MoreGeneral.trans {α : Type} [Signature α] {σ₁ σ₂ σ₃ : Subst α}
    (h₁ : MoreGeneral σ₁ σ₂) (h₂ : MoreGeneral σ₂ σ₃) : MoreGeneral σ₁ σ₃ := by
  obtain ⟨τ₁, hτ₁⟩ := h₁
  obtain ⟨τ₂, hτ₂⟩ := h₂
  refine ⟨Subst.comp τ₂ τ₁, fun t => ?_⟩
  calc HasSubst.pSubst t σ₃
      = HasSubst.pSubst (HasSubst.pSubst t σ₂) τ₂ := hτ₂ t
    _ = HasSubst.pSubst (HasSubst.pSubst (HasSubst.pSubst t σ₁) τ₁) τ₂ := by
          rw [hτ₁]
    _ = HasSubst.pSubst (HasSubst.pSubst t σ₁) (Subst.comp τ₂ τ₁) := by
          rw [← Signature.pSubst_comp]

/-! ## Fresh-mvar extension.

Inserting a binding `(k, v)` into σ doesn't change `pSubst`'s action on
any term `t` that doesn't mention `k` as a free variable. Used by the
principal-types proof in `W.lean`: when W picks a fresh `mvar k`, any
user-supplied σ' (which is freshness-blind to W's `k`) can be extended
without affecting its action on the source. -/

/-- Every element is bounded by a `max`-fold over any list containing its index. The `<` version
of this is inlined in `fresh_gt_occurs`; the `≤` version is wanted here. -/
private theorem foldr_max_ge {α : Type} [Signature α] {m : Nat} (f : Fin m → α) :
    ∀ (l : List (Fin m)) (i : Fin m), i ∈ l →
      Signature.fresh (f i) ≤ l.foldr (fun j acc => max acc (Signature.fresh (f j))) 0
  | [],      _, h => absurd h (by simp)
  | j :: js, i, h => by
      simp only [List.foldr]
      rcases List.mem_cons.mp h with rfl | hj
      · exact Nat.le_max_right _ _
      · exact Nat.le_trans (foldr_max_ge f js i hj) (Nat.le_max_left _ _)

/-- If every key of σ is below the threshold, restricting changes nothing, on any term at all. -/
theorem Subst.restrictBelow_action_eq {α : Type} [Signature α] (σ : Subst α) (n : Nat)
    (hkeys : ∀ k, σ.get? k ≠ none → k < n) (t : α) :
    HasSubst.pSubst t (Subst.restrictBelow σ n) = HasSubst.pSubst t σ := by
  simp only [Signature.hasSubst_pSubst_eq]
  induction t using Signature.term_ind with
  | var_case m =>
      rw [Signature.pSubst_var, Signature.pSubst_var]
      rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?,
          Subst.restrictBelow_get?]
      by_cases hm : m < n
      · rw [if_pos hm]
      · rw [if_neg hm]
        have hnone : σ.get? m = none := by
          cases hgm : σ.get? m with
          | none => rfl
          | some v => exact absurd (hkeys m (by rw [hgm]; exact Option.some_ne_none v)) hm
        rw [hnone]
  | construct_case c args ih =>
      rw [Signature.pSubst_construct, Signature.pSubst_construct]
      congr 3
      apply Signature.Vector.ofFn_get_eq_self
      intro i
      have h2 : (Vector.ofFn (fun j => Signature.pSubst (args.get j) σ)).get i
              = Signature.pSubst (args.get i) σ := by
        show ((Vector.ofFn _)[i.val]'i.isLt) = _; simp
      rw [h2]; exact ih i

/-- Restricting σ to keys below `n` doesn't change pSubst's action on
any `t` whose free mvars are all below `n` (i.e. `HasVars.fresh t ≤ n`).
This is the key lemma for option D in the principal-types story:
W's σ has bindings at indices ≥ srcFresh (its internal fresh mvars);
those bindings are invisible to the source-level pSubst, so pruning
them gives an action-equivalent substitution on the source. -/
theorem Signature.pSubst_restrictBelow {α : Type} [Signature α]
    (σ : Subst α) (n : Nat) (t : α)
    (h_fresh : HasVars.fresh t ≤ n) :
    HasSubst.pSubst t (Subst.restrictBelow σ n) = HasSubst.pSubst t σ := by
  show Signature.pSubst t (Subst.restrictBelow σ n) = Signature.pSubst t σ
  -- Same shape as `fresh_gt_occurs`: strong recursion on `size`, then split on `deconstruct`.
  induction hk : Signature.size t using Nat.strongRecOn generalizing t with
  | _ k ih =>
    match hd : Signature.deconstruct t with
    | Sum.inl m =>
        -- A variable below the threshold looks itself up in the *unrestricted* σ.
        have ht : t = Signature.var m := by
          have := Signature.deconstruct_construct (α := α) t
          rw [hd] at this
          exact this.symm
        subst ht
        have hmn : m < n := by
          have : Signature.fresh (Signature.var m : α) ≤ n := h_fresh
          rw [Signature.fresh_var] at this; omega
        rw [Signature.pSubst_var, Signature.pSubst_var]
        rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?,
            Subst.restrictBelow_get?, if_pos hmn]
    | Sum.inr ⟨c, args⟩ =>
        -- Constructors recurse; each argument's `fresh` is bounded by the whole term's.
        have ht : t = Signature.construct (Sum.inr ⟨c, args⟩) := by
          have := Signature.deconstruct_construct (α := α) t
          rw [hd] at this
          exact this.symm
        subst ht
        rw [Signature.pSubst_construct, Signature.pSubst_construct]
        refine congrArg (fun v => Signature.construct (Sum.inr ⟨c, v⟩)) ?_
        refine congrArg Vector.ofFn (funext fun i => ?_)
        have hsz : Signature.size (args.get i) <
            Signature.size (Signature.construct (Sum.inr ⟨c, args⟩)) :=
          Signature.size_lt_of_get hd i
        refine ih (Signature.size (args.get i)) (hk ▸ hsz) (args.get i) ?_ rfl
        have hle : Signature.fresh (args.get i) ≤
            Signature.fresh (Signature.construct (Sum.inr ⟨c, args⟩)) := by
          rw [Signature.fresh_construct]
          exact foldr_max_ge (fun j => args.get j) _ i (List.mem_finRange i)
        exact Nat.le_trans hle h_fresh

/-- `LawfulRestrict` for a signature's own type, packaged from the theorem above the way
`instLawfulComp` packages `pSubst_comp`. This is the instance that lets a *generic* consumer — one
holding only `[PrincipalElaborate N Tm Ty]`, with no `Signature` anywhere in sight — prune a
computed substitution down to its source's threshold. -/
instance instLawfulRestrict {α : Type} [Signature α] : LawfulRestrict α α where
  pSubst_restrictBelow := fun t σ n h => Signature.pSubst_restrictBelow σ n t h

theorem Signature.pSubst_insert_fresh {α : Type} [Signature α]
    (σ : Subst α) (k : Nat) (v : α) (t : α)
    (h_fresh : ¬ HasVars.isFree t k) :
    HasSubst.pSubst t (σ.insert k v) = HasSubst.pSubst t σ := by
  show Signature.pSubst t (σ.insert k v) = Signature.pSubst t σ
  induction t using Signature.term_ind with
  | var_case n =>
      rw [Signature.pSubst_var, Signature.pSubst_var,
          Std.HashMap.getD_insert]
      have hkn_ne : k ≠ n := by
        intro h; exact h_fresh ((Signature.isFree_var n k).mpr h)
      simp [hkn_ne]
  | construct_case c args ih =>
      rw [Signature.pSubst_construct, Signature.pSubst_construct]
      congr 3
      apply Vector.ext
      intro i hi
      have hget : ∀ (f : Fin (Signature.arity c) → α),
          (Vector.ofFn f)[i]'hi = f ⟨i, hi⟩ := fun _ => by simp
      rw [hget, hget]
      apply ih ⟨i, hi⟩
      intro h_arg_free
      exact h_fresh
        ((Signature.isFree_construct c args k).mpr ⟨⟨i, hi⟩, h_arg_free⟩)


