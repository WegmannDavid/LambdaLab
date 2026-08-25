import LambdaLab.Nominal.Unification.Basic
import LambdaLab.Nominal.Unification.Soundness

open LambdaLab.Nominal

/-! # Completeness of `unifyList`

If any unifier exists, the algorithm succeeds. Carries over from the
fat-typeclass version on `archive/fat-unification`. -/

/-- Pull the head equation out of a `Subst`-form unifier, in the `Signature.pSubst` spelling the
helper lemmas use. -/
theorem Subst.Unifies.head_eq {A α : Type} [Atom A] [Signature A α] {σ : Subst A α} {x y : α}
    {eqs' : Equations α} (hσ : Subst.Unifies σ ((x, y) :: eqs')) :
    Signature.pSubst x σ = Signature.pSubst y σ :=
  hσ (x, y) List.mem_cons_self

/-- **Completeness of `unifyList`.** If any unifier exists for `eqs`, then
`unifyList eqs` succeeds. Equivalently — and more usefully in this
contrapositive form — if `unifyList eqs = none`, no unifier exists. Proved by
induction on `unifyList.induct`: success branches close trivially; failure
branches each contradict the unifier-exists hypothesis using one of
`occurs_no_unifier`, `decomp_none_no_unifier`, or `unifier_absorb`. The
mechanical `unifyList` case-split is dispatched by `grind [unifyList]`. -/
theorem unifyList_complete {A α : Type} [Atom A] [Signature A α] :
    ∀ (eqs : Equations α) (σ : Subst A α),
      Subst.Unifies σ eqs → unifyList eqs ≠ none := by
  intro eqs
  induction eqs using unifyList.induct with
  | case1 => intro σ _ heq; rw [unifyList] at heq; cases heq
  | case2 x y eqs' m hxv hyv ih =>
      intro σ hσ heq
      have heq : unifyList eqs' = none := by grind [unifyList]
      exact ih σ (fun p hp => hσ p (List.mem_cons_of_mem _ hp)) heq
  | case3 x y eqs' m hxv hyv hocc =>
      intro σ hσ _
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hxeq : x = Signature.var m := Signature.var_of_isVar x m hxv
      rw [hxeq] at hxy
      exact Signature.occurs_no_unifier y m σ hocc hyv hxy
  | case4 _ _ _ _ _ _ _ _ _ _ => intro _ _ heq; grind [unifyList]
  | case5 x y eqs' m hxv hyv hocc hnone ih =>
      intro σ hσ _
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hxeq : x = Signature.var m := Signature.var_of_isVar x m hxv
      rw [hxeq] at hxy
      have hσ_sub : Subst.Unifies σ (HasSubst.single eqs' m y) := by
        intro p hp
        rw [Equations.single_eq] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, hqeq⟩
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        simp only [Signature.hasSubst_pSubst_eq]
        rw [Signature.unifier_absorb σ q.1 m y hxy,
            Signature.unifier_absorb σ q.2 m y hxy]
        exact hq_unif
      exact ih σ hσ_sub hnone
  | case6 x y eqs' hxv m hyv hocc =>
      intro σ hσ _
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hyeq : y = Signature.var m := Signature.var_of_isVar y m hyv
      rw [hyeq] at hxy
      have hxv' : Signature.isVar x ≠ some m := by rw [hxv]; intro h; cases h
      exact Signature.occurs_no_unifier x m σ hocc hxv' hxy.symm
  | case7 _ _ _ _ _ _ _ _ _ _ => intro _ _ heq; grind [unifyList]
  | case8 x y eqs' hxv m hyv hocc hnone ih =>
      intro σ hσ _
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hyeq : y = Signature.var m := Signature.var_of_isVar y m hyv
      rw [hyeq] at hxy
      have hxy' : Signature.pSubst (Signature.var m) σ = Signature.pSubst x σ := hxy.symm
      have hσ_sub : Subst.Unifies σ (HasSubst.single eqs' m x) := by
        intro p hp
        rw [Equations.single_eq] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, hqeq⟩
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        simp only [Signature.hasSubst_pSubst_eq]
        rw [Signature.unifier_absorb σ q.1 m x hxy',
            Signature.unifier_absorb σ q.2 m x hxy']
        exact hq_unif
      exact ih σ hσ_sub hnone
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro σ hσ heq
      have heq : unifyList (xs ++ eqs') = none := by grind [unifyList]
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hσ' : Subst.Unifies σ (xs ++ eqs') := by
        intro p hp
        rcases List.mem_append.mp hp with hp_xs | hp_eqs'
        · exact Signature.decomp_unifier_sound x y xs σ hdec hxy p hp_xs
        · exact hσ p (List.mem_cons_of_mem _ hp_eqs')
      exact ih σ hσ' heq
  | case10 x y eqs' hxv hyv hdec =>
      intro σ hσ _
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      exact Signature.decomp_none_no_unifier x y σ hxv hyv hdec hxy

/-! ## Public completeness. -/

/-- **Completeness of `unify`.** If *any* substitution unifies `eqs`, then `unify eqs` succeeds.

The witness is an arbitrary parallel `Subst A α`, matching the textbook definition of a unifier
(any substitution σ with Eσ = Dσ). It used to be a list-form `Unifier A α`, which forced callers
to convert — and an arbitrary `Subst A α` cannot be converted: `Unifier.toSubst`'s image contains
only the acyclic substitutions, so e.g. the swap `{0 ↦ ?1, 1 ↦ ?0}` is not in it. The induction
never needed the list structure, only the action, which is why generalising the hypothesis was
the fix. -/
theorem unify_complete {A α : Type} [Atom A] [Signature A α] :
    ∀ (eqs : Equations α) (σ : Subst A α),
      Subst.Unifies σ eqs → unify eqs ≠ none := by
  intro eqs σ hσ heq
  rw [unify, Option.map_eq_none_iff] at heq
  exact unifyList_complete eqs σ hσ heq

/-- List-form corollary, for callers holding a `Unifier A α` (e.g. the empty unifier for trivially
unifiable equations). This direction is the easy one — `toSubst` always exists. -/
theorem unify_complete_unifier {A α : Type} [Atom A] [Signature A α] :
    ∀ (eqs : Equations α) (u : Unifier A α),
      u.Unifies eqs → unify eqs ≠ none := by
  intro eqs u hu
  refine unify_complete eqs u.toSubst (fun p hp => ?_)
  have h := hu p hp
  rwa [Unifier.apply_eq_pSubst_toSubst, Unifier.apply_eq_pSubst_toSubst] at h

/-! ## Domain of the computed unifier

`unify` never invents variables: everything it binds occurred free in the equations. Needed
wherever the result is pruned down to an atom set (`Subst.restrictTo`) — the pruning is
only harmless because the domain is bounded.
-/

/-- Every variable `unifyList` binds was free in the equations it was given. -/
theorem unifyList_keys {A α : Type} [Atom A] [Signature A α] :
    ∀ (eqs : Equations α) (u : Unifier A α), unifyList eqs = some u →
      ∀ p ∈ u, HasVars.isFree eqs p.1 := by
  intro eqs
  induction eqs using unifyList.induct with
  | case1 => intro u hu p hp; rw [unifyList] at hu; cases hu; cases hp
  | case2 x y eqs' m hxv hyv ih =>
      intro u hu p hp
      have hu' : unifyList eqs' = some u := by grind [unifyList]
      obtain ⟨q, hq, hqf⟩ := ih u hu' p hp
      exact ⟨q, List.mem_cons_of_mem _ hq, hqf⟩
  | case3 _ _ _ _ _ _ _ => intro u hu; grind [unifyList]
  | case4 x y eqs' m hxv hyv hocc rest hrest ih =>
      intro u hu p hp
      have hueq : (m, y) :: rest = u := by grind [unifyList]
      subst hueq
      have hxeq : x = Signature.var m := Signature.var_of_isVar x m hxv
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨(x, y), List.mem_cons_self, Or.inl (by rw [hxeq]; exact (Signature.var_isFree m m).mpr rfl)⟩
      · obtain ⟨q, hq, hqf⟩ := ih rest hrest p hp'
        rw [Equations.single_eq] at hq
        rcases List.mem_map.mp hq with ⟨r, hr, hreq⟩
        subst hreq
        have : HasVars.isFree r.1 p.1 ∨ HasVars.isFree r.2 p.1 ∨ HasVars.isFree y p.1 := by
          rcases hqf with h1 | h2
          · rcases (Signature.single_isFree r.1 m y p.1).mp h1 with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          · rcases (Signature.single_isFree r.2 m y p.1).mp h2 with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        rcases this with h | h | h
        · exact ⟨r, List.mem_cons_of_mem _ hr, Or.inl h⟩
        · exact ⟨r, List.mem_cons_of_mem _ hr, Or.inr h⟩
        · exact ⟨(x, y), List.mem_cons_self, Or.inr h⟩
  | case5 _ _ _ _ _ _ _ _ _ => intro u hu; grind [unifyList]
  | case6 _ _ _ _ _ _ _ => intro u hu; grind [unifyList]
  | case7 x y eqs' hxv m hyv hocc rest hrest ih =>
      intro u hu p hp
      have hueq : (m, x) :: rest = u := by grind [unifyList]
      subst hueq
      have hyeq : y = Signature.var m := Signature.var_of_isVar y m hyv
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨(x, y), List.mem_cons_self, Or.inr (by rw [hyeq]; exact (Signature.var_isFree m m).mpr rfl)⟩
      · obtain ⟨q, hq, hqf⟩ := ih rest hrest p hp'
        rw [Equations.single_eq] at hq
        rcases List.mem_map.mp hq with ⟨r, hr, hreq⟩
        subst hreq
        have : HasVars.isFree r.1 p.1 ∨ HasVars.isFree r.2 p.1 ∨ HasVars.isFree x p.1 := by
          rcases hqf with h1 | h2
          · rcases (Signature.single_isFree r.1 m x p.1).mp h1 with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          · rcases (Signature.single_isFree r.2 m x p.1).mp h2 with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        rcases this with h | h | h
        · exact ⟨r, List.mem_cons_of_mem _ hr, Or.inl h⟩
        · exact ⟨r, List.mem_cons_of_mem _ hr, Or.inr h⟩
        · exact ⟨(x, y), List.mem_cons_self, Or.inl h⟩
  | case8 _ _ _ _ _ _ _ _ _ => intro u hu; grind [unifyList]
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro u hu p hp
      have hu' : unifyList (xs ++ eqs') = some u := by grind [unifyList]
      obtain ⟨q, hq, hqf⟩ := ih u hu' p hp
      rcases List.mem_append.mp hq with hq_xs | hq_eqs'
      · have hxs : HasVars.isFree xs p.1 := ⟨q, hq_xs, hqf⟩
        rcases Signature.decomp_isFree x y xs p.1 hdec hxs with h | h
        · exact ⟨(x, y), List.mem_cons_self, Or.inl h⟩
        · exact ⟨(x, y), List.mem_cons_self, Or.inr h⟩
      · exact ⟨q, List.mem_cons_of_mem _ hq_eqs', hqf⟩
  | case10 _ _ _ _ _ _ => intro u hu; grind [unifyList]

/-- Keys of `toSubst u` are the variables `u` binds. -/
theorem Unifier.toSubst_mem_keys {A α : Type} [Atom A] [Signature A α] :
    ∀ (u : Unifier A α) (k : A), (Unifier.toSubst u).get? k ≠ none → ∃ p ∈ u, p.1 = k
  | [], k, h => by
      rw [Unifier.toSubst_nil] at h
      simp [Std.HashMap.get?_eq_getElem?] at h
  | (n, s) :: rest, k, h => by
      rw [Unifier.toSubst_cons, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert] at h
      by_cases hnk : n = k
      · exact ⟨(n, s), List.mem_cons_self, hnk⟩
      · rw [if_neg (by simp [hnk])] at h
        obtain ⟨p, hp, hpk⟩ :=
          Unifier.toSubst_mem_keys rest k (by rwa [Std.HashMap.get?_eq_getElem?])
        exact ⟨p, List.mem_cons_of_mem _ hp, hpk⟩

/-- **Domain of `unify`.** Every variable the computed unifier binds was free in the equations. -/
theorem unify_keys {A α : Type} [Atom A] [Signature A α] (eqs : Equations α) (σ : Subst A α)
    (h : unify eqs = some σ) (k : A) (hk : σ.get? k ≠ none) : HasVars.isFree eqs k := by
  rw [unify, Option.map_eq_some_iff] at h
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨p, hp, rfl⟩ := Unifier.toSubst_mem_keys u k hk
  exact unifyList_keys eqs u hu p hp

/-- **Range of `unifyList`.** Every variable appearing in a bound *value* was free in the
equations. Companion to `unifyList_keys`, same induction. -/
theorem unifyList_range {A α : Type} [Atom A] [Signature A α] :
    ∀ (eqs : Equations α) (u : Unifier A α), unifyList eqs = some u →
      ∀ p ∈ u, ∀ m, HasVars.isFree p.2 m → HasVars.isFree eqs m := by
  intro eqs
  induction eqs using unifyList.induct with
  | case1 => intro u hu p hp; rw [unifyList] at hu; cases hu; cases hp
  | case2 x y eqs' m hxv hyv ih =>
      intro u hu p hp k hk
      have hu' : unifyList eqs' = some u := by grind [unifyList]
      obtain ⟨q, hq, hqf⟩ := ih u hu' p hp k hk
      exact ⟨q, List.mem_cons_of_mem _ hq, hqf⟩
  | case3 _ _ _ _ _ _ _ => intro u hu; grind [unifyList]
  | case4 x y eqs' m hxv hyv hocc rest hrest ih =>
      intro u hu p hp k hk
      have hueq : (m, y) :: rest = u := by grind [unifyList]
      subst hueq
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨(x, y), List.mem_cons_self, Or.inr hk⟩
      · obtain ⟨q, hq, hqf⟩ := ih rest hrest p hp' k hk
        rw [Equations.single_eq] at hq
        rcases List.mem_map.mp hq with ⟨r, hr, hreq⟩
        subst hreq
        have : HasVars.isFree r.1 k ∨ HasVars.isFree r.2 k ∨ HasVars.isFree y k := by
          rcases hqf with h1 | h2
          · rcases (Signature.single_isFree r.1 m y k).mp h1 with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          · rcases (Signature.single_isFree r.2 m y k).mp h2 with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        rcases this with h | h | h
        · exact ⟨r, List.mem_cons_of_mem _ hr, Or.inl h⟩
        · exact ⟨r, List.mem_cons_of_mem _ hr, Or.inr h⟩
        · exact ⟨(x, y), List.mem_cons_self, Or.inr h⟩
  | case5 _ _ _ _ _ _ _ _ _ => intro u hu; grind [unifyList]
  | case6 _ _ _ _ _ _ _ => intro u hu; grind [unifyList]
  | case7 x y eqs' hxv m hyv hocc rest hrest ih =>
      intro u hu p hp k hk
      have hueq : (m, x) :: rest = u := by grind [unifyList]
      subst hueq
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨(x, y), List.mem_cons_self, Or.inl hk⟩
      · obtain ⟨q, hq, hqf⟩ := ih rest hrest p hp' k hk
        rw [Equations.single_eq] at hq
        rcases List.mem_map.mp hq with ⟨r, hr, hreq⟩
        subst hreq
        have : HasVars.isFree r.1 k ∨ HasVars.isFree r.2 k ∨ HasVars.isFree x k := by
          rcases hqf with h1 | h2
          · rcases (Signature.single_isFree r.1 m x k).mp h1 with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          · rcases (Signature.single_isFree r.2 m x k).mp h2 with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        rcases this with h | h | h
        · exact ⟨r, List.mem_cons_of_mem _ hr, Or.inl h⟩
        · exact ⟨r, List.mem_cons_of_mem _ hr, Or.inr h⟩
        · exact ⟨(x, y), List.mem_cons_self, Or.inl h⟩
  | case8 _ _ _ _ _ _ _ _ _ => intro u hu; grind [unifyList]
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro u hu p hp k hk
      have hu' : unifyList (xs ++ eqs') = some u := by grind [unifyList]
      obtain ⟨q, hq, hqf⟩ := ih u hu' p hp k hk
      rcases List.mem_append.mp hq with hq_xs | hq_eqs'
      · have hxs : HasVars.isFree xs k := ⟨q, hq_xs, hqf⟩
        rcases Signature.decomp_isFree x y xs k hdec hxs with h | h
        · exact ⟨(x, y), List.mem_cons_self, Or.inl h⟩
        · exact ⟨(x, y), List.mem_cons_self, Or.inr h⟩
      · exact ⟨q, List.mem_cons_of_mem _ hq_eqs', hqf⟩
  | case10 _ _ _ _ _ _ => intro u hu; grind [unifyList]

/-- Values of `toSubst u` only mention variables appearing in `u`'s values. -/
theorem Unifier.toSubst_range {A α : Type} [Atom A] [Signature A α] :
    ∀ (u : Unifier A α) (k : A) (v : α), (Unifier.toSubst u).get? k = some v →
      ∀ m, HasVars.isFree v m → ∃ p ∈ u, HasVars.isFree p.2 m
  | [], k, v, h, m, hm => by
      rw [Unifier.toSubst_nil] at h
      simp [Std.HashMap.get?_eq_getElem?] at h
  | (n, s) :: rest, k, v, h, m, hm => by
      rw [Unifier.toSubst_cons, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert] at h
      by_cases hnk : n = k
      · rw [if_pos (by simp [hnk])] at h
        obtain rfl := Option.some.inj h
        obtain ⟨k', hk', hk'm⟩ := Signature.isFree_pSubst s (Unifier.toSubst rest) m hm
        cases hg : (Unifier.toSubst rest).get? k' with
        | none =>
            have he : (Unifier.toSubst rest).getD k' (Signature.var k') = Signature.var k' := by
              rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?, hg]; rfl
            rw [he] at hk'm
            obtain rfl := (Signature.var_isFree k' m).mp hk'm
            exact ⟨(n, s), List.mem_cons_self, hk'⟩
        | some v' =>
            have he : (Unifier.toSubst rest).getD k' (Signature.var k') = v' := by
              rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?, hg]; rfl
            rw [he] at hk'm
            obtain ⟨p, hp, hpm⟩ := Unifier.toSubst_range rest k' v' hg m hk'm
            exact ⟨p, List.mem_cons_of_mem _ hp, hpm⟩
      · rw [if_neg (by simp [hnk])] at h
        obtain ⟨p, hp, hpm⟩ :=
          Unifier.toSubst_range rest k v (by rwa [Std.HashMap.get?_eq_getElem?]) m hm
        exact ⟨p, List.mem_cons_of_mem _ hp, hpm⟩

/-- **Range of `unify`.** Everything mentioned in a computed value was free in the equations.
With `unify_keys` (domain) this pins the whole substitution inside the equations' variables. -/
theorem unify_range {A α : Type} [Atom A] [Signature A α] (eqs : Equations α) (σ : Subst A α)
    (h : unify eqs = some σ) (k : A) (v : α) (hkv : σ.get? k = some v)
    (m : A) (hm : HasVars.isFree v m) : HasVars.isFree eqs m := by
  rw [unify, Option.map_eq_some_iff] at h
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨p, hp, hpm⟩ := Unifier.toSubst_range u k v hkv m hm
  exact unifyList_range eqs u hu p hp m hpm

/-! ## Support: a substitution confined to a range of variables

`unify_keys` + `unify_range` say the computed substitution lives inside the equations' variables.
`SupportedIn` packages that as one predicate and closes it under the operations the
principal-types proof composes with.
-/

/-- `σ` only mentions atoms of `s`, in its domain *and* its values. The order-free
`SupportedBelow`. -/
def SupportedIn {A α : Type} [Atom A] [Signature A α] (s : List A) (σ : Subst A α) : Prop :=
  ∀ k v, σ.get? k = some v → k ∈ s ∧ ∀ m, HasVars.isFree v m → m ∈ s

/-- `unify`'s answer is supported inside the equations' own variables — domain by `unify_keys`,
values by `unify_range`. -/
theorem unify_supported {A α : Type} [Atom A] [Signature A α] (eqs : Equations α) (σ : Subst A α)
    (h : unify eqs = some σ) : SupportedIn (HasVars.supp eqs) σ := by
  intro k v hkv
  refine ⟨(HasVars.mem_supp_iff_isFree _ _).mpr
      (unify_keys eqs σ h k (by rw [hkv]; exact Option.some_ne_none v)),
    fun m hm => (HasVars.mem_supp_iff_isFree _ _).mpr (unify_range eqs σ h k v hkv m hm)⟩

/-- Support is closed under composition. -/
theorem SupportedIn.comp {A α : Type} [Atom A] [Signature A α] {s : List A} {σ₂ σ₁ : Subst A α}
    (h₂ : SupportedIn s σ₂) (h₁ : SupportedIn s σ₁) :
    SupportedIn s (Subst.comp σ₂ σ₁) := by
  intro k v hkv
  rw [Subst.comp_get?] at hkv
  cases h1k : σ₁.get? k with
  | none =>
      rw [h1k] at hkv
      exact h₂ k v hkv
  | some t =>
      rw [h1k] at hkv
      obtain rfl := Option.some.inj hkv
      refine ⟨(h₁ k t h1k).1, fun m hm => ?_⟩
      obtain ⟨k', hk', hk'm⟩ := Signature.isFree_pSubst t σ₂ m hm
      have hk'n : k' ∈ s := (h₁ k t h1k).2 k' hk'
      cases h2 : σ₂.get? k' with
      | none =>
          have he : σ₂.getD k' (Signature.var k') = Signature.var k' := by
            rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?, h2]; rfl
          rw [he] at hk'm
          obtain rfl := (Signature.var_isFree k' m).mp hk'm
          exact hk'n
      | some v' =>
          have he : σ₂.getD k' (Signature.var k') = v' := by
            rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?, h2]; rfl
          rw [he] at hk'm
          exact (h₂ k' v' h2).2 m hk'm

/-- Substituting by a supported σ keeps a term inside the same atom set. -/
theorem SupportedIn.pSubst_supp {A α : Type} [Atom A] [Signature A α] {s : List A}
    {σ : Subst A α} (hσ : SupportedIn s σ) (t : α)
    (ht : ∀ a, HasVars.isFree t a → a ∈ s) :
    ∀ a, HasVars.isFree (HasSubst.pSubst t σ) a → a ∈ s := by
  intro m hm
  simp only [Signature.hasSubst_pSubst_eq] at hm
  obtain ⟨k, hk, hkm⟩ := Signature.isFree_pSubst t σ m hm
  have hkn : k ∈ s := ht k hk
  cases h : σ.get? k with
  | none =>
      have he : σ.getD k (Signature.var k) = Signature.var k := by
        rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?, h]; rfl
      rw [he] at hkm
      obtain rfl := (Signature.var_isFree k m).mp hkm
      exact hkn
  | some v =>
      have he : σ.getD k (Signature.var k) = v := by
        rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?, h]; rfl
      rw [he] at hkm
      exact (hσ k v h).2 m hkm

