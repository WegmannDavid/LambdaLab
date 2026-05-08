import LambdaLab.Unification2.Term

/-! # Bridge lemmas for `Term C` (Fin-function args version) -/

namespace LambdaLab.Unification2

namespace Term

variable {C : Type}

/-! ## `pSubst` β-laws (definitional) -/

@[simp] theorem pSubst_var (n : Nat) (σ : Subst (Term C)) :
    pSubst σ (.var n) = σ.getD n (.var n) := rfl

@[simp] theorem pSubst_app (c : C) (k : Nat) (args : Fin k → Term C)
    (σ : Subst (Term C)) :
    pSubst σ (.app c k args) = .app c k (fun i => pSubst σ (args i)) := rfl

/-! ## `occurs` β-laws (definitional) -/

@[simp] theorem occurs_var (n m : Nat) :
    occurs (C := C) n (.var m) = decide (n = m) := rfl

@[simp] theorem occurs_app (n : Nat) (c : C) (k : Nat) (args : Fin k → Term C) :
    occurs n (.app c k args) =
      (List.finRange k).any (fun i => occurs n (args i)) := rfl

@[simp] theorem fresh_var (n : Nat) : fresh (.var n : Term C) = n + 1 := rfl

@[simp] theorem fresh_app (c : C) (k : Nat) (args : Fin k → Term C) :
    fresh (.app c k args) =
      (List.finRange k).foldr (fun i acc => max acc (fresh (args i))) 0 := rfl

/-! ## `pSubst` with empty substitution is the identity -/

theorem pSubst_empty : ∀ (t : Term C), pSubst (∅ : Subst (Term C)) t = t := by
  intro t
  induction t with
  | var n => simp [pSubst, Std.HashMap.getD_empty]
  | app c k args ih =>
      rw [pSubst_app]
      congr; funext i
      exact ih i

/-! ## `single` lemmas -/

theorem single_var_self : ∀ (t : Term C) (n : Nat),
    single t n (.var n) = t := by
  intro t n
  induction t with
  | var m =>
      show pSubst _ (.var m) = .var m
      rw [pSubst_var, Std.HashMap.getD_insert]
      by_cases hnm : n = m
      · subst hnm; simp
      · simp [hnm, Std.HashMap.getD_empty]
  | app c k args ih =>
      show pSubst _ (.app c k args) = _
      rw [pSubst_app]
      congr; funext i; exact ih i

/-- Singleton substitution at a non-occurring index is identity. -/
theorem single_off : ∀ (t : Term C) (n : Nat) (s : Term C),
    occurs n t = false → single t n s = t := by
  intro t n s
  induction t with
  | var m =>
      intro h
      show pSubst _ (.var m) = .var m
      rw [pSubst_var, Std.HashMap.getD_insert]
      have hnm : n ≠ m := by
        intro hnm; rw [occurs_var] at h; simp [hnm] at h
      simp [hnm, Std.HashMap.getD_empty]
  | app c k args ih =>
      intro h
      show pSubst _ (.app c k args) = _
      rw [pSubst_app]
      rw [occurs_app, List.any_eq_false] at h
      congr; funext i
      apply ih i
      have hni : ¬ occurs n (args i) = true := h i (List.mem_finRange i)
      cases hb : occurs n (args i)
      · rfl
      · exact absurd hb hni

/-! ## `decomp` shape -/

theorem decomp_eq_some [DecidableEq C] {x y : Term C} {xs : Equations C}
    (hd : decomp x y = some xs) :
    ∃ (c : C) (k : Nat) (argsx argsy : Fin k → Term C),
      x = .app c k argsx ∧ y = .app c k argsy ∧
      xs = (List.finRange k).map (fun i => (argsx i, argsy i)) := by
  cases x with
  | var _ => simp [decomp] at hd
  | app cx nx argsx =>
      cases y with
      | var _ => simp [decomp] at hd
      | app cy ny argsy =>
          simp only [decomp] at hd
          split at hd
          · rename_i hcc
            obtain ⟨hcx, hnx⟩ := hcc
            subst hcx hnx
            injection hd with hxs
            refine ⟨cx, nx, argsx, argsy, rfl, rfl, hxs.symm⟩
          · cases hd

/-! ## `fresh` strictly dominates every variable that occurs -/

theorem fresh_gt_occurs : ∀ (t : Term C) (n : Nat),
    occurs n t = true → n < fresh t := by
  intro t n
  induction t with
  | var m =>
      intro h
      rw [occurs_var] at h
      have : n = m := of_decide_eq_true h
      subst this
      show n < n + 1; omega
  | app c k args ih =>
      intro h
      rw [occurs_app, List.any_eq_true] at h
      obtain ⟨i, _, hi⟩ := h
      rw [fresh_app]
      have hii := ih i hi
      -- need: n < (List.finRange k).foldr ... 0; from hii (n < fresh (args i)) and
      --   args i is in the foldr.
      have hmem : i ∈ List.finRange k := List.mem_finRange i
      revert hmem
      induction List.finRange k with
      | nil => intro h; cases h
      | cons j js ihl =>
          intro hmem
          simp only [List.foldr]
          rcases List.mem_cons.mp hmem with rfl | hj
          · exact Nat.lt_of_lt_of_le hii (Nat.le_max_right _ _)
          · exact Nat.lt_of_lt_of_le (ihl hj) (Nat.le_max_left _ _)

/-! ## Free variables under `single` -/

theorem single_isFree : ∀ (t : Term C) (n : Nat) (s : Term C) (m : Nat),
    occurs m (single t n s) = true ↔
      (m ≠ n ∧ occurs m t = true) ∨ (occurs n t = true ∧ occurs m s = true) := by
  intro t n s m
  induction t with
  | var k =>
      show occurs m (pSubst _ (.var k)) = true ↔ _
      rw [pSubst_var, Std.HashMap.getD_insert]
      by_cases hnk : n = k
      · subst hnk
        simp only [BEq.rfl, ↓reduceIte, occurs_var]
        constructor
        · intro hms; right; refine ⟨?_, hms⟩; simp
        · rintro (⟨hmn, hmk⟩ | ⟨_, hsm⟩)
          · exfalso; rw [decide_eq_true_iff] at hmk; exact hmn hmk
          · exact hsm
      · have hbeq : (n == k) = false := by simp [hnk]
        rw [hbeq]
        simp only [Bool.false_eq_true, ↓reduceIte, Std.HashMap.getD_empty]
        rw [occurs_var, occurs_var]
        constructor
        · intro hmk
          left
          refine ⟨?_, hmk⟩
          intro hmn
          rw [decide_eq_true_iff] at hmk
          subst hmn; exact hnk hmk
        · rintro (⟨_, hmk⟩ | ⟨hkn, _⟩)
          · exact hmk
          · exfalso
            rw [decide_eq_true_iff] at hkn
            exact hnk hkn
  | app c k args ih =>
      show occurs m (pSubst _ (.app c k args)) = true ↔ _
      simp only [pSubst_app, occurs_app, List.any_eq_true]
      constructor
      · rintro ⟨i, _, hi⟩
        rcases (ih i).mp hi with ⟨hmn, hm⟩ | ⟨hn, hms⟩
        · exact Or.inl ⟨hmn, ⟨i, List.mem_finRange i, hm⟩⟩
        · exact Or.inr ⟨⟨i, List.mem_finRange i, hn⟩, hms⟩
      · rintro (⟨hmn, ⟨i, _, hm⟩⟩ | ⟨⟨i, _, hn⟩, hms⟩)
        · exact ⟨i, List.mem_finRange i, (ih i).mpr (Or.inl ⟨hmn, hm⟩)⟩
        · exact ⟨i, List.mem_finRange i, (ih i).mpr (Or.inr ⟨hn, hms⟩)⟩

/-! ## Free variables under `decomp` -/

theorem decomp_isFree [DecidableEq C] (x y : Term C) (xs : Equations C) (n : Nat)
    (hd : decomp x y = some xs)
    (hxs : ∃ p ∈ xs, occurs n p.1 = true ∨ occurs n p.2 = true) :
    occurs n x = true ∨ occurs n y = true := by
  obtain ⟨c, k, argsx, argsy, hxc, hyc, hxsxs⟩ := decomp_eq_some hd
  subst hxc hyc
  rw [hxsxs] at hxs
  obtain ⟨p, hp, hor⟩ := hxs
  rw [List.mem_map] at hp
  obtain ⟨i, _, hp_eq⟩ := hp
  subst hp_eq
  rcases hor with h1 | h2
  · left
    rw [occurs_app, List.any_eq_true]
    exact ⟨i, List.mem_finRange i, h1⟩
  · right
    rw [occurs_app, List.any_eq_true]
    exact ⟨i, List.mem_finRange i, h2⟩

/-! ## Size and decomp -/

theorem size_decomp [DecidableEq C] (x y : Term C) (xs : Equations C)
    (hd : decomp x y = some xs) :
    xs.foldr (fun p acc => acc + size p.1 + size p.2) 0 < size x + size y := by
  obtain ⟨c, k, argsx, argsy, hxc, hyc, hxs⟩ := decomp_eq_some hd
  subst hxs hxc hyc
  rw [List.foldr_map]
  show (List.finRange k).foldr (fun i acc => acc + size (argsx i) + size (argsy i)) 0 <
    size (.app c k argsx) + size (.app c k argsy)
  rw [size, size]
  generalize List.finRange k = L
  induction L with
  | nil => simp
  | cons j js ih =>
      simp only [List.foldr]
      omega

/-! ## Misc lemmas -/

theorem var_of_isVar (t : Term C) (n : Nat) : isVar t = some n → t = .var n := by
  intro h
  cases t with
  | var m => simp [isVar] at h; rw [h]
  | app _ _ _ => simp [isVar] at h

theorem pSubst_var_eq (n : Nat) (s : Term C) :
    pSubst ((∅ : Subst (Term C)).insert n s) (.var n) = s := by
  rw [pSubst_var]
  exact Std.HashMap.getD_insert_self

end Term

/-! ## Equations under `single` -/

theorem Equations.single_eq {C : Type} (eqs : Equations C) (n : Nat) (s : Term C) :
    eqs.map (fun p => (Term.single p.1 n s, Term.single p.2 n s)) =
      eqs.map (fun p => (Term.single p.1 n s, Term.single p.2 n s)) := rfl

/-! ## Unifier-level bridges -/

namespace Unifier

variable {C : Type}

theorem apply_var_self (l : Unifier C) (n : Nat) (s : Term C)
    (hns : l.apply (.var n) = l.apply s) :
    l.apply (.var n) = l.apply s := hns

/-- `Unifier.apply` distributes over `app`. -/
theorem apply_app (l : Unifier C) (c : C) (k : Nat) (args : Fin k → Term C) :
    l.apply (.app c k args) = .app c k (fun i => l.apply (args i)) := by
  induction l generalizing args with
  | nil => simp [apply_nil]
  | cons p rest ih =>
      obtain ⟨n, s⟩ := p
      rw [apply_cons]
      show apply rest (Term.pSubst _ (.app c k args)) = _
      rw [Term.pSubst_app, ih]
      apply congrArg
      funext i
      rfl

/-- **Unifier absorption.** If `l.apply (var n) = l.apply s`, then
prepending `[n ↦ s]` to any term `t` doesn't change `l`'s result. -/
theorem absorb (l : Unifier C) (t : Term C) (n : Nat) (s : Term C)
    (hns : l.apply (.var n) = l.apply s) :
    l.apply (Term.single t n s) = l.apply t := by
  induction t with
  | var k =>
      show l.apply (Term.pSubst _ (.var k)) = l.apply (.var k)
      rw [Term.pSubst_var, Std.HashMap.getD_insert]
      by_cases hnk : n = k
      · subst hnk; simp; exact hns.symm
      · have hbeq : (n == k) = false := by simp [hnk]
        rw [hbeq]; simp [Std.HashMap.getD_empty]
  | app c k args ih =>
      show l.apply (Term.pSubst _ (.app c k args)) = l.apply (.app c k args)
      rw [Term.pSubst_app, apply_app, apply_app]
      congr; funext i; exact ih i

/-- **Decomposition under unifier (forward).** If `l` unifies each pair
in `xs` and `decomp x y = some xs`, then `l.apply x = l.apply y`. -/
theorem decomp_apply_sound [DecidableEq C] (l : Unifier C) (x y : Term C)
    (xs : Equations C) (hd : Term.decomp x y = some xs)
    (hu : ∀ p ∈ xs, l.apply p.1 = l.apply p.2) :
    l.apply x = l.apply y := by
  obtain ⟨c, k, argsx, argsy, hxc, hyc, hxs⟩ := Term.decomp_eq_some hd
  subst hxs hxc hyc
  rw [apply_app, apply_app]
  congr; funext i
  exact hu (argsx i, argsy i) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

end Unifier

end LambdaLab.Unification2
