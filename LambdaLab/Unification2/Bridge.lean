import LambdaLab.Unification2.Term

/-! # Bridge lemmas for `Term C`

Structural lemmas about `pSubst`, `single`, `decomp`, `occurs`, and the
unifier-level bridges needed for the unification algorithm and its
verification.

In contrast to the typeclass version, many lemmas that were
propositional in `Unification/Bridge.lean` are now definitional (`rfl`)
because there's no `construct`/`deconstruct` indirection. -/

namespace LambdaLab.Unification2

namespace Term

variable {C : Type}

/-! ## `pSubst` β-laws (definitional) -/

@[simp] theorem pSubst_var (n : Nat) (σ : Subst (Term C)) :
    pSubst σ (.var n) = σ.getD n (.var n) := rfl

@[simp] theorem pSubst_app (c : C) (args : List (Term C)) (σ : Subst (Term C)) :
    pSubst σ (.app c args) = .app c (pSubstList σ args) := rfl

@[simp] theorem pSubstList_nil (σ : Subst (Term C)) :
    pSubstList σ ([] : List (Term C)) = [] := rfl

@[simp] theorem pSubstList_cons (σ : Subst (Term C)) (t : Term C) (ts : List (Term C)) :
    pSubstList σ (t :: ts) = pSubst σ t :: pSubstList σ ts := rfl

theorem pSubstList_length (σ : Subst (Term C)) :
    ∀ (ts : List (Term C)), (pSubstList σ ts).length = ts.length
  | []      => rfl
  | _ :: ts => by simp [pSubstList_length σ ts]

/-! ## `pSubst` with empty substitution is the identity -/

mutual
  theorem pSubst_empty : ∀ (t : Term C), pSubst (∅ : Subst (Term C)) t = t
    | .var n      => by simp [pSubst, Std.HashMap.getD_empty]
    | .app c args => by
        rw [pSubst_app]
        congr 1
        exact pSubstList_empty args
  theorem pSubstList_empty : ∀ (ts : List (Term C)),
      pSubstList (∅ : Subst (Term C)) ts = ts
    | []      => rfl
    | t :: ts => by
        rw [pSubstList_cons, pSubst_empty t, pSubstList_empty ts]
end

/-! ## `occurs` β-laws (definitional) -/

@[simp] theorem occurs_var (n m : Nat) :
    occurs (C := C) n (.var m) = decide (n = m) := rfl

@[simp] theorem occurs_app (n : Nat) (c : C) (args : List (Term C)) :
    occurs n (.app c args) = occursList n args := rfl

@[simp] theorem occursList_nil (n : Nat) :
    occursList (C := C) n [] = false := rfl

@[simp] theorem occursList_cons (n : Nat) (t : Term C) (ts : List (Term C)) :
    occursList n (t :: ts) = (occurs n t || occursList n ts) := rfl

/-! ## `single` lemmas -/

mutual
  theorem single_var_self : ∀ (t : Term C) (n : Nat),
      single t n (.var n) = t
    | .var m, n => by
        show pSubst ((∅ : Subst (Term C)).insert n (.var n)) (.var m) = .var m
        rw [pSubst_var, Std.HashMap.getD_insert]
        by_cases hnm : n = m
        · subst hnm; simp
        · simp [hnm, Std.HashMap.getD_empty]
    | .app c args, n => by
        show pSubst _ (.app c args) = _
        rw [pSubst_app]
        congr 1
        exact singleList_var_self args n
  theorem singleList_var_self : ∀ (ts : List (Term C)) (n : Nat),
      pSubstList ((∅ : Subst (Term C)).insert n (.var n)) ts = ts
    | [], _ => rfl
    | t :: ts, n => by
        rw [pSubstList_cons]
        show pSubst _ t :: pSubstList _ ts = t :: ts
        congr 1
        · exact single_var_self t n
        · exact singleList_var_self ts n
end

mutual
  /-- A singleton substitution at an off-free-vars index is the identity. -/
  theorem single_off : ∀ (t : Term C) (n : Nat) (s : Term C),
      occurs n t = false → single t n s = t
    | .var m, n, s, h => by
        show pSubst ((∅ : Subst (Term C)).insert n s) (.var m) = .var m
        rw [pSubst_var, Std.HashMap.getD_insert]
        have hnm : n ≠ m := by
          intro hnm; rw [occurs_var] at h; simp [hnm] at h
        simp [hnm, Std.HashMap.getD_empty]
    | .app c args, n, s, h => by
        show pSubst _ (.app c args) = _
        rw [pSubst_app]
        rw [occurs_app] at h
        congr 1
        exact singleList_off args n s h
  theorem singleList_off : ∀ (ts : List (Term C)) (n : Nat) (s : Term C),
      occursList n ts = false →
      pSubstList ((∅ : Subst (Term C)).insert n s) ts = ts
    | [], _, _, _ => rfl
    | t :: ts, n, s, h => by
        rw [occursList_cons, Bool.or_eq_false_iff] at h
        rw [pSubstList_cons]
        congr 1
        · exact single_off t n s h.1
        · exact singleList_off ts n s h.2
end

/-! ## `decomp` shape -/

theorem decomp_eq_some [DecidableEq C] {x y : Term C} {xs : Equations C}
    (hd : decomp x y = some xs) :
    ∃ (c : C) (argsx argsy : List (Term C)),
      x = .app c argsx ∧ y = .app c argsy ∧
      argsx.length = argsy.length ∧ xs = argsx.zip argsy := by
  cases x with
  | var n => simp [decomp] at hd
  | app cx argsx =>
      cases y with
      | var n => simp [decomp] at hd
      | app cy argsy =>
          simp only [decomp] at hd
          split at hd
          · rename_i hcc
            injection hd with hxs
            refine ⟨cx, argsx, argsy, rfl, ?_, hcc.2, hxs.symm⟩
            rw [hcc.1]
          · cases hd

/-! ## Size and decomp -/

theorem sizeList_zip_le [DecidableEq C] : ∀ (xs ys : List (Term C)),
    xs.length = ys.length →
    (xs.zip ys).foldr (fun p acc => acc + size p.1 + size p.2) 0 ≤
      sizeList xs + sizeList ys
  | [], [], _ => by simp
  | x :: xs, y :: ys, h => by
      simp only [List.zip_cons_cons, List.foldr_cons, sizeList]
      have hlen : xs.length = ys.length := by
        simp at h; exact h
      have ih := sizeList_zip_le xs ys hlen
      omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem size_decomp [DecidableEq C] (x y : Term C) (xs : Equations C)
    (hd : decomp x y = some xs) :
    xs.foldr (fun p acc => acc + size p.1 + size p.2) 0 < size x + size y := by
  obtain ⟨c, argsx, argsy, hxc, hyc, hlen, hxs⟩ := decomp_eq_some hd
  subst hxs hxc hyc
  show (argsx.zip argsy).foldr (fun p acc => acc + size p.1 + size p.2) 0 <
    size (.app c argsx) + size (.app c argsy)
  rw [size, size]
  have h := sizeList_zip_le argsx argsy hlen
  omega

end Term

end LambdaLab.Unification2
