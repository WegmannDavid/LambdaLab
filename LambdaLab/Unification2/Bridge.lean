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

/-! ## Custom induction principle on `Term C`

`Term.rec` takes motives over both `Term` and `List Term`. The
combinator below sets `motive_2 := ∀ t ∈ ·, motive t`, giving a clean
"each argument satisfies the motive" induction hypothesis at the `app`
case. -/

theorem ind {motive : Term C → Prop}
    (var_case : ∀ n, motive (.var n))
    (app_case : ∀ (c : C) (args : List (Term C)),
      (∀ t ∈ args, motive t) → motive (.app c args))
    : ∀ t, motive t := by
  intro t
  refine @Term.rec C motive (fun ts => ∀ t ∈ ts, motive t) var_case app_case
    (fun _ h => by cases h)
    (fun head tail ih_head ih_tail t ht => ?_) t
  rcases List.mem_cons.mp ht with rfl | ht'
  · exact ih_head
  · exact ih_tail t ht'

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

/-! ## `fresh` strictly dominates every variable that occurs -/

theorem freshList_le_of_mem : ∀ {ts : List (Term C)} {t : Term C}, t ∈ ts →
    fresh t ≤ freshList ts
  | _ :: ts, t, h => by
      rcases List.mem_cons.mp h with rfl | hmem
      · show fresh t ≤ max (fresh t) (freshList ts); exact Nat.le_max_left _ _
      · have := freshList_le_of_mem (ts := ts) hmem
        show fresh t ≤ max _ (freshList ts); omega

theorem fresh_gt_occurs : ∀ (t : Term C) (n : Nat),
    occurs n t = true → n < fresh t := by
  intro t
  refine ind (motive := fun t => ∀ n, occurs n t = true → n < fresh t)
    ?var ?app t
  · intro m n hocc
    rw [occurs_var] at hocc
    have hnm : n = m := of_decide_eq_true hocc
    subst hnm
    show n < n + 1; omega
  · intro c args ih n hocc
    rw [occurs_app] at hocc
    show n < freshList args
    -- find the arg where occurs n holds, use ih
    induction args with
    | nil => simp [occursList] at hocc
    | cons a as iharg =>
        simp [occursList, Bool.or_eq_true] at hocc
        rcases hocc with h | h
        · have := ih a List.mem_cons_self n h
          simp [freshList]; omega
        · have ihres := iharg
            (fun t ht => ih t (List.mem_cons_of_mem _ ht))
            h
          simp [freshList]; omega

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

/-! ## Free variables under `single` -/

mutual
  /-- `single t n s` is free in `m` iff either: `m ≠ n` and `t` is free in `m`,
  or `t` is free in `n` and `s` is free in `m`. -/
  theorem single_isFree : ∀ (t : Term C) (n : Nat) (s : Term C) (m : Nat),
      occurs m (single t n s) = true ↔
        (m ≠ n ∧ occurs m t = true) ∨ (occurs n t = true ∧ occurs m s = true)
    | .var k, n, s, m => by
        show occurs m (pSubst _ (.var k)) = true ↔ _
        rw [pSubst_var, Std.HashMap.getD_insert]
        rw [occurs_var]
        by_cases hnk : n = k
        · subst hnk
          simp only [BEq.rfl, ↓reduceIte]
          rw [occurs_var]
          constructor
          · intro hmsm; right; exact ⟨by simp, hmsm⟩
          · rintro (⟨hmn, hmk⟩ | ⟨_, hsm⟩)
            · exfalso; rw [decide_eq_true_iff] at hmk; exact hmn hmk
            · exact hsm
        · have hbeq : (n == k) = false := by simp [hnk]
          rw [hbeq]
          simp only [Bool.false_eq_true, ↓reduceIte, Std.HashMap.getD_empty]
          rw [occurs_var]
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
              rw [occurs_var, decide_eq_true_iff] at hkn
              exact hnk hkn
    | .app c args, n, s, m => by
        show occurs m (pSubst _ (.app c args)) = true ↔ _
        rw [pSubst_app, occurs_app, occurs_app]
        exact singleList_isFree args n s m
  theorem singleList_isFree : ∀ (ts : List (Term C)) (n : Nat) (s : Term C) (m : Nat),
      occursList m (pSubstList ((∅ : Subst (Term C)).insert n s) ts) = true ↔
        (m ≠ n ∧ occursList m ts = true) ∨ (occursList n ts = true ∧ occurs m s = true)
    | [], n, s, m => by
        simp [pSubstList, occursList]
    | t :: ts, n, s, m => by
        rw [pSubstList_cons, occursList_cons, occursList_cons, occursList_cons]
        rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
        have h1 : occurs m (pSubst ((∅ : Subst (Term C)).insert n s) t) = true ↔ _ :=
          single_isFree t n s m
        have h2 : occursList m (pSubstList ((∅ : Subst (Term C)).insert n s) ts) = true ↔ _ :=
          singleList_isFree ts n s m
        rw [h1, h2]
        constructor
        · rintro ((⟨hmn, hmt⟩ | ⟨htn, hms⟩) | (⟨hmn, hmts⟩ | ⟨htsn, hms⟩))
          · exact Or.inl ⟨hmn, Or.inl hmt⟩
          · exact Or.inr ⟨Or.inl htn, hms⟩
          · exact Or.inl ⟨hmn, Or.inr hmts⟩
          · exact Or.inr ⟨Or.inr htsn, hms⟩
        · rintro (⟨hmn, hmt | hmts⟩ | ⟨htn | htsn, hms⟩)
          · exact Or.inl (Or.inl ⟨hmn, hmt⟩)
          · exact Or.inr (Or.inl ⟨hmn, hmts⟩)
          · exact Or.inl (Or.inr ⟨htn, hms⟩)
          · exact Or.inr (Or.inr ⟨htsn, hms⟩)
end

/-! ## Free variables under `decomp` and `single` -/

/-- If `n` occurs in any element of `ts`, then `occursList n ts = true`. -/
theorem occursList_of_mem : ∀ {ts : List (Term C)} {t : Term C} {n : Nat},
    t ∈ ts → occurs n t = true → occursList n ts = true
  | _ :: ts, t, n, ht, h => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · simp [occursList, h]
      · simp [occursList, occursList_of_mem ht' h]

/-- If `decomp x y = some xs` and `n` is free in `xs`, then `n` is free
in `x` or in `y`. -/
theorem decomp_isFree [DecidableEq C] (x y : Term C) (xs : Equations C) (n : Nat)
    (hd : decomp x y = some xs)
    (hxs : ∃ p ∈ xs, occurs n p.1 = true ∨ occurs n p.2 = true) :
    occurs n x = true ∨ occurs n y = true := by
  obtain ⟨c, argsx, argsy, hxc, hyc, _hlen, hxsxs⟩ := decomp_eq_some hd
  subst hxsxs hxc hyc
  obtain ⟨p, hp, hor⟩ := hxs
  -- p ∈ argsx.zip argsy ⟹ p.1 ∈ argsx, p.2 ∈ argsy
  have hp1 : p.1 ∈ argsx := List.of_mem_zip hp |>.1
  have hp2 : p.2 ∈ argsy := List.of_mem_zip hp |>.2
  rcases hor with h1 | h2
  · left; rw [occurs_app]; exact occursList_of_mem hp1 h1
  · right; rw [occurs_app]; exact occursList_of_mem hp2 h2

end Term

end LambdaLab.Unification2
