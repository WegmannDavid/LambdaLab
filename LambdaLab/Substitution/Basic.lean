import Std.Data.HashMap
import Std.Data.HashSet

-- naming convention
-- Nat variables
-- 𝕋 terms with variables
-- 𝕊 things that are substituted for variables


class HasVars (𝕋 : Type) where
  isFree : 𝕋 → Nat → Prop
  fresh : 𝕋 → Nat

  fresh_gt_free : ∀ x n, isFree x n → n < fresh x

/-- **Ground**: no metavariable occurs anywhere in `x`.

Stated as the absence of free variables rather than as `fresh x = 0`, because `fresh` is only
required to be an *upper bound* (`fresh_gt_free`) — an instance may over-approximate, so
`fresh x = 0` is sufficient for groundness but not necessary. `Ground.of_fresh_eq_zero` below is
that one sound direction. -/
def HasVars.Ground {𝕋 : Type} [HasVars 𝕋] (x : 𝕋) : Prop := ∀ n, ¬ HasVars.isFree x n

/-- A zero fresh-counter forces groundness: every free variable would have to be below it. -/
theorem HasVars.Ground.of_fresh_eq_zero {𝕋 : Type} [HasVars 𝕋] {x : 𝕋}
    (h : HasVars.fresh x = 0) : HasVars.Ground x :=
  fun n hn => Nat.not_lt_zero n (h ▸ HasVars.fresh_gt_free x n hn)

abbrev Subst (𝕊 : Type) := Std.HashMap Nat 𝕊

class HasSubst (𝕋 : Type) (𝕊 : outParam Type) extends HasVars 𝕋 where
  pSubst : 𝕋 → Subst 𝕊 → 𝕋

/-- **Substitution does nothing to a ground object.** True of every instance here and of any
sane one — substitution replaces metavariables, and a ground object has none — but `HasSubst`
states no laws at all, so nothing downstream may assume it.

A **mixin**, taking `[HasSubst 𝕋 𝕊]` as a parameter rather than `extends`-ing it. That is not
stylistic: a class extending `HasSubst` would carry its own copy, and a caller asking for both it
and something else built on `HasSubst` would get two unrelated `pSubst`s. Same diamond
`TypeSystem.LawfulMVars` exists to flatten; a `Prop`-valued mixin over the existing instance
cannot open it in the first place.

Wanted by anything that computes a substitution and then needs to know what it did *not* touch —
`TypeSystem/Vernacular/Elaborate.lean` is the first such caller, where a solved declaration must
be re-read under the context it was checked in rather than under the substituted one. -/
class GroundStable (𝕋 : Type) (𝕊 : outParam Type) [HasSubst 𝕋 𝕊] : Prop where
  /-- Substituting into a ground object leaves it alone. -/
  pSubst_ground : ∀ {x : 𝕋} (σ : Subst 𝕊), HasVars.Ground x → HasSubst.pSubst x σ = x

/-- Apply the singleton substitution `[n ↦ s]` to `t`. -/
def HasSubst.single [HasSubst 𝕋 𝕊] (t : 𝕋) (n : Nat) (s : 𝕊) : 𝕋 :=
  HasSubst.pSubst t (((∅ : Subst 𝕊).insert n s))

/-- `MoreGeneral σ σ'` says σ is at least as general as σ': there exists
some τ such that, on every term, applying σ' is the same as applying σ
then τ. Reflexive (witness τ = `∅`, modulo `pSubst t ∅ = t`); the name
covers both strictly-more-general and equally-general cases. -/
def MoreGeneral {α : Type} [HasSubst α α] (σ σ' : Subst α) : Prop :=
  ∃ τ : Subst α, ∀ t : α,
    HasSubst.pSubst t σ' = HasSubst.pSubst (HasSubst.pSubst t σ) τ

/-- Parallel composition of substitutions. `comp σ τ` is the substitution
whose intended action is "apply τ first, then σ" — i.e. function
composition `σ ∘ τ` on terms.

* For each `(n, t) ∈ τ`, the result binds `n ↦ pSubst t σ`.
* For each `(n, s) ∈ σ` with `n ∉ dom τ`, the result preserves `n ↦ s`.

Implemented as `σ.insertMany (mappedTau)` so that `insertMany`'s override
semantics gives τ's mapped entries priority over σ's bindings for shared
keys.

The correctness law
`HasSubst.pSubst t (Subst.comp σ τ) = HasSubst.pSubst (HasSubst.pSubst t τ) σ`
cannot be proved from the `HasSubst` axioms alone; it must be discharged
per instance (typically by structural induction on `t`). -/
def Subst.comp [HasSubst α α] (σ τ : Subst α) : Subst α :=
  σ.insertMany (τ.toList.map (fun p => (p.1, HasSubst.pSubst p.2 σ)))

/-- The `get?` characterization of `Subst.comp`: at every variable `n`,
the composed substitution either returns τ's binding with `σ` applied
(when `n ∈ dom τ`) or σ's binding (when `n ∉ dom τ`). -/
theorem Subst.comp_get? [HasSubst α α] (σ τ : Subst α) (n : Nat) :
    (Subst.comp σ τ).get? n =
      match τ.get? n with
      | some t => some (HasSubst.pSubst t σ)
      | none   => σ.get? n := by
  unfold Subst.comp
  have hdistinct_τ : τ.toList.Pairwise (fun a b => (a.1 == b.1) = false) :=
    Std.HashMap.distinct_keys_toList
  have hdistinct :
      (τ.toList.map (fun p => (p.1, HasSubst.pSubst p.2 σ))).Pairwise
        (fun a b => (a.1 == b.1) = false) :=
    hdistinct_τ.map _ (fun _ _ h => h)
  rw [Std.HashMap.get?_eq_getElem?]
  cases hτ : τ.get? n with
  | none =>
      simp only
      rw [← Std.HashMap.get?_eq_getElem?]
      apply Std.HashMap.getElem?_insertMany_list_of_contains_eq_false
      simp only [List.map_map, Function.comp_def, List.contains_eq_mem,
                 decide_eq_false_iff_not]
      intro hmem
      rcases List.mem_map.mp hmem with ⟨p, hp_mem, hp_eq⟩
      have hpτ : τ.get? p.1 = some p.2 := by
        rw [Std.HashMap.get?_eq_getElem?]
        exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp_mem
      rw [hp_eq] at hpτ
      rw [hpτ] at hτ
      cases hτ
  | some t =>
      simp only
      have hmem_τ : (n, t) ∈ τ.toList := by
        rw [Std.HashMap.mem_toList_iff_getElem?_eq_some,
            ← Std.HashMap.get?_eq_getElem?]
        exact hτ
      have hmem : (n, HasSubst.pSubst t σ) ∈
                    τ.toList.map (fun p => (p.1, HasSubst.pSubst p.2 σ)) :=
        List.mem_map.mpr ⟨(n, t), hmem_τ, rfl⟩
      exact Std.HashMap.getElem?_insertMany_list_of_mem
        BEq.rfl hdistinct hmem

/-- `getD` variant of `Subst.comp_get?`: convenient for working with
`pSubst` on substitution variables, which is defined via `getD`. -/
theorem Subst.comp_getD [HasSubst α α] (σ τ : Subst α) (n : Nat) (d : α) :
    (Subst.comp σ τ).getD n d =
      match τ.get? n with
      | some t => HasSubst.pSubst t σ
      | none   => σ.getD n d := by
  rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?,
      Subst.comp_get?]
  cases τ.get? n with
  | none =>
      simp only
      rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?]
  | some t => simp only [Option.getD]

/-! ## Restriction by domain threshold

`Subst.restrictBelow σ n` is σ with all bindings whose key is `≥ n`
dropped. Used by the elaborator to prune W's internal fresh-mvar
bindings (which sit at indices ≥ the source's fresh threshold) so the
substitution returned by `Term.elaborate` doesn't expose algorithm
scaffolding. -/

/-- Restrict σ to keys strictly below `n`. -/
def Subst.restrictBelow {α : Type} (σ : Subst α) (n : Nat) : Subst α :=
  σ.filter (fun k _ => decide (k < n))

/-- `get?` characterization: below the threshold σ is preserved; at or
above the threshold the result is `none`. -/
theorem Subst.restrictBelow_get? {α : Type} (σ : Subst α) (n k : Nat) :
    (Subst.restrictBelow σ n).get? k = if k < n then σ.get? k else none := by
  rw [Subst.restrictBelow, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter]
  -- `getElem?_filter` phrases the predicate at the *stored* key; `getKey_eq` (a `simp` lemma,
  -- available since `Nat` is `LawfulBEq`) identifies it with `k`, after which the filter is
  -- constantly true or constantly false.
  by_cases h : k < n <;>
    simp [h, Std.HashMap.get?_eq_getElem?, Option.filter] <;>
    cases σ[k]? <;> rfl

/-- For an arbitrary `f : α → Nat`, the foldr of `max` over a list bounds
`f a` from above whenever `a` is in the list. Used to prove
`fresh_gt_free` for substitution-shaped instances. -/
theorem List.foldr_max_of_mem (f : α → Nat) :
    ∀ (l : List α) (a : α), a ∈ l →
    f a ≤ l.foldr (fun x acc => max acc (f x)) 0 := by
  intro l
  induction l with
  | nil => intro a h; cases h
  | cons x xs ih =>
      intro a h
      simp only [List.foldr]
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.le_max_right _ _
      · exact Nat.le_trans (ih a h') (Nat.le_max_left _ _)

/-- **Substituting twice is substituting once, through the composite.** The other law `HasSubst`
does not state and that anything accumulating substitutions needs — without it a fold that solves
one constraint after another can never describe its answers by a single `Subst`.

A mixin for the same reason as `GroundStable`: extending `HasSubst` would mint a second `pSubst`.
The orientation matches `Signature.pSubst_comp`, which is where the instance for a signature's own
type comes from. -/
class LawfulComp (𝕋 : Type) (𝕊 : outParam Type) [HasSubst 𝕋 𝕊] [HasSubst 𝕊 𝕊] : Prop where
  /-- `comp σ τ` acts as τ first, then σ. -/
  pSubst_comp : ∀ (x : 𝕋) (σ τ : Subst 𝕊),
    HasSubst.pSubst x (Subst.comp σ τ) = HasSubst.pSubst (HasSubst.pSubst x τ) σ

/-! ## Generic instances -/

/-- Componentwise substitution on pairs. Free vars and `fresh` use the
union/max of both components. -/
instance {α α' β : Type} [HasSubst α β] [HasSubst α' β] :
    HasSubst (α × α') β where
  pSubst p s := (HasSubst.pSubst p.1 s, HasSubst.pSubst p.2 s)
  isFree p n := HasVars.isFree p.1 n ∨ HasVars.isFree p.2 n
  fresh p := max (HasVars.fresh p.1) (HasVars.fresh p.2)
  fresh_gt_free := by
    intro p n h
    rcases h with h₁ | h₂
    · exact Nat.lt_of_lt_of_le (HasVars.fresh_gt_free _ _ h₁) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (HasVars.fresh_gt_free _ _ h₂) (Nat.le_max_right _ _)

instance {α α' β : Type} [HasSubst α β] [HasSubst α' β] [HasSubst β β]
    [LawfulComp α β] [LawfulComp α' β] : LawfulComp (α × α') β where
  pSubst_comp p σ τ := by
    show (HasSubst.pSubst p.1 (Subst.comp σ τ), HasSubst.pSubst p.2 (Subst.comp σ τ))
        = (HasSubst.pSubst (HasSubst.pSubst p.1 τ) σ, HasSubst.pSubst (HasSubst.pSubst p.2 τ) σ)
    rw [LawfulComp.pSubst_comp p.1 σ τ, LawfulComp.pSubst_comp p.2 σ τ]

/-- A pair is ground exactly when both components are, so `GroundStable` lifts componentwise —
and eta makes the reassembled pair the original one. -/
instance {α α' β : Type} [HasSubst α β] [HasSubst α' β] [GroundStable α β] [GroundStable α' β] :
    GroundStable (α × α') β where
  pSubst_ground {p} σ h := by
    show (HasSubst.pSubst p.1 σ, HasSubst.pSubst p.2 σ) = p
    rw [GroundStable.pSubst_ground σ (fun n hn => h n (Or.inl hn)),
        GroundStable.pSubst_ground σ (fun n hn => h n (Or.inr hn))]

/-- Pointwise substitution on lists. `isFree` is "free in some element";
`fresh` is the foldr of `max` over the per-element fresh values. -/
instance {α β : Type} [HasSubst α β] : HasSubst (List α) β where
  pSubst xs s := xs.map (fun x => HasSubst.pSubst x s)
  isFree xs n := ∃ x ∈ xs, HasVars.isFree x n
  fresh xs := xs.foldr (fun x acc => max acc (HasVars.fresh x)) 0
  fresh_gt_free := by
    intro xs n h
    obtain ⟨x, hx, hf⟩ := h
    have key := List.foldr_max_of_mem (fun y : α => HasVars.fresh y) xs x hx
    exact Nat.lt_of_lt_of_le (HasVars.fresh_gt_free _ _ hf) key

instance {α β : Type} [HasSubst α β] [HasSubst β β] [LawfulComp α β] :
    LawfulComp (List α) β where
  pSubst_comp xs σ τ := by
    show xs.map _ = (xs.map _).map _
    rw [List.map_map]
    exact List.map_congr_left (fun x _ => LawfulComp.pSubst_comp x σ τ)

/-- A ground list is one all of whose elements are ground, so the pointwise map is the identity.

This is what makes an already-elaborated *program* a fixed point of elaboration: `Program` is a
`Command` paired with a `List Command`, and the two instances above and here are what carry
groundness of every declaration up to groundness of the file. -/
instance {α β : Type} [HasSubst α β] [GroundStable α β] : GroundStable (List α) β where
  pSubst_ground {xs} σ h := by
    show xs.map _ = xs
    rw [List.map_congr_left
      (fun x hx => GroundStable.pSubst_ground σ (fun n hn => h n ⟨x, hx, hn⟩))]
    exact List.map_id xs

/-- Substitution does not change a list's length — what lets a fold over a program recurse on the
substituted tail and still terminate. -/
@[simp] theorem List.length_pSubst {α β : Type} [HasSubst α β] (xs : List α) (σ : Subst β) :
    (HasSubst.pSubst xs σ).length = xs.length :=
  List.length_map _

/-! ## A `Nat` is its own variable

For a bare `Nat`, the only "free variable" is the number itself, and a
fresh `Nat` is just the successor. -/

instance : HasVars Nat where
  isFree n m := n = m
  fresh n := n + 1
  fresh_gt_free := by intro n m h; subst h; exact Nat.lt_succ_self _

/-! ## A `String` has no `Nat` free variables

Used as the key type in named contexts (`HashMap String Ty`): keys are
binder names, not metavariables, so they contribute no support. -/

instance : HasVars String where
  isFree _ _ := False
  fresh _ := 0
  fresh_gt_free := by intro _ _ h; cases h

/-! ## Substitution-into-`HashMap` instance

Generalises the substitution-into-substitution case: any `HashMap K V`
with variable-bearing keys and substitutable values is itself
substitutable. The key contribution to support uses `HasVars K`, so the
nominal-set support semantics still falls out for `Subst 𝕊 = HashMap Nat
𝕊` — keys appear in `isFree` because `HasVars Nat` makes a key its own
variable. -/

/-- Per-entry contribution of a `(key, value)` pair to the support of a
hashmap: above every free var in either component. -/
private def pairFresh {K V : Type} [HasVars K] [HasVars V] (p : K × V) : Nat :=
  max (HasVars.fresh p.1) (HasVars.fresh p.2)

instance {K V β : Type} [BEq K] [Hashable K] [HasVars K] [HasSubst V β] :
    HasSubst (Std.HashMap K V) β where
  pSubst m s := m.map (fun _ v => HasSubst.pSubst v s)
  isFree m n := ∃ p ∈ m.toList, HasVars.isFree p.1 n ∨ HasVars.isFree p.2 n
  fresh m := m.toList.foldr (fun p acc => max acc (pairFresh p)) 0
  fresh_gt_free := by
    intro m n h
    obtain ⟨p, hp, hor⟩ := h
    have key := List.foldr_max_of_mem pairFresh m.toList p hp
    rcases hor with hk | hv
    · have h₁ : n < HasVars.fresh p.1 := HasVars.fresh_gt_free _ _ hk
      have h₂ : HasVars.fresh p.1 ≤ pairFresh p := Nat.le_max_left _ _
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h₁ h₂) key
    · have h₁ : n < HasVars.fresh p.2 := HasVars.fresh_gt_free _ _ hv
      have h₂ : HasVars.fresh p.2 ≤ pairFresh p := Nat.le_max_right _ _
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h₁ h₂) key

/-- Every value stored in a hashmap has `fresh` bounded by the map's own — the map's `fresh` is a
`max`-fold over its entries. It lives here because `pairFresh` is private to this file. Used to
prune a substitution below a threshold without disturbing a context, the way
`Signature.pSubst_restrictBelow` does for a single term. -/
theorem HashMap.fresh_ge_get? {K V β : Type} [BEq K] [Hashable K] [LawfulBEq K]
    [HasVars K] [HasSubst V β] (m : Std.HashMap K V) (k : K) (v : V)
    (h : m.get? k = some v) : HasVars.fresh v ≤ HasVars.fresh m := by
  have hmem : (k, v) ∈ m.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact h
  exact Nat.le_trans (Nat.le_max_right _ _)
    (List.foldr_max_of_mem pairFresh m.toList (k, v) hmem)
