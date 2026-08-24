import Std.Data.HashMap
import LambdaLab.Nominal.Atom

/-!
# Substitution over an arbitrary atom supply

The atom-generic port of `Substitution/Basic.lean`. Same operations, same laws; the variable type
is `[Atom A]` rather than `Nat`, and the support structure is a **list of atoms** rather than a
bound in `Nat`'s order.

## What changed, and why

`HasVars` carried two fields: `isFree : 𝕋 → Nat → Prop` and `fresh : 𝕋 → Nat`, tied together by
`fresh_gt_free`. `fresh` is an upper bound *in an order*, which atoms do not have. It becomes
`supp : 𝕋 → List A`, and `isFree` is then not a field at all — it is membership in `supp`. That
collapses two fields and a law into one field:

* `fresh_gt_free` disappears — it said "everything free is below the bound", and membership is
  that statement;
* `Ground x` is `supp x = []`, decidable, instead of a quantified negation;
* `Subst.restrictBelow σ n` (keys below a threshold) becomes `Subst.restrictTo σ s` (keys in a
  finite set).

Nothing here mentions `Perm`. This file is Mathlib-free and stays that way: the whole point is
that the executables can keep it, and `Nominal/Substitution.lean` — which does take Mathlib — is
the specification it will be checked against, not a dependency.

## `A` is an `outParam`

`supp`'s result type mentions `A`, but at a use site the expected type rarely pins it down, so
instance search must determine it from the carrier. Same fragility, and the same argument, as in
`Nominal/Substitution.lean`: fine while each carrier substitutes atoms of one type, and the thing
to revisit first if that stops holding.
-/

open LambdaLab.Nominal

/-- A type whose values mention finitely many atoms of `A`.

Two fields and a law, the same shape the old class had — but where `fresh_gt_free` said only
that `fresh` *bounds* the free variables, leaving an instance free to over-approximate,
`mem_supp_iff_isFree` is an equivalence. Every instance in the old file was in fact exact, so
nothing is lost, and the measure in `Measure.lean` needs exactness: it counts `supp`. -/
class HasVars (A : outParam Type) (𝕋 : Type) where
  /-- `a` occurs in `x`. -/
  isFree : 𝕋 → A → Prop
  /-- The atoms occurring in `x`, with multiplicity. -/
  supp : 𝕋 → List A
  /-- `supp` lists exactly the atoms that occur. Replaces `fresh_gt_free`. -/
  mem_supp_iff_isFree : ∀ (x : 𝕋) (a : A), a ∈ supp x ↔ isFree x a

/-- **Ground**: no atom occurs.

Kept as a quantified negation rather than `supp x = []`, even though `supp` now makes the latter
expressible and decidable. The two are equivalent (`ground_iff_supp_nil`), and consumers reason
with `Ground` one atom at a time. -/
def HasVars.Ground {A 𝕋 : Type} [HasVars A 𝕋] (x : 𝕋) : Prop :=
  ∀ a : A, ¬ HasVars.isFree x a

theorem HasVars.ground_iff_supp_nil {A 𝕋 : Type} [HasVars A 𝕋] {x : 𝕋} :
    HasVars.Ground (A := A) x ↔ HasVars.supp (A := A) x = [] := by
  simp only [HasVars.Ground]
  constructor
  · intro h
    cases hs : HasVars.supp (A := A) x with
    | nil => rfl
    | cons a _ =>
        exact absurd ((HasVars.mem_supp_iff_isFree x a).mp (hs ▸ List.mem_cons_self)) (h a)
  · intro h a hfree
    have := (HasVars.mem_supp_iff_isFree x a).mpr hfree
    rw [h] at this
    exact List.not_mem_nil this

/-- A substitution: a finite map from atoms to values. `Atom` supplies exactly what the
representation needs — `Hashable` from the class itself, `BEq` from `decEq`. -/
abbrev Subst (A 𝕊 : Type) [Atom A] := Std.HashMap A 𝕊

/-- Applying a substitution. -/
class HasSubst (A : outParam Type) (𝕋 : Type) (𝕊 : outParam Type) [Atom A]
    extends HasVars A 𝕋 where
  pSubst : 𝕋 → Subst A 𝕊 → 𝕋

/-- **Substitution does nothing to a ground object.** A mixin over `[HasSubst]`, not an
`extends`: a class extending `HasSubst` would mint a second `pSubst`. -/
class GroundStable (A : outParam Type) (𝕋 : Type) (𝕊 : outParam Type) [Atom A]
    [HasSubst A 𝕋 𝕊] : Prop where
  pSubst_ground : ∀ {x : 𝕋} (σ : Subst A 𝕊),
    HasVars.Ground (A := A) x → HasSubst.pSubst x σ = x

/-- Apply the singleton substitution `[a ↦ s]` to `x`. -/
def HasSubst.single {A 𝕋 𝕊 : Type} [Atom A] [HasSubst A 𝕋 𝕊] (x : 𝕋) (a : A) (s : 𝕊) : 𝕋 :=
  HasSubst.pSubst x ((∅ : Subst A 𝕊).insert a s)

/-- `MoreGeneral σ σ'`: some τ factors σ' through σ, on every object. -/
def MoreGeneral {A α : Type} [Atom A] [HasSubst A α α] (σ σ' : Subst A α) : Prop :=
  ∃ τ : Subst A α, ∀ t : α,
    HasSubst.pSubst t σ' = HasSubst.pSubst (HasSubst.pSubst t σ) τ

/-- `MoreGeneralOn s σ σ'` is `MoreGeneral` restricted to objects whose atoms all lie in `s` —
the order-free `MoreGeneralBelow`.

The restriction is what principality looks like when the general answer has atoms of its own: an
elaborator draws atoms the source never mentioned and may mention them in its answer, a competing
σ' says nothing about those, and no τ can factor σ' through σ *at those atoms*. Below the source's
own atoms the question does not arise. -/
def MoreGeneralOn {A α : Type} [Atom A] [HasSubst A α α] (s : List A) (σ σ' : Subst A α) : Prop :=
  ∃ τ : Subst A α, ∀ t : α, (∀ a, HasVars.isFree (A := A) t a → a ∈ s) →
    HasSubst.pSubst t σ' = HasSubst.pSubst (HasSubst.pSubst t σ) τ

/-- Generality everywhere is generality on any atom set. -/
theorem MoreGeneral.on {A α : Type} [Atom A] [HasSubst A α α] {σ σ' : Subst A α}
    (h : MoreGeneral σ σ') (s : List A) : MoreGeneralOn s σ σ' :=
  ⟨h.choose, fun t _ => h.choose_spec t⟩

/-- Parallel composition: `comp σ τ` acts as τ first, then σ. -/
def Subst.comp {A α : Type} [Atom A] [HasSubst A α α] (σ τ : Subst A α) : Subst A α :=
  σ.insertMany (τ.toList.map (fun p => (p.1, HasSubst.pSubst p.2 σ)))

/-- The `get?` characterisation of `Subst.comp`. -/
theorem Subst.comp_get? {A α : Type} [Atom A] [HasSubst A α α] (σ τ : Subst A α) (a : A) :
    (Subst.comp σ τ).get? a =
      match τ.get? a with
      | some t => some (HasSubst.pSubst t σ)
      | none   => σ.get? a := by
  unfold Subst.comp
  have hdistinct_τ : τ.toList.Pairwise (fun x y => (x.1 == y.1) = false) :=
    Std.HashMap.distinct_keys_toList
  have hdistinct :
      (τ.toList.map (fun p => (p.1, HasSubst.pSubst p.2 σ))).Pairwise
        (fun x y => (x.1 == y.1) = false) :=
    hdistinct_τ.map _ (fun _ _ h => h)
  rw [Std.HashMap.get?_eq_getElem?]
  cases hτ : τ.get? a with
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
      have hmem_τ : (a, t) ∈ τ.toList := by
        rw [Std.HashMap.mem_toList_iff_getElem?_eq_some,
            ← Std.HashMap.get?_eq_getElem?]
        exact hτ
      have hmem : (a, HasSubst.pSubst t σ) ∈
                    τ.toList.map (fun p => (p.1, HasSubst.pSubst p.2 σ)) :=
        List.mem_map.mpr ⟨(a, t), hmem_τ, rfl⟩
      exact Std.HashMap.getElem?_insertMany_list_of_mem BEq.rfl hdistinct hmem

/-- `getD` variant of `Subst.comp_get?`: convenient for working with
`pSubst` on substitution variables, which is defined via `getD`. -/
theorem Subst.comp_getD {A α : Type} [Atom A] [HasSubst A α α]
    (σ τ : Subst A α) (a : A) (d : α) :
    (Subst.comp σ τ).getD a d =
      match τ.get? a with
      | some t => HasSubst.pSubst t σ
      | none   => σ.getD a d := by
  rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?,
      Subst.comp_get?]
  cases τ.get? a with
  | none =>
      simp only
      rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?]
  | some t => simp only [Option.getD]

/-- Restrict σ to the keys in `s`. The order-free `restrictBelow`. -/
def Subst.restrictTo {A α : Type} [Atom A] (σ : Subst A α) (s : List A) : Subst A α :=
  σ.filter (fun k _ => s.contains k)

/-- `get?` characterisation: inside `s` σ is preserved, outside it the result is `none`. -/
theorem Subst.restrictTo_get? {A α : Type} [Atom A] (σ : Subst A α) (s : List A) (k : A) :
    (Subst.restrictTo σ s).get? k = if k ∈ s then σ.get? k else none := by
  rw [Subst.restrictTo, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter]
  by_cases h : k ∈ s <;>
    simp [h, Std.HashMap.get?_eq_getElem?, Option.filter] <;>
    cases σ[k]? <;> rfl

/-- **Substituting twice is substituting once, through the composite.** -/
class LawfulComp (A : outParam Type) (𝕋 : Type) (𝕊 : outParam Type) [Atom A]
    [HasSubst A 𝕋 𝕊] [HasSubst A 𝕊 𝕊] : Prop where
  pSubst_comp : ∀ (x : 𝕋) (σ τ : Subst A 𝕊),
    HasSubst.pSubst x (Subst.comp σ τ) = HasSubst.pSubst (HasSubst.pSubst x τ) σ

/-- **Bindings on atoms an object does not mention are invisible to it.**

Stated as an equality of *actions*, never as `σ = Subst.restrictTo σ s`: `Std.HashMap` has no
`getElem?` extensionality in this toolchain, so two substitutions that agree everywhere still
cannot be proved equal. -/
class LawfulRestrict (A : outParam Type) (𝕋 : Type) (𝕊 : outParam Type) [Atom A]
    [HasSubst A 𝕋 𝕊] : Prop where
  pSubst_restrictTo : ∀ (x : 𝕋) (σ : Subst A 𝕊) (s : List A),
    (∀ a, HasVars.isFree x a → a ∈ s) →
    HasSubst.pSubst x (Subst.restrictTo σ s) = HasSubst.pSubst x σ

/-! ## Generic instances

Support is a concatenation where the old file took a `max`; that is the whole of the change. -/

instance {A α α' β : Type} [Atom A] [HasSubst A α β] [HasSubst A α' β] :
    HasSubst A (α × α') β where
  isFree p a := HasVars.isFree p.1 a ∨ HasVars.isFree p.2 a
  supp p := HasVars.supp (A := A) p.1 ++ HasVars.supp (A := A) p.2
  mem_supp_iff_isFree p a := by
    rw [List.mem_append, HasVars.mem_supp_iff_isFree, HasVars.mem_supp_iff_isFree]
  pSubst p σ := (HasSubst.pSubst p.1 σ, HasSubst.pSubst p.2 σ)

instance {A α β : Type} [Atom A] [HasSubst A α β] : HasSubst A (List α) β where
  isFree xs a := ∃ x ∈ xs, HasVars.isFree x a
  supp xs := xs.flatMap (fun x => HasVars.supp (A := A) x)
  mem_supp_iff_isFree xs a := by
    rw [List.mem_flatMap]
    exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, (HasVars.mem_supp_iff_isFree x a).mp h⟩,
      fun ⟨x, hx, h⟩ => ⟨x, hx, (HasVars.mem_supp_iff_isFree x a).mpr h⟩⟩
  pSubst xs σ := xs.map (fun x => HasSubst.pSubst x σ)

instance {A α α' β : Type} [Atom A] [HasSubst A α β] [HasSubst A α' β] [HasSubst A β β]
    [LawfulComp A α β] [LawfulComp A α' β] : LawfulComp A (α × α') β where
  pSubst_comp p σ τ := by
    show (HasSubst.pSubst p.1 (Subst.comp σ τ), HasSubst.pSubst p.2 (Subst.comp σ τ))
        = (HasSubst.pSubst (HasSubst.pSubst p.1 τ) σ, HasSubst.pSubst (HasSubst.pSubst p.2 τ) σ)
    rw [LawfulComp.pSubst_comp p.1 σ τ, LawfulComp.pSubst_comp p.2 σ τ]

/-- A pair is ground exactly when both components are, so `GroundStable` lifts componentwise —
and eta makes the reassembled pair the original one. -/
instance {A α α' β : Type} [Atom A] [HasSubst A α β] [HasSubst A α' β]
    [GroundStable A α β] [GroundStable A α' β] : GroundStable A (α × α') β where
  pSubst_ground {p} σ h := by
    show (HasSubst.pSubst p.1 σ, HasSubst.pSubst p.2 σ) = p
    rw [GroundStable.pSubst_ground σ (fun n hn => h n (Or.inl hn)),
        GroundStable.pSubst_ground σ (fun n hn => h n (Or.inr hn))]

/-- A pair's atoms are the two components' together, so an atom set the pair sits inside is one
both components sit inside. -/
instance {A α α' β : Type} [Atom A] [HasSubst A α β] [HasSubst A α' β]
    [LawfulRestrict A α β] [LawfulRestrict A α' β] : LawfulRestrict A (α × α') β where
  pSubst_restrictTo p σ s h := by
    show (HasSubst.pSubst p.1 _, HasSubst.pSubst p.2 _)
        = (HasSubst.pSubst p.1 σ, HasSubst.pSubst p.2 σ)
    rw [LawfulRestrict.pSubst_restrictTo p.1 σ s (fun a ha => h a (Or.inl ha)),
        LawfulRestrict.pSubst_restrictTo p.2 σ s (fun a ha => h a (Or.inr ha))]

instance {A α β : Type} [Atom A] [HasSubst A α β] [HasSubst A β β] [LawfulComp A α β] :
    LawfulComp A (List α) β where
  pSubst_comp xs σ τ := by
    show xs.map _ = (xs.map _).map _
    rw [List.map_map]
    exact List.map_congr_left (fun x _ => LawfulComp.pSubst_comp x σ τ)

/-- A ground list is one all of whose elements are ground, so the pointwise map is the identity.

This is what makes an already-elaborated *program* a fixed point of elaboration: `Program` is a
`Command` paired with a `List Command`, and the two instances above and here are what carry
groundness of every declaration up to groundness of the file. -/
instance {A α β : Type} [Atom A] [HasSubst A α β] [GroundStable A α β] :
    GroundStable A (List α) β where
  pSubst_ground {xs} σ h := by
    show xs.map _ = xs
    rw [List.map_congr_left
      (fun x hx => GroundStable.pSubst_ground σ (fun n hn => h n ⟨x, hx, hn⟩))]
    exact List.map_id xs

/-- A list's atoms include every element's, so pruning invisible to the list is pruning invisible
to each element, and the pointwise maps agree. -/
instance {A α β : Type} [Atom A] [HasSubst A α β] [LawfulRestrict A α β] :
    LawfulRestrict A (List α) β where
  pSubst_restrictTo xs σ s h := by
    show xs.map _ = xs.map _
    refine List.map_congr_left (fun x hx => ?_)
    exact LawfulRestrict.pSubst_restrictTo x σ s (fun a ha => h a ⟨x, hx, ha⟩)

@[simp] theorem List.length_pSubst {A α β : Type} [Atom A] [HasSubst A α β]
    (xs : List α) (σ : Subst A β) :
    (HasSubst.pSubst xs σ : List α).length = xs.length := by
  show (xs.map (fun x => HasSubst.pSubst x σ)).length = xs.length
  exact List.length_map _

/-! ## An atom is its own variable

The old file had this at `Nat` only ("for a bare `Nat`, the only free variable is the number
itself"). Over an atom supply it is generic, and it is what gives `Subst A 𝕊 = HashMap A 𝕊` its
key-aware support: the keys of a substitution *are* the atoms it binds. -/

instance instHasVarsAtom {A : Type} [Atom A] : HasVars A A where
  isFree a b := a = b
  supp a := [a]
  mem_supp_iff_isFree a b := by simp [eq_comm]

/-- The instance for a carrier that mentions no atoms of `A` at all — the generic form of the old
`HasVars String` ("keys are binder names, not metavariables, so they contribute no support").

Deliberately **not** an instance: as a blanket one it would overlap `instHasVarsAtom` at `K = A`,
and the two disagree (`a = b` versus `False`). Object languages opt in per name type. -/
@[reducible] def HasVars.ofNoAtoms (A K : Type) : HasVars A K where
  isFree _ _ := False
  supp _ := []
  mem_supp_iff_isFree _ _ := by simp

/-! ## Substitution into a hashmap

Generalises substitution-into-substitution: any `HashMap K V` with atom-bearing keys and
substitutable values is itself substitutable. Support is a concatenation where the old instance
took a `max` over a private `pairFresh`; with no order there is nothing to fold. -/

instance instHasSubstHashMap {A K V β : Type} [Atom A] [BEq K] [Hashable K] [HasVars A K]
    [HasSubst A V β] : HasSubst A (Std.HashMap K V) β where
  isFree m a := ∃ p ∈ m.toList, HasVars.isFree p.1 a ∨ HasVars.isFree p.2 a
  supp m := m.toList.flatMap
    (fun p => HasVars.supp (A := A) p.1 ++ HasVars.supp (A := A) p.2)
  mem_supp_iff_isFree m a := by
    simp only [List.mem_flatMap, List.mem_append, HasVars.mem_supp_iff_isFree]
  pSubst m s := m.map (fun _ v => HasSubst.pSubst v s)

/-- Every atom of a stored value is an atom of the map. The order-free `HashMap.fresh_ge_get?`:
where that bounded `fresh v` by `fresh m`, this says `supp v ⊆ supp m` one atom at a time. -/
theorem HashMap.isFree_of_get? {A K V β : Type} [Atom A] [BEq K] [Hashable K] [LawfulBEq K]
    [HasVars A K] [HasSubst A V β] (m : Std.HashMap K V) (k : K) (v : V)
    (h : m.get? k = some v) (a : A) (ha : HasVars.isFree v a) :
    HasVars.isFree (A := A) m a := by
  refine ⟨(k, v), ?_, Or.inr ha⟩
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
  exact h

