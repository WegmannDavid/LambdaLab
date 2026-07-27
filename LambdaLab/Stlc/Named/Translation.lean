import LambdaLab.Stlc.Named.Step.MStep
import LambdaLab.Stlc.Named.Typing.Basic
import LambdaLab.Stlc.DeBruijn.MStep
import LambdaLab.Stlc.DeBruijn.Substitution
import LambdaLab.Stlc.DeBruijn.Typing
import LambdaLab.Stlc.DeBruijn.Preservation

/-!
# Translation from named-variable to de Bruijn STLC

This file builds the machinery for translating named terms into their
de Bruijn equivalents and proving that named reductions correspond to
de Bruijn multi-step reductions on the translated terms.

The translation collapses α-equivalent named terms onto the same de
Bruijn term, which is exactly what we want when transferring properties
that are quotient-friendly (e.g. confluence, preservation up to α).

## Key technical lemmas

* `Term.toDB_relevant` — translation only depends on the lookup
  agreement at the term's free variables.
* `Term.toDB_rename` — α-renaming a binder commutes with translation
  when the new name is fresh in the term.
* `Term.toDB_insert` / `Term.toDB_insert_fresh` — inserting a
  (shadowed or fresh) binder in the middle of the context is a single
  de Bruijn `shift`.
* `Term.toDB_shift_context` — extending the context with binders fresh
  from `e.freeVars` is iterated `shift 0`.
* `Term.toDB_subst` — the named substitution `body.subst x v`
  translates to de Bruijn `subst` of the translated body. The α-renaming
  branch is handled via `Term.toDB_rename`.
* `Step.preserves_freeVars` / `MStep.preserves_freeVars` — needed to
  propagate the `freeVars ⊆ Γ` invariant through reductions.
* `Step.toDB_step` / `MStep.toDB_step` — every named (multi-)step
  lifts to a de Bruijn multi-step on the translated term.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Language1 (freshFor freshFor_not_in)

/-! ## Type translation -/

def Ty.toDB : Ty → Stlc.DeBruijn.Ty
  | .base => Stlc.DeBruijn.Ty.base
  | .arrow τ₁ τ₂ => Stlc.DeBruijn.Ty.arrow τ₁.toDB τ₂.toDB
  | .mvar _ => Stlc.DeBruijn.Ty.base

/-! ## Variable lookup in a context -/

/-- First index of `x` in `Γ`; if `x ∉ Γ`, returns `Γ.length`. -/
def lookupVar (x : String) : List String → Nat
  | [] => 0
  | y :: ys => if y = x then 0 else lookupVar x ys + 1

@[simp] theorem lookupVar_cons_eq (x : String) (Γ : List String) :
    lookupVar x (x :: Γ) = 0 := by simp [lookupVar]

theorem lookupVar_cons_ne {y x : String} (Γ : List String) (h : y ≠ x) :
    lookupVar x (y :: Γ) = lookupVar x Γ + 1 := by simp [lookupVar, h]

theorem lookupVar_append_left (x : String) (Γ₁ Γ₂ : List String) (h : x ∈ Γ₁) :
    lookupVar x (Γ₁ ++ Γ₂) = lookupVar x Γ₁ := by
  induction Γ₁ <;> grind [lookupVar]

theorem lookupVar_append_right (x : String) (Γ₁ Γ₂ : List String) (h : x ∉ Γ₁) :
    lookupVar x (Γ₁ ++ Γ₂) = Γ₁.length + lookupVar x Γ₂ := by
  induction Γ₁ <;> grind [lookupVar]

theorem lookupVar_lt_length (x : String) (Γ : List String) (h : x ∈ Γ) :
    lookupVar x Γ < Γ.length := by
  induction Γ <;> grind [lookupVar]

/-! ## Term translation -/

def Term.toDB (Γ : List String) : (Term String) → Stlc.DeBruijn.Term
  | .var x => Stlc.DeBruijn.Term.var (lookupVar x Γ)
  | .lam x τ body => Stlc.DeBruijn.Term.lam τ.toDB (body.toDB (x :: Γ))
  | .app e₁ e₂ => Stlc.DeBruijn.Term.app (e₁.toDB Γ) (e₂.toDB Γ)

/-! ## Translation only depends on the lookup of free variables -/

theorem Term.toDB_relevant : ∀ (e : (Term String)) {Γ Γ' : List String},
    (∀ x ∈ e.freeVars, lookupVar x Γ = lookupVar x Γ') →
    e.toDB Γ = e.toDB Γ' := by
  intro e
  induction e <;> intro Γ Γ' hag <;> grind [Term.toDB, Term.freeVars, lookupVar]

/-! ## Translation respects α-renaming -/

theorem Term.toDB_rename : ∀ (e : (Term String)) (Γ₁ Γ₂ : List String) (y z : String),
    z ∉ e.allVars → z ≠ y → y ∉ Γ₁ → z ∉ Γ₁ →
    e.toDB (Γ₁ ++ y :: Γ₂) = (e.rename y z).toDB (Γ₁ ++ z :: Γ₂) := by
  intro e
  induction e with
  | var w =>
      intro Γ₁ Γ₂ y z hz hzy hyΓ hzΓ
      simp only [Term.allVars, List.mem_singleton] at hz
      by_cases hwy : w = y
      · grind [Term.rename, Term.toDB, lookupVar_append_right, lookupVar_cons_eq]
      · by_cases hwΓ : w ∈ Γ₁
        · grind [Term.rename, Term.toDB, lookupVar_append_left]
        · grind [Term.rename, Term.toDB, lookupVar_append_right, lookupVar_cons_ne]
  | lam u σ inner ih =>
      intro Γ₁ Γ₂ y z hz hzy hyΓ hzΓ
      simp only [Term.allVars, List.mem_cons, not_or] at hz
      obtain ⟨hzu, hz_inner⟩ := hz
      by_cases huy : u = y
      · simp only [Term.rename, if_pos huy, Term.toDB]
        congr 1
        apply Term.toDB_relevant
        intro w hw
        have hwa : w ∈ inner.allVars := Term.freeVars_subset_allVars inner w hw
        by_cases hwu : u = w
        · grind [lookupVar_cons_eq]
        · by_cases hwΓ : w ∈ Γ₁
          · grind [lookupVar_cons_ne, lookupVar_append_left]
          · grind [lookupVar_cons_ne, lookupVar_append_right]
      · simp only [Term.rename, if_neg huy, Term.toDB]
        have := ih (u :: Γ₁) Γ₂ y z hz_inner hzy
          (by grind) (by grind)
        grind
  | app e₁ e₂ ih₁ ih₂ =>
      intro Γ₁ Γ₂ y z hz hzy hyΓ hzΓ
      have := ih₁ Γ₁ Γ₂ y z (by grind [Term.allVars]) hzy hyΓ hzΓ
      have := ih₂ Γ₁ Γ₂ y z (by grind [Term.allVars]) hzy hyΓ hzΓ
      grind [Term.rename, Term.toDB]

/-! ## Iterated shift -/

def iterShift0 : Nat → Stlc.DeBruijn.Term → Stlc.DeBruijn.Term
  | 0, e => e
  | n+1, e => (iterShift0 n e).shift 0

/-! ## Translation respects "redundantly inserting a binder"

If `w` is already bound somewhere in `Γ₁`, inserting another `w` between
`Γ₁` and `Γ₂` doesn't change which name maps where (the inner binder
shadows). On the de Bruijn side, this corresponds to a single `shift`
at position `Γ₁.length`.
-/

theorem Term.toDB_insert : ∀ (e : (Term String)) (Γ₁ Γ₂ : List String) (w : String),
    w ∈ Γ₁ →
    e.toDB (Γ₁ ++ w :: Γ₂) = (e.toDB (Γ₁ ++ Γ₂)).shift Γ₁.length := by
  intro e
  induction e with
  | var t =>
      intro Γ₁ Γ₂ w hw
      simp only [Term.toDB, Stlc.DeBruijn.Term.shift]
      by_cases htΓ : t ∈ Γ₁
      · rw [lookupVar_append_left _ _ _ htΓ, lookupVar_append_left _ _ _ htΓ]
        rw [if_pos (lookupVar_lt_length _ _ htΓ)]
      · rw [lookupVar_append_right _ _ _ htΓ, lookupVar_append_right _ _ _ htΓ]
        have hge : ¬ Γ₁.length + lookupVar t Γ₂ < Γ₁.length := by omega
        rw [if_neg hge]
        have hwt : w ≠ t := by intro h; subst h; exact htΓ hw
        rw [lookupVar_cons_ne _ hwt]; congr 1
  | lam u σ inner ih =>
      intro Γ₁ Γ₂ w hw
      have := ih (u :: Γ₁) Γ₂ w (List.mem_cons.mpr (Or.inr hw))
      grind [Term.toDB, Stlc.DeBruijn.Term.shift]
  | app e₁ e₂ ih₁ ih₂ =>
      intro Γ₁ Γ₂ w hw
      have := ih₁ Γ₁ Γ₂ w hw
      have := ih₂ Γ₁ Γ₂ w hw
      grind [Term.toDB, Stlc.DeBruijn.Term.shift]

/-! ## Translation respects inserting a fresh binder

If `w` is fresh in `e` (not free), then inserting it anywhere in the
context is a single de Bruijn shift at the corresponding position.
-/

theorem Term.toDB_insert_fresh : ∀ (e : (Term String)) (Γ₁ Γ₂ : List String) (w : String),
    w ∉ e.freeVars →
    e.toDB (Γ₁ ++ w :: Γ₂) = (e.toDB (Γ₁ ++ Γ₂)).shift Γ₁.length := by
  intro e
  induction e with
  | var t =>
      intro Γ₁ Γ₂ w hw
      simp only [Term.freeVars, List.mem_singleton] at hw
      simp only [Term.toDB, Stlc.DeBruijn.Term.shift]
      by_cases htΓ : t ∈ Γ₁
      · rw [lookupVar_append_left _ _ _ htΓ, lookupVar_append_left _ _ _ htΓ]
        rw [if_pos (lookupVar_lt_length _ _ htΓ)]
      · rw [lookupVar_append_right _ _ _ htΓ, lookupVar_append_right _ _ _ htΓ]
        have hge : ¬ Γ₁.length + lookupVar t Γ₂ < Γ₁.length := by omega
        rw [if_neg hge, lookupVar_cons_ne _ hw]; congr 1
  | lam u σ inner ih =>
      intro Γ₁ Γ₂ w hw
      simp only [Term.toDB, Stlc.DeBruijn.Term.shift]
      congr 1
      by_cases hwu : w = u
      · exact Term.toDB_insert inner (u :: Γ₁) Γ₂ w (List.mem_cons.mpr (Or.inl hwu))
      · exact ih (u :: Γ₁) Γ₂ w (by grind [Term.freeVars])
  | app e₁ e₂ ih₁ ih₂ =>
      intro Γ₁ Γ₂ w hw
      have := ih₁ Γ₁ Γ₂ w (by grind [Term.freeVars])
      have := ih₂ Γ₁ Γ₂ w (by grind [Term.freeVars])
      grind [Term.toDB, Stlc.DeBruijn.Term.shift]

/-! ## Translation respects extending the context with fresh binders -/

theorem Term.toDB_shift_context : ∀ (Γ₁ Γ₂ : List String) (e : (Term String)),
    (∀ y ∈ Γ₁, y ∉ e.freeVars) →
    e.toDB (Γ₁ ++ Γ₂) = iterShift0 Γ₁.length (e.toDB Γ₂) := by
  intro Γ₁
  induction Γ₁ with
  | nil => intros; simp [iterShift0]
  | cons w ws ih =>
      intro Γ₂ e hag
      have h_insert := Term.toDB_insert_fresh e [] (ws ++ Γ₂) w
        (hag w List.mem_cons_self)
      simp at h_insert
      show e.toDB (w :: (ws ++ Γ₂)) = iterShift0 (ws.length + 1) (e.toDB Γ₂)
      rw [h_insert, ih Γ₂ e (by grind)]
      simp [iterShift0]

/-! ## Translation respects substitution

The key lemma. With `Γ₁` accumulating the binders we've descended past
(none initially, with each lam adding one), the named substitution
`(e.subst x v)` translated under `Γ₁ ++ Γ₂` matches the de Bruijn
substitution of the translated body at index `Γ₁.length` with the
appropriately shifted `v.toDB Γ₂`.

We use `Nat`-induction on a `body.size` upper bound because the named
`subst`'s α-renaming branch recurses on `inner.rename u z`, which is
not structurally smaller than the input lam.
-/

private theorem Term.toDB_subst_aux : ∀ (n : Nat) (e : (Term String)), e.size ≤ n →
    ∀ (Γ₁ Γ₂ : List String) (x : String) (v : (Term String)),
    v.freeVars ⊆ Γ₂ →
    x ∉ Γ₁ →
    (∀ y ∈ Γ₁, y ∉ v.freeVars) →
    (e.subst x v).toDB (Γ₁ ++ Γ₂) =
      (e.toDB (Γ₁ ++ x :: Γ₂)).subst Γ₁.length
        (iterShift0 Γ₁.length (v.toDB Γ₂)) := by
  intro n
  induction n with
  | zero => intro e hsize; cases e <;> grind [Term.size]
  | succ n ih =>
      intro e hsize Γ₁ Γ₂ x v hvfv hxΓ hvΓ
      cases e with
      | var w =>
          by_cases hxw : x = w
          · subst hxw
            simp only [Term.subst, Term.toDB]
            rw [lookupVar_append_right _ _ _ hxΓ, lookupVar_cons_eq, Nat.add_zero]
            simp only [Stlc.DeBruijn.Term.subst]
            exact Term.toDB_shift_context Γ₁ Γ₂ v hvΓ
          · simp only [Term.subst, if_neg hxw, Term.toDB, Stlc.DeBruijn.Term.subst]
            by_cases hwΓ : w ∈ Γ₁
            · rw [lookupVar_append_left _ _ _ hwΓ, lookupVar_append_left _ _ _ hwΓ]
              have hlt : lookupVar w Γ₁ < Γ₁.length := lookupVar_lt_length _ _ hwΓ
              have hne : lookupVar w Γ₁ ≠ Γ₁.length := by omega
              rw [if_neg hne]
              have hngt : ¬ lookupVar w Γ₁ > Γ₁.length := by omega
              rw [if_neg hngt]
            · rw [lookupVar_append_right _ _ _ hwΓ, lookupVar_append_right _ _ _ hwΓ,
                  lookupVar_cons_ne _ hxw]
              have hne : Γ₁.length + (lookupVar w Γ₂ + 1) ≠ Γ₁.length := by omega
              rw [if_neg hne]
              have hgt : Γ₁.length + (lookupVar w Γ₂ + 1) > Γ₁.length := by omega
              rw [if_pos hgt]
              congr 1
      | lam u σ inner =>
          have hsize_inner : inner.size ≤ n := by
            simp [Term.size] at hsize; omega
          by_cases hxu : x = u
          · -- Sub-case (a): x = u, subst returns body unchanged
            rw [show (Term.lam u σ inner).subst x v = .lam u σ inner by
                  simp only [Term.subst]; rw [if_pos hxu]]
            simp only [Term.toDB, Stlc.DeBruijn.Term.subst]
            congr 1
            have hF := Term.toDB_insert inner (u :: Γ₁) Γ₂ x
              (List.mem_cons.mpr (Or.inl hxu))
            simp only [List.cons_append, List.length_cons] at hF
            rw [hF, Stlc.DeBruijn.Term.shift_subst_cancel]
          · by_cases huv : u ∈ v.freeVars
            · -- Sub-case (b): rename branch
              let z := freshFor (v.freeVars ++ inner.allVars ++ [x])
              rw [show (Term.lam u σ inner).subst x v =
                      .lam z σ ((inner.rename u z).subst x v) by
                   simp only [Term.subst]; rw [if_neg hxu, if_pos huv]]
              have hz_not_in : z ∉ v.freeVars ++ inner.allVars ++ [x] :=
                freshFor_not_in _
              have hz_v : z ∉ v.freeVars := by grind
              have hz_inner : z ∉ inner.allVars := by grind
              have hz_neq_u : z ≠ u := fun h => hz_v (h ▸ huv)
              have hsize_ren : (inner.rename u z).size ≤ n := by
                rw [Term.rename_size]; exact hsize_inner
              have ih_call := ih (inner.rename u z) hsize_ren (z :: Γ₁) Γ₂ x v
                hvfv (by grind) (by grind)
              simp only [List.cons_append] at ih_call
              simp only [Term.toDB, Stlc.DeBruijn.Term.subst]
              congr 1
              have hren_lemma := Term.toDB_rename inner [] (Γ₁ ++ x :: Γ₂) u z
                hz_inner hz_neq_u List.not_mem_nil List.not_mem_nil
              simp only [List.nil_append] at hren_lemma
              rw [ih_call, ← hren_lemma]
              simp [iterShift0]
            · -- Sub-case (c): no rename
              rw [show (Term.lam u σ inner).subst x v = .lam u σ (inner.subst x v) by
                    simp only [Term.subst]; rw [if_neg hxu, if_neg huv]]
              simp only [Term.toDB, Stlc.DeBruijn.Term.subst]
              congr 1
              have ih_call := ih inner hsize_inner (u :: Γ₁) Γ₂ x v hvfv
                (by grind) (by grind)
              simp only [List.cons_append] at ih_call
              rw [ih_call]
              simp [iterShift0]
      | app e₁ e₂ =>
          have h1 := ih e₁ (by grind [Term.size]) Γ₁ Γ₂ x v hvfv hxΓ hvΓ
          have h2 := ih e₂ (by grind [Term.size]) Γ₁ Γ₂ x v hvfv hxΓ hvΓ
          grind [Term.subst, Term.toDB, Stlc.DeBruijn.Term.subst]

theorem Term.toDB_subst (e : (Term String)) (Γ₁ Γ₂ : List String) (x : String) (v : (Term String))
    (hvfv : v.freeVars ⊆ Γ₂)
    (hxΓ : x ∉ Γ₁)
    (hvΓ : ∀ y ∈ Γ₁, y ∉ v.freeVars) :
    (e.subst x v).toDB (Γ₁ ++ Γ₂) =
      (e.toDB (Γ₁ ++ x :: Γ₂)).subst Γ₁.length
        (iterShift0 Γ₁.length (v.toDB Γ₂)) :=
  Term.toDB_subst_aux e.size e (Nat.le_refl _) Γ₁ Γ₂ x v hvfv hxΓ hvΓ

/-! ## Free variables under rename and subst -/

theorem Term.freeVars_rename_subset : ∀ (e : (Term String)) (y z : String) (w : String),
    w ∈ (e.rename y z).freeVars → (w ∈ e.freeVars ∧ w ≠ y) ∨ w = z := by
  intro e
  induction e <;> intro y z w hw <;> grind [Term.rename, Term.freeVars]

private theorem Term.freeVars_subst_subset_aux : ∀ (n : Nat) (e : (Term String)), e.size ≤ n →
    ∀ (x : String) (v : (Term String)) (w : String),
    w ∈ (e.subst x v).freeVars → (w ∈ e.freeVars ∧ w ≠ x) ∨ w ∈ v.freeVars := by
  intro n
  induction n with
  | zero => intro e hsize; cases e <;> grind [Term.size]
  | succ n ih =>
      intro e hsize x v w hw
      cases e with
      | var y => grind [Term.subst, Term.freeVars]
      | lam u σ inner =>
          have hsize_inner : inner.size ≤ n := by grind [Term.size]
          by_cases hxu : x = u
          · -- subst returns body unchanged
            rw [show (Term.lam u σ inner).subst x v = .lam u σ inner by
                  simp only [Term.subst]; rw [if_pos hxu]] at hw
            grind [Term.freeVars]
          · by_cases huv : u ∈ v.freeVars
            · -- rename branch
              let z := freshFor (v.freeVars ++ inner.allVars ++ [x])
              rw [show (Term.lam u σ inner).subst x v =
                      .lam z σ ((inner.rename u z).subst x v) by
                   simp only [Term.subst]; rw [if_neg hxu, if_pos huv]] at hw
              simp only [Term.freeVars, List.mem_filter, decide_eq_true_eq] at hw
              obtain ⟨hw_sub, hw_neq_z⟩ := hw
              have hsize_ren : (inner.rename u z).size ≤ n := by
                rw [Term.rename_size]; exact hsize_inner
              have ih_call := ih (inner.rename u z) hsize_ren x v w hw_sub
              have hren_facts := fun w hin =>
                Term.freeVars_rename_subset inner u z w hin
              grind [Term.freeVars]
            · -- no rename
              rw [show (Term.lam u σ inner).subst x v = .lam u σ (inner.subst x v) by
                    simp only [Term.subst]; rw [if_neg hxu, if_neg huv]] at hw
              simp only [Term.freeVars, List.mem_filter, decide_eq_true_eq] at hw
              obtain ⟨hw_sub, hw_neq_u⟩ := hw
              have := ih inner hsize_inner x v w hw_sub
              grind [Term.freeVars]
      | app e₁ e₂ =>
          simp only [Term.subst, Term.freeVars, List.mem_append] at hw
          cases hw with
          | inl h =>
              have := ih e₁ (by grind [Term.size]) x v w h
              grind [Term.freeVars]
          | inr h =>
              have := ih e₂ (by grind [Term.size]) x v w h
              grind [Term.freeVars]

theorem Term.freeVars_subst_subset (e : (Term String)) (x : String) (v : (Term String)) (w : String) :
    w ∈ (e.subst x v).freeVars → (w ∈ e.freeVars ∧ w ≠ x) ∨ w ∈ v.freeVars :=
  Term.freeVars_subst_subset_aux e.size e (Nat.le_refl _) x v w

/-! ## Reduction preserves the "free variables ⊆ Γ" invariant -/

theorem Step.preserves_freeVars : ∀ {e e' : (Term String)},
    e ⟶ e' → ∀ w ∈ e'.freeVars, w ∈ e.freeVars := by
  intro e e' hstep
  induction hstep with
  | @beta x τ body v =>
      intro w hw
      have := Term.freeVars_subst_subset body x v w hw
      grind [Term.freeVars]
  | lam _ ih => intro w hw; grind [Term.freeVars]
  | appL _ ih => intro w hw; grind [Term.freeVars]
  | appR _ ih => intro w hw; grind [Term.freeVars]

theorem MStep.preserves_freeVars : ∀ {e e' : (Term String)},
    e ⟶* e' → ∀ w ∈ e'.freeVars, w ∈ e.freeVars := by
  intro e e' hms
  induction hms with
  | refl => intro w hw; exact hw
  | head s _ ih => intro w hw; exact Step.preserves_freeVars s w (ih w hw)

/-! ## Step simulation -/

theorem Step.toDB_step : ∀ {e e' : (Term String)} (Γ : List String),
    (∀ w ∈ e.freeVars, w ∈ Γ) →
    e ⟶ e' →
    Stlc.DeBruijn.MStep (e.toDB Γ) (e'.toDB Γ) := by
  intro e e' Γ hfv hstep
  induction hstep generalizing Γ with
  | @beta x τ body v =>
      have hvfv : ∀ w ∈ v.freeVars, w ∈ Γ := by
        intro w hw; apply hfv
        simp only [Term.freeVars, List.mem_append]
        exact Or.inr hw
      have hbody_aux : (body.subst x v).toDB Γ =
                       (body.toDB (x :: Γ)).subst 0 (v.toDB Γ) := by
        have h := Term.toDB_subst body [] Γ x v hvfv List.not_mem_nil
          (fun y hy => absurd hy List.not_mem_nil)
        simp [iterShift0] at h
        exact h
      simp only [Term.toDB]
      rw [hbody_aux]
      exact Stlc.DeBruijn.MStep.lift Stlc.DeBruijn.Step.beta
  | @lam e₀ e₀' xn τn _ ih =>
      simp only [Term.toDB]
      exact Stlc.DeBruijn.MStep.lam (ih (xn :: Γ) (by grind [Term.freeVars]))
  | appL _ ih =>
      simp only [Term.toDB]
      exact Stlc.DeBruijn.MStep.appL (ih Γ (by grind [Term.freeVars]))
  | appR _ ih =>
      simp only [Term.toDB]
      exact Stlc.DeBruijn.MStep.appR (ih Γ (by grind [Term.freeVars]))

/-! ## Strengthened simulation: a named step lifts to a *head* DB step

Every named single-step contains at least one DB single-step (β translates
to β, and the congruence rules recurse to that base case). This is the
key fact that makes named SN follow from DB SN: an infinite named
reduction sequence would translate to an infinite DB reduction. -/

theorem Step.toDB_pos : ∀ {e e' : (Term String)} (Γ : List String),
    (∀ w ∈ e.freeVars, w ∈ Γ) →
    e ⟶ e' →
    ∃ d_mid, Stlc.DeBruijn.Step (e.toDB Γ) d_mid ∧
             Stlc.DeBruijn.MStep d_mid (e'.toDB Γ) := by
  intro e e' Γ hfv hstep
  induction hstep generalizing Γ with
  | @beta x τ body v =>
      have hvfv : ∀ w ∈ v.freeVars, w ∈ Γ := by
        intro w hw; apply hfv
        simp only [Term.freeVars, List.mem_append]
        exact Or.inr hw
      have hbody_aux : (body.subst x v).toDB Γ =
                       (body.toDB (x :: Γ)).subst 0 (v.toDB Γ) := by
        have h := Term.toDB_subst body [] Γ x v hvfv List.not_mem_nil
          (fun y hy => absurd hy List.not_mem_nil)
        simp [iterShift0] at h
        exact h
      simp only [Term.toDB]
      refine ⟨(body.toDB (x :: Γ)).subst 0 (v.toDB Γ),
              Stlc.DeBruijn.Step.beta, ?_⟩
      rw [hbody_aux]
      exact Stlc.DeBruijn.MStep.refl
  | @lam e₀ e₀' xn τn _ ih =>
      simp only [Term.toDB]
      obtain ⟨d_mid, h_step, h_rest⟩ := ih (xn :: Γ) (by grind [Term.freeVars])
      exact ⟨_, Stlc.DeBruijn.Step.lam h_step, Stlc.DeBruijn.MStep.lam h_rest⟩
  | appL _ ih =>
      simp only [Term.toDB]
      obtain ⟨d_mid, h_step, h_rest⟩ := ih Γ (by grind [Term.freeVars])
      exact ⟨_, Stlc.DeBruijn.Step.appL h_step, Stlc.DeBruijn.MStep.appL h_rest⟩
  | appR _ ih =>
      simp only [Term.toDB]
      obtain ⟨d_mid, h_step, h_rest⟩ := ih Γ (by grind [Term.freeVars])
      exact ⟨_, Stlc.DeBruijn.Step.appR h_step, Stlc.DeBruijn.MStep.appR h_rest⟩

/-! ## Multi-step simulation -/

theorem MStep.toDB_step : ∀ {e e' : (Term String)} (Γ : List String),
    (∀ w ∈ e.freeVars, w ∈ Γ) →
    e ⟶* e' →
    Stlc.DeBruijn.MStep (e.toDB Γ) (e'.toDB Γ) := by
  intro e e' Γ hfv hms
  induction hms with
  | refl => exact Stlc.DeBruijn.MStep.refl
  | head s _ ih =>
      exact (Step.toDB_step Γ hfv s).trans
            (ih (fun w hw => hfv w (Step.preserves_freeVars s w hw)))

/-! ## Type translation back: `DB.Ty → Ty` -/

def Ty.fromDB : Stlc.DeBruijn.Ty → Ty
  | .base => .base
  | .arrow t₁ t₂ => .arrow (Ty.fromDB t₁) (Ty.fromDB t₂)

theorem Ty.fromDB_toDB : ∀ {τ : Ty}, τ.Ground → Ty.fromDB τ.toDB = τ := by
  intro τ h
  induction τ with
  | base => rfl
  | arrow τ₁ τ₂ ih₁ ih₂ =>
      obtain ⟨h₁, h₂⟩ := Ty.Ground.arrow.mp h
      simp [Ty.toDB, Ty.fromDB, ih₁ h₁, ih₂ h₂]
  | mvar n   => exact absurd h (Ty.Ground.mvar n)

@[simp] theorem Ty.toDB_fromDB (t : Stlc.DeBruijn.Ty) : (Ty.fromDB t).toDB = t := by
  induction t with
  | base => rfl
  | arrow t₁ t₂ ih₁ ih₂ => simp [Ty.toDB, Ty.fromDB, ih₁, ih₂]

theorem Ty.toDB_inj : ∀ {τ τ' : Ty}, τ.Ground → τ'.Ground →
    τ.toDB = τ'.toDB → τ = τ' := by
  intro τ τ' hg hg' h
  rw [← Ty.fromDB_toDB hg, ← Ty.fromDB_toDB hg', h]

/-! ## Lookup is functional -/

theorem Stlc.DeBruijn.Lookup.functional :
    ∀ {Γ : Stlc.DeBruijn.Ctx} {n : Nat} {τ τ' : Stlc.DeBruijn.Ty},
    Stlc.DeBruijn.Lookup Γ n τ → Stlc.DeBruijn.Lookup Γ n τ' → τ = τ' := by
  intro Γ n τ τ' h h'
  induction h with
  | here => cases h'; rfl
  | there _ ih => cases h' with | there h'' => exact ih h''

/-! ## Compatibility relation between named and DB contexts -/

/-- A named context (function-based) and a de Bruijn context (list-based)
agree along the given binder list: for every binder `x`, the named lookup
yields some `τ` whose translation matches the de Bruijn lookup at the
corresponding index. -/
def CtxCompat (Γ : Ctx) (binders : List String) (db_ctx : Stlc.DeBruijn.Ctx) : Prop :=
  ∀ x ∈ binders, ∃ τ : Ty, Γ.get? x = some τ ∧ τ.Ground ∧
    Stlc.DeBruijn.Lookup db_ctx (lookupVar x binders) τ.toDB

theorem CtxCompat.cons {Γ : Ctx} {binders : List String} {db_ctx : Stlc.DeBruijn.Ctx}
    (x : String) (τ₁ : Ty) (h₁ : τ₁.Ground) (hcompat : CtxCompat Γ binders db_ctx) :
    CtxCompat (Γ.cons x τ₁) (x :: binders) (τ₁.toDB :: db_ctx) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    refine ⟨τ₁, ?_, h₁, ?_⟩
    · simp [Ctx.cons]
    · have hlk : lookupVar y (y :: binders) = 0 := by simp [lookupVar]
      rw [hlk]; exact .here
  · rcases List.mem_cons.mp hy with hyEq | hy'
    · exact absurd hyEq hyx
    · obtain ⟨τ_y, heq, hg, hl⟩ := hcompat y hy'
      have hxy : ¬ x = y := fun h => hyx h.symm
      refine ⟨τ_y, ?_, hg, ?_⟩
      · rw [Ctx.get?_cons, if_neg hxy]; exact heq
      · have hlk : lookupVar y (x :: binders) = lookupVar y binders + 1 := by
          simp [lookupVar, hxy]
        rw [hlk]; exact .there hl

/-- Build a compatible DB context from a named context, given that all
binder names are bound in `Γ`. -/
def Ctx.toDB (Γ : Ctx) : List String → Stlc.DeBruijn.Ctx
  | [] => []
  | x :: xs =>
    (match Γ.get? x with | some τ => τ.toDB | none => Stlc.DeBruijn.Ty.base) ::
    Ctx.toDB Γ xs

theorem CtxCompat.fromCtx (Γ : Ctx) (binders : List String)
    (hbound : ∀ x ∈ binders, ∃ τ, Γ.get? x = some τ ∧ τ.Ground) :
    CtxCompat Γ binders (Ctx.toDB Γ binders) := by
  intro x hx
  induction binders with
  | nil => exact absurd hx List.not_mem_nil
  | cons y ys ih =>
      by_cases hyx : y = x
      · subst hyx
        obtain ⟨τ_y, heq, hg⟩ := hbound y List.mem_cons_self
        refine ⟨τ_y, heq, hg, ?_⟩
        simp only [Ctx.toDB, heq, lookupVar]
        exact .here
      · rcases List.mem_cons.mp hx with hxEq | hx'
        · exact absurd hxEq.symm hyx
        · have hbound' : ∀ z ∈ ys, ∃ τ, Γ.get? z = some τ ∧ τ.Ground :=
            fun z hz => hbound z (List.mem_cons.mpr (Or.inr hz))
          obtain ⟨τ_x, heq, hg, hl⟩ := ih hbound' hx'
          refine ⟨τ_x, heq, hg, ?_⟩
          have hcons : Ctx.toDB Γ (y :: ys) =
            (match Γ.get? y with | some τ => τ.toDB | none => Stlc.DeBruijn.Ty.base) ::
            Ctx.toDB Γ ys := rfl
          rw [hcons]
          have hlk : lookupVar x (y :: ys) = lookupVar x ys + 1 := by
            simp [lookupVar, hyx]
          rw [hlk]
          exact .there hl

/-! ## Forward typing translation -/

theorem HasType.toDB : ∀ (e : (Term String)) {Γ : Ctx} {τ : Ty},
    Γ.Ground → e.AnnotsGround → HasType Γ e τ →
    ∀ (binders : List String) (db_ctx : Stlc.DeBruijn.Ctx),
    (∀ x ∈ e.freeVars, x ∈ binders) →
    CtxCompat Γ binders db_ctx →
    Stlc.DeBruijn.HasType db_ctx (e.toDB binders) τ.toDB := by
  intro e
  induction e with
  | var x =>
      intro Γ τ _ _ ht binders db_ctx hfv hcompat
      cases ht with
      | var heq =>
          apply Stlc.DeBruijn.HasType.var
          have hxb : x ∈ binders := hfv x (by simp [Term.freeVars])
          obtain ⟨τ', heq', _, hl⟩ := hcompat x hxb
          have : τ = τ' := by rw [heq] at heq'; injection heq'
          subst this
          exact hl
  | lam x τ₁ body ih =>
      intro Γ τ hΓ hag ht binders db_ctx hfv hcompat
      cases ht with
      | lam hb =>
          obtain ⟨h₁g, hbg⟩ := hag
          simp only [Term.toDB, Ty.toDB]
          apply Stlc.DeBruijn.HasType.lam
          apply ih (Ctx.Ground.cons hΓ h₁g) hbg hb
            (x :: binders) (τ₁.toDB :: db_ctx)
          · intro y hy
            by_cases hyx : y = x
            · subst hyx; exact List.mem_cons_self
            · apply List.mem_cons.mpr (Or.inr ?_)
              apply hfv
              simp [Term.freeVars, List.mem_filter]
              exact ⟨hy, hyx⟩
          · exact CtxCompat.cons x τ₁ h₁g hcompat
  | app e₁ e₂ ih₁ ih₂ =>
      intro Γ τ hΓ hag ht binders db_ctx hfv hcompat
      cases ht with
      | app hf ha =>
          obtain ⟨h₁ag, h₂ag⟩ := hag
          have h_arrow_g : (_ ⇒ τ).Ground :=
            HasType.ground_result hΓ h₁ag hf
          obtain ⟨hτ₁g, _⟩ := Ty.Ground.arrow.mp h_arrow_g
          simp only [Term.toDB]
          apply Stlc.DeBruijn.HasType.app
          · apply ih₁ hΓ h₁ag hf binders db_ctx ?_ hcompat
            intro y hy; apply hfv; simp [Term.freeVars]; exact Or.inl hy
          · apply ih₂ hΓ h₂ag ha binders db_ctx ?_ hcompat
            intro y hy; apply hfv; simp [Term.freeVars]; exact Or.inr hy

/-! ## Backward typing translation

Phrased in terms of an arbitrary de Bruijn type `t`; the named result
type is `Ty.fromDB t`. -/

theorem HasType.fromDB : ∀ (e : (Term String)) {Γ : Ctx} (binders : List String)
    (db_ctx : Stlc.DeBruijn.Ctx) (t : Stlc.DeBruijn.Ty),
    e.AnnotsGround →
    (∀ x ∈ e.freeVars, x ∈ binders) →
    CtxCompat Γ binders db_ctx →
    Stlc.DeBruijn.HasType db_ctx (e.toDB binders) t →
    HasType Γ e (Ty.fromDB t) := by
  intro e
  induction e with
  | var x =>
      intro Γ binders db_ctx t _ hfv hcompat hdb
      simp only [Term.toDB] at hdb
      cases hdb with
      | var hl =>
          apply HasType.var
          have hxb : x ∈ binders := hfv x (by simp [Term.freeVars])
          obtain ⟨τ', heq, hg, hl'⟩ := hcompat x hxb
          have h_eq : t = τ'.toDB := Stlc.DeBruijn.Lookup.functional hl hl'
          subst h_eq
          rw [Ty.fromDB_toDB hg]
          exact heq
  | lam x τ₁ body ih =>
      intro Γ binders db_ctx t hag hfv hcompat hdb
      obtain ⟨h₁g, hbg⟩ := hag
      simp only [Term.toDB] at hdb
      cases hdb with
      | lam hb =>
          rename_i τ_out
          simp only [Ty.fromDB, Ty.fromDB_toDB h₁g]
          apply HasType.lam
          apply ih (x :: binders) (τ₁.toDB :: db_ctx) τ_out hbg _ _ hb
          · intro y hy
            by_cases hyx : y = x
            · subst hyx; exact List.mem_cons_self
            · apply List.mem_cons.mpr (Or.inr ?_)
              apply hfv
              simp [Term.freeVars, List.mem_filter]
              exact ⟨hy, hyx⟩
          · exact CtxCompat.cons x τ₁ h₁g hcompat
  | app e₁ e₂ ih₁ ih₂ =>
      intro Γ binders db_ctx t hag hfv hcompat hdb
      obtain ⟨h₁ag, h₂ag⟩ := hag
      simp only [Term.toDB] at hdb
      cases hdb with
      | app hf ha =>
          rename_i τ_in
          have h₁ := ih₁ binders db_ctx (.arrow τ_in t) h₁ag
            (fun y hy => hfv y (by simp [Term.freeVars]; exact Or.inl hy))
            hcompat hf
          have h₂ := ih₂ binders db_ctx τ_in h₂ag
            (fun y hy => hfv y (by simp [Term.freeVars]; exact Or.inr hy))
            hcompat ha
          simp only [Ty.fromDB] at h₁
          exact HasType.app h₁ h₂

/-! ## Multi-step DB preservation (lifted from single-step) -/

theorem Stlc.DeBruijn.MStep.preservation :
    ∀ {Γ : Stlc.DeBruijn.Ctx} {e e' : Stlc.DeBruijn.Term} {τ : Stlc.DeBruijn.Ty},
    Stlc.DeBruijn.HasType Γ e τ → Stlc.DeBruijn.MStep e e' →
    Stlc.DeBruijn.HasType Γ e' τ := by
  intro Γ e e' τ ht hms
  induction hms with
  | refl => exact ht
  | head s _ ih => exact ih (Stlc.DeBruijn.HasType.preservation ht s)

end LambdaLab.Stlc.Named
