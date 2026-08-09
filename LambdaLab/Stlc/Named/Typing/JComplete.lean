import LambdaLab.Stlc.Named.Typing.Target

/-!
# Completeness of constraint generation

`Target.GenerationComplete`, proved. Its docstring there calls it "the one missing lemma"; this
file supplies it, along with the bookkeeping it turns out to need.

## Shape of the argument

The statement in `Target.lean` is a *checking* one — it fixes the declared type `τ` and asks the
constraints to be satisfiable. That form does not induct. In the `lam` case, inverting the typing
of `pSubst (lam x α body) σ'` gives `pSubst τ σ' = pSubst α σ' ⇒ ρb` for some `ρb`, and there is no
source-level type mapping to `ρb`: `τ` may be a bare metavariable that `σ'` happens to send to an
arrow, so it cannot be split.

`complete_aux` below is the *synthesising* form: for **any** type `ρ` at which the substituted
term is typeable, the constraints have a solution which moreover sends the generated type `τg` to
`ρ`. That inducts cleanly, and the checking form falls out by instantiating `ρ := pSubst τ σ'` and
using agreement to put `τ` back under the new substitution.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.TypeSystem (NameAlphabet)

variable {N : Type} [NameAlphabet N] [HasVars N]

/-! ## Freshness of `Ty`, computed

`Signature.fresh` is defined by well-founded recursion through `construct`/`deconstruct`, so it
does not reduce on `Ty`'s constructors. These two put it back in closed form. -/

theorem Ty.fresh_arrow (a b : Ty) :
    HasVars.fresh (a ⇒ b) = max (HasVars.fresh a) (HasVars.fresh b) := by
  have h : Ty.arrow a b = Signature.construct (Sum.inr ⟨TyConstructor.arrow,
      Vector.ofFn (fun i : Fin 2 => match i with | 0 => a | 1 => b)⟩) := rfl
  show Signature.fresh (Ty.arrow a b) = _
  rw [h, Signature.fresh_construct]
  have e0 : (Vector.ofFn (fun i : Fin 2 => match i with | 0 => a | 1 => b)).get 0 = a := rfl
  have e1 : (Vector.ofFn (fun i : Fin 2 => match i with | 0 => a | 1 => b)).get 1 = b := rfl
  have hb : ∀ t : Ty, HasVars.fresh t = Signature.fresh t := fun _ => rfl
  simp [List.finRange, e0, e1, hb]
  omega

theorem Ty.fresh_mvar (k : Nat) : HasVars.fresh (Ty.mvar k) = k + 1 := Signature.fresh_var k

/-! ## Context freshness, pointwise

`HasVars.fresh Γ` is a fold over `Γ.toList`, and `Ctx.cons` is `insert`, which may *replace* an
entry — so bounding `fresh (Γ.cons x α)` means reasoning about `toList` of an insert. The
pointwise form avoids that entirely and is all the argument ever uses. -/

/-- Every type in `Γ` has its metavariables below `n`. -/
def CtxFreshBelow (n : Nat) (Γ : Ctx N) : Prop :=
  ∀ (x : N) (τ : Ty), Γ.get? x = some τ → HasVars.fresh τ ≤ n

theorem CtxFreshBelow.of_fresh {n : Nat} {Γ : Ctx N} (h : HasVars.fresh Γ ≤ n) :
    CtxFreshBelow n Γ :=
  fun x τ hx => Nat.le_trans (HashMap.fresh_ge_get? Γ x τ hx) h

omit [HasVars N] in
theorem CtxFreshBelow.mono {m n : Nat} {Γ : Ctx N} (hmn : m ≤ n) (h : CtxFreshBelow m Γ) :
    CtxFreshBelow n Γ :=
  fun x τ hx => Nat.le_trans (h x τ hx) hmn

omit [HasVars N] in
theorem CtxFreshBelow.cons {n : Nat} {Γ : Ctx N} {x : N} {α : Ty}
    (h : CtxFreshBelow n Γ) (hα : HasVars.fresh α ≤ n) : CtxFreshBelow n (Γ.cons x α) := by
  intro y τ hy
  rw [Ctx.get?_cons] at hy
  by_cases hxy : x = y
  · simp only [hxy, if_pos] at hy
    cases hy
    exact hα
  · rw [if_neg hxy] at hy
    exact h y τ hy

/-! ## Agreement below a threshold

The whole argument is about substitutions that differ only on variables the generator drew.
`AgreeBelow n σ σ'` says they are indistinguishable on anything whose metavariables sit below `n`
— which is exactly the source material: the context, the term, and the declared type. -/

/-- σ and σ' act alike on every type whose metavariables are below `n`. -/
def AgreeBelow (n : Nat) (σ σ' : Subst Ty) : Prop :=
  ∀ u : Ty, HasVars.fresh u ≤ n → HasSubst.pSubst u σ = HasSubst.pSubst u σ'

theorem AgreeBelow.refl (n : Nat) (σ : Subst Ty) : AgreeBelow n σ σ := fun _ _ => rfl

theorem AgreeBelow.trans {n : Nat} {σ₁ σ₂ σ₃ : Subst Ty}
    (h₁ : AgreeBelow n σ₁ σ₂) (h₂ : AgreeBelow n σ₂ σ₃) : AgreeBelow n σ₁ σ₃ :=
  fun u hu => (h₁ u hu).trans (h₂ u hu)

/-- Agreement on a wider range implies agreement on a narrower one. -/
theorem AgreeBelow.mono {m n : Nat} {σ σ' : Subst Ty} (hmn : m ≤ n)
    (h : AgreeBelow n σ σ') : AgreeBelow m σ σ' :=
  fun u hu => h u (Nat.le_trans hu hmn)

/-- A variable at or above the threshold is not free in anything below it. -/
theorem not_isFree_of_fresh_le {u : Ty} {n k : Nat} (hu : HasVars.fresh u ≤ n) (hk : n ≤ k) :
    ¬ HasVars.isFree u k := fun hfree =>
  Nat.lt_irrefl k (Nat.lt_of_lt_of_le (HasVars.fresh_gt_free u k hfree) (Nat.le_trans hu hk))

/-- **Extending at a fresh index changes nothing below it.** This is what lets the `app` case bind
the drawn result variable without disturbing anything already solved. -/
theorem AgreeBelow.insert {n m : Nat} (σ : Subst Ty) (ρ : Ty) (hnm : n ≤ m) :
    AgreeBelow n (σ.insert m ρ) σ :=
  fun u hu => Signature.pSubst_insert_fresh σ m ρ u (not_isFree_of_fresh_le hu hnm)

/-! ### Transport to contexts and terms

Agreement is stated on types because that is where the induction needs it; the typing judgement it
feeds is stated on contexts and terms. These two lift it. -/

theorem AgreeBelow.ctx {n : Nat} {σ σ' : Subst Ty} (h : AgreeBelow n σ σ')
    {Γ : Ctx N} (hΓ : CtxFreshBelow n Γ) (x : N) :
    (HasSubst.pSubst Γ σ).get? x = (HasSubst.pSubst Γ σ').get? x := by
  rw [HashMap.pSubst_get?, HashMap.pSubst_get?]
  cases hx : Γ.get? x with
  | none => rfl
  | some τ => exact congrArg _ (h τ (hΓ x τ hx))

theorem AgreeBelow.term {n : Nat} {σ σ' : Subst Ty} (h : AgreeBelow n σ σ')
    (e : Term N) (he : HasVars.fresh e ≤ n) :
    HasSubst.pSubst e σ = HasSubst.pSubst e σ' := by
  show Term.tyPSubst e σ = Term.tyPSubst e σ'
  induction e with
  | var x => rfl
  | lam x α body ih =>
      have hα : HasVars.fresh α ≤ n := Nat.le_trans (Nat.le_max_left _ _) he
      have hb : HasVars.fresh body ≤ n := Nat.le_trans (Nat.le_max_right _ _) he
      simp only [Term.tyPSubst, h α hα, ih hb]
  | app e₁ e₂ ih₁ ih₂ =>
      have h₁ : HasVars.fresh e₁ ≤ n := Nat.le_trans (Nat.le_max_left _ _) he
      have h₂ : HasVars.fresh e₂ ≤ n := Nat.le_trans (Nat.le_max_right _ _) he
      simp only [Term.tyPSubst, ih₁ h₁, ih₂ h₂]

/-- Agreement transports a whole typing derivation. -/
theorem AgreeBelow.hasType {n : Nat} {σ σ' : Subst Ty} (h : AgreeBelow n σ σ')
    {Γ : Ctx N} {e : Term N} {ρ : Ty} (hΓ : CtxFreshBelow n Γ) (he : HasVars.fresh e ≤ n)
    (hty : HasType (HasSubst.pSubst Γ σ') (HasSubst.pSubst e σ') ρ) :
    HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst e σ) ρ := by
  rw [h.term e he]
  exact HasType.cong (fun y => (h.ctx hΓ y).symm) hty

/-! ## The generated type and constraints stay below the ending supply

Needed in the `app` case, where a solution found for the *second* subderivation must still satisfy
the *first* one's constraints: it does, because those mention nothing at or above `n₁`, and the two
substitutions agree there. -/

/-- Every metavariable in an equation set is below `n`. -/
def EqsFreshBelow (n : Nat) (C : Equations Ty) : Prop :=
  ∀ p ∈ C, HasVars.fresh p.1 ≤ n ∧ HasVars.fresh p.2 ≤ n

theorem EqsFreshBelow.mono {m n : Nat} {C : Equations Ty} (hmn : m ≤ n) (h : EqsFreshBelow m C) :
    EqsFreshBelow n C :=
  fun p hp => ⟨Nat.le_trans (h p hp).1 hmn, Nat.le_trans (h p hp).2 hmn⟩

theorem HasTypeJ.fresh_bound {n : Nat} {Γ : Ctx N} {e : Term N} {τ : Ty} {C : Equations Ty}
    {n' : Nat} (h : HasTypeJ n Γ e τ C n') :
    CtxFreshBelow n Γ → HasVars.fresh e ≤ n →
    HasVars.fresh τ ≤ n' ∧ EqsFreshBelow n' C := by
  induction h with
  | @var n Γ x τ hget =>
      intro hΓ _
      exact ⟨hΓ x τ hget, fun p hp => absurd hp (List.not_mem_nil)⟩
  | @lam n Γ x α body τb C n' hj ih =>
      intro hΓ he
      have hα : HasVars.fresh α ≤ n := Nat.le_trans (Nat.le_max_left _ _) he
      have hb : HasVars.fresh body ≤ n := Nat.le_trans (Nat.le_max_right _ _) he
      obtain ⟨hτb, hC⟩ := ih (hΓ.cons hα) hb
      refine ⟨?_, hC⟩
      rw [Ty.fresh_arrow]
      exact Nat.max_le.mpr ⟨Nat.le_trans hα hj.supply_le, hτb⟩
  | @app n Γ e₁ e₂ τ₁ τ₂ C₁ C₂ n₁ n₂ hj₁ hj₂ ih₁ ih₂ =>
      intro hΓ he
      have h₁ : HasVars.fresh e₁ ≤ n := Nat.le_trans (Nat.le_max_left _ _) he
      have h₂ : HasVars.fresh e₂ ≤ n := Nat.le_trans (Nat.le_max_right _ _) he
      obtain ⟨hτ₁, hC₁⟩ := ih₁ hΓ h₁
      obtain ⟨hτ₂, hC₂⟩ := ih₂ (hΓ.mono hj₁.supply_le) (Nat.le_trans h₂ hj₁.supply_le)
      have hn₁₂ : n₁ ≤ n₂ := hj₂.supply_le
      refine ⟨by rw [Ty.fresh_mvar]; exact Nat.le_refl _, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hrest
      · refine ⟨Nat.le_trans hτ₁ (Nat.le_trans hn₁₂ (Nat.le_succ _)), ?_⟩
        rw [Ty.fresh_arrow, Ty.fresh_mvar]
        exact Nat.max_le.mpr ⟨Nat.le_trans hτ₂ (Nat.le_succ _), Nat.le_refl _⟩
      · rcases List.mem_append.mp hrest with hin | hin
        · exact (hC₁.mono (Nat.le_trans hn₁₂ (Nat.le_succ _))) p hin
        · exact (hC₂.mono (Nat.le_succ _)) p hin

/-! ## Completeness, in synthesising form

The induction. See the module header for why the checking form in `Target.lean` cannot be the
induction hypothesis. -/

/-- **Every typing of the substituted term solves the constraints.** The converse of
`HasTypeJ.sound`: given any `ρ` at which `pSubst e σ'` is typeable, the generated constraints have
a solution `σ''` sending the generated type to `ρ`, and agreeing with `σ'` on everything the
generator did not draw. -/
theorem HasTypeJ.complete_aux {n : Nat} {Γ : Ctx N} {e : Term N} {τg : Ty} {C : Equations Ty}
    {n' : Nat} (h : HasTypeJ n Γ e τg C n') :
    ∀ (σ' : Subst Ty) (ρ : Ty), CtxFreshBelow n Γ → HasVars.fresh e ≤ n →
      HasType (HasSubst.pSubst Γ σ') (HasSubst.pSubst e σ') ρ →
      ∃ σ'', Subst.Unifies σ'' C ∧ HasSubst.pSubst τg σ'' = ρ ∧ AgreeBelow n σ'' σ' := by
  induction h with
  | @var n Γ x τ hget =>
      intro σ' ρ _ _ hty
      refine ⟨σ', fun p hp => absurd hp List.not_mem_nil, ?_, AgreeBelow.refl n σ'⟩
      -- the only rule that types a variable is `var`, and it reads the substituted context
      cases hty with
      | var hlook =>
          rw [HashMap.pSubst_get?, hget] at hlook
          exact (Option.some.inj hlook)
  | @lam n Γ x α body τb C n' hj ih =>
      intro σ' ρ hΓ he hty
      have hα : HasVars.fresh α ≤ n := Nat.le_trans (Nat.le_max_left _ _) he
      have hb : HasVars.fresh body ≤ n := Nat.le_trans (Nat.le_max_right _ _) he
      cases hty with
      | lam hbody =>
          rename_i ρb
          -- move the body's typing across `pSubst (Γ.cons x α) σ' ≅ (pSubst Γ σ').cons x α[σ']`
          have hbody' : HasType (HasSubst.pSubst (Γ.cons x α) σ')
              (HasSubst.pSubst body σ') ρb :=
            HasType.cong (fun y => (Ctx.pSubst_cons_get? Γ σ' x α y).symm) hbody
          obtain ⟨σ'', hC, hτb, hag⟩ := ih σ' ρb (hΓ.cons hα) hb hbody'
          refine ⟨σ'', hC, ?_, hag⟩
          rw [Ty.pSubst_arrow, hτb, hag α hα]
  | @app n Γ e₁ e₂ τ₁ τ₂ C₁ C₂ n₁ n₂ hj₁ hj₂ ih₁ ih₂ =>
      intro σ' ρ hΓ he hty
      have h₁ : HasVars.fresh e₁ ≤ n := Nat.le_trans (Nat.le_max_left _ _) he
      have h₂ : HasVars.fresh e₂ ≤ n := Nat.le_trans (Nat.le_max_right _ _) he
      have hnn₁ : n ≤ n₁ := hj₁.supply_le
      have hn₁₂ : n₁ ≤ n₂ := hj₂.supply_le
      obtain ⟨hτ₁b, hC₁b⟩ := hj₁.fresh_bound hΓ h₁
      obtain ⟨hτ₂b, hC₂b⟩ := hj₂.fresh_bound (hΓ.mono hnn₁) (Nat.le_trans h₂ hnn₁)
      cases hty with
      | app hfun harg =>
          rename_i ρ₂
          -- first subderivation, at the incoming σ'
          obtain ⟨σ₁, hC₁, hτ₁, hag₁⟩ := ih₁ σ' (ρ₂ ⇒ ρ) hΓ h₁ hfun
          -- second, at σ₁: it agrees with σ' below n, and Γ and e₂ live entirely below n
          obtain ⟨σ₂, hC₂, hτ₂, hag₂⟩ :=
            ih₂ σ₁ ρ₂ (hΓ.mono hnn₁) (Nat.le_trans h₂ hnn₁)
              (hag₁.hasType hΓ h₂ harg)
          -- bind the drawn result variable to the observed result type
          refine ⟨σ₂.insert n₂ ρ, ?_, ?_, ?_⟩
          · intro p hp
            rcases List.mem_cons.mp hp with rfl | hrest
            · -- head: τ₁ ≐ τ₂ → βₙ₂
              have e₁' : HasSubst.pSubst τ₁ (σ₂.insert n₂ ρ) = HasSubst.pSubst τ₁ σ₁ := by
                rw [AgreeBelow.insert σ₂ ρ (Nat.le_trans hτ₁b hn₁₂) τ₁ (Nat.le_refl _)]
                exact hag₂ τ₁ hτ₁b
              have e₂' : HasSubst.pSubst τ₂ (σ₂.insert n₂ ρ) = HasSubst.pSubst τ₂ σ₂ :=
                AgreeBelow.insert σ₂ ρ (Nat.le_refl _) τ₂ hτ₂b
              have ehd : HasSubst.pSubst (Ty.mvar n₂) (σ₂.insert n₂ ρ) = ρ := by
                rw [Ty.pSubst_mvar, Std.HashMap.getD_insert]
                simp
              show HasSubst.pSubst τ₁ _ = HasSubst.pSubst (τ₂ ⇒ Ty.mvar n₂) _
              rw [e₁', hτ₁, Ty.pSubst_arrow, e₂', hτ₂, ehd]
            · rcases List.mem_append.mp hrest with hin | hin
              · have hp₁ := (hC₁b p hin).1
                have hp₂ := (hC₁b p hin).2
                rw [AgreeBelow.insert σ₂ ρ (Nat.le_trans hp₁ hn₁₂) p.1 (Nat.le_refl _),
                    AgreeBelow.insert σ₂ ρ (Nat.le_trans hp₂ hn₁₂) p.2 (Nat.le_refl _),
                    hag₂ p.1 hp₁, hag₂ p.2 hp₂]
                exact hC₁ p hin
              · have hp₁ := (hC₂b p hin).1
                have hp₂ := (hC₂b p hin).2
                rw [AgreeBelow.insert σ₂ ρ (Nat.le_refl _) p.1 hp₁,
                    AgreeBelow.insert σ₂ ρ (Nat.le_refl _) p.2 hp₂]
                exact hC₂ p hin
          · rw [Ty.pSubst_mvar, Std.HashMap.getD_insert]; simp
          · exact ((AgreeBelow.insert σ₂ ρ (Nat.le_trans hnn₁ hn₁₂)).trans
              ((hag₂.mono hnn₁).trans hag₁))

/-! ## The target statement

`Target.GenerationComplete` is the checking form. It follows by taking `ρ := pSubst τ σ'` and then
putting `τ` back under the new substitution — sound because `τ` is source material, so the two
substitutions agree on it. -/

/-- **`Target.GenerationComplete`, discharged.** -/
theorem generationComplete : GenerationComplete (N := N) := by
  intro Γ t τ τg n n' C σ' hΓ ht hτ hj hty
  obtain ⟨σ'', hC, hτg, hag⟩ :=
    hj.complete_aux σ' (HasSubst.pSubst τ σ') (CtxFreshBelow.of_fresh hΓ) ht hty
  refine ⟨σ'', ?_, fun u hu => hag u hu⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hrest
  · show HasSubst.pSubst τg σ'' = HasSubst.pSubst τ σ''
    rw [hτg, hag τ hτ]
  · exact hC p hrest

end LambdaLab.Stlc.Named
