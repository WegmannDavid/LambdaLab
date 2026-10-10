import LambdaLab.Languages.SystemF.Syntax

/-!
# System F — the typing judgement

`HasType Δ Γ t A`: under `Δ` type variables in scope and the term context `Γ` (types of the free
term variables, innermost first), `t` has type `A`.

    Γ[n] = A                                   ⊢ var n : A
    A wf in Δ,   Δ; A :: Γ ⊢ t : B             ⊢ λ A . t : A → B
    Δ; Γ ⊢ t : A → B,   Δ; Γ ⊢ u : A           ⊢ t u : B
    Δ + 1; ↑Γ ⊢ t : A                          ⊢ Λ . t : ∀ A
    Δ; Γ ⊢ t : ∀ A,   B wf in Δ                ⊢ t [B] : A[0 := B]

Under `Λ` the context is shifted (`↑Γ = Γ.map (ren succ)`), because its types now sit under one
more type binder. The annotations a term carries must be well-formed — no type variable beyond
`Δ` — which is what keeps the judgement about well-scoped programs; nothing else is required of
`Γ`, and nothing in the metatheory needs more.

## The structural lemmas

All four are stated for a whole map at once, which is what the parallel-substitution algebra of
`Syntax.lean` is for:

* `HasType.ren` — weakening and exchange: a term renamed by `ξ` types in any context that agrees
  with the old one along `ξ`;
* `HasType.tren` / `HasType.tsubst` — renaming or substituting the type variables of a judgement;
* `HasType.subst` — substituting typed terms for the term variables.

Each is one induction on the derivation; the binder cases are where the composition laws earn
their keep.
-/

namespace LambdaLab.Languages.SystemF

namespace Ty

/-- Every free type variable is below `k`. -/
def wf (k : Nat) : Ty → Bool
  | var n => decide (n < k)
  | arr A B => A.wf k && B.wf k
  | all A => A.wf (k + 1)

theorem wf_ren : ∀ (A : Ty) {k k' : Nat} {ξ : Nat → Nat}, (∀ n, n < k → ξ n < k') →
    A.wf k = true → (A.ren ξ).wf k' = true
  | var n, _, _, _, h, hA => by
      simp only [wf, ren, decide_eq_true_eq] at hA ⊢
      exact h n hA
  | arr A B, _, _, _, h, hA => by
      simp only [wf, ren, Bool.and_eq_true] at hA ⊢
      exact ⟨wf_ren A h hA.1, wf_ren B h hA.2⟩
  | all A, _, _, _, h, hA => by
      simp only [wf, ren] at hA ⊢
      refine wf_ren A ?_ hA
      intro n hn
      cases n with
      | zero => exact Nat.zero_lt_succ _
      | succ n => exact Nat.succ_lt_succ (h n (Nat.lt_of_succ_lt_succ hn))

theorem wf_subst : ∀ (A : Ty) {k k' : Nat} {σ : Nat → Ty}, (∀ n, n < k → (σ n).wf k' = true) →
    A.wf k = true → (A.subst σ).wf k' = true
  | var n, _, _, _, h, hA => by
      simp only [wf, subst, decide_eq_true_eq] at hA ⊢
      exact h n hA
  | arr A B, _, _, _, h, hA => by
      simp only [wf, subst, Bool.and_eq_true] at hA ⊢
      exact ⟨wf_subst A h hA.1, wf_subst B h hA.2⟩
  | all A, _, k', _, h, hA => by
      simp only [wf, subst] at hA ⊢
      refine wf_subst A ?_ hA
      intro n hn
      cases n with
      | zero => simp [up, wf]
      | succ n =>
          simp only [up_succ]
          exact wf_ren _ (fun m hm => Nat.succ_lt_succ hm) (h n (Nat.lt_of_succ_lt_succ hn))

theorem wf_inst {A B : Ty} {k : Nat} (hA : A.wf (k + 1) = true) (hB : B.wf k = true) :
    (A.inst B).wf k = true := by
  refine wf_subst A ?_ hA
  intro n hn
  cases n with
  | zero => exact hB
  | succ n => simp only [scons_succ, wf, decide_eq_true_eq]; exact Nat.lt_of_succ_lt_succ hn

end Ty

/-- **The typing judgement.** -/
inductive HasType : Nat → List Ty → Tm → Ty → Prop
  | var {Δ : Nat} {Γ : List Ty} {n : Nat} {A : Ty} :
      Γ[n]? = some A → HasType Δ Γ (.var n) A
  | lam {Δ : Nat} {Γ : List Ty} {A : Ty} {t : Tm} {B : Ty} :
      A.wf Δ = true → HasType Δ (A :: Γ) t B → HasType Δ Γ (.lam A t) (.arr A B)
  | app {Δ : Nat} {Γ : List Ty} {t u : Tm} {A B : Ty} :
      HasType Δ Γ t (.arr A B) → HasType Δ Γ u A → HasType Δ Γ (.app t u) B
  | tlam {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} :
      HasType (Δ + 1) (Γ.map (Ty.ren Nat.succ)) t A → HasType Δ Γ (.tlam t) (.all A)
  | tapp {Δ : Nat} {Γ : List Ty} {t : Tm} {A B : Ty} :
      HasType Δ Γ t (.all A) → B.wf Δ = true → HasType Δ Γ (.tapp t B) (A.inst B)

namespace HasType

/-- Looking a variable up in a mapped context. -/
theorem getElem?_map_eq_some {Γ : List Ty} {f : Ty → Ty} {n : Nat} {B : Ty}
    (h : (Γ.map f)[n]? = some B) : ∃ B₀, Γ[n]? = some B₀ ∧ B = f B₀ := by
  rw [List.getElem?_map] at h
  cases hn : Γ[n]? with
  | none => rw [hn] at h; cases h
  | some B₀ => rw [hn] at h; exact ⟨B₀, rfl, (Option.some.inj h).symm⟩

/-- **Weakening and exchange**: rename the term variables along `ξ`, into any context that agrees
with the old one along `ξ`. -/
theorem ren {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Δ Γ t A) :
    ∀ {Γ' : List Ty} {ξ : Nat → Nat}, (∀ n B, Γ[n]? = some B → Γ'[ξ n]? = some B) →
      HasType Δ Γ' (t.ren ξ) A := by
  induction h with
  | var hn => intro _ _ hξ; exact .var (hξ _ _ hn)
  | lam hA _ ih =>
      intro Γ' ξ hξ
      refine .lam hA (ih ?_)
      intro n B hn
      cases n with
      | zero => exact hn
      | succ n => exact hξ n B hn
  | app _ _ ih₁ ih₂ => intro _ _ hξ; exact .app (ih₁ hξ) (ih₂ hξ)
  | tlam _ ih =>
      intro Γ' ξ hξ
      refine .tlam (ih ?_)
      intro n B hn
      obtain ⟨B₀, hB₀, rfl⟩ := getElem?_map_eq_some hn
      rw [List.getElem?_map, hξ n B₀ hB₀]
      rfl
  | tapp _ hB ih => intro _ _ hξ; exact .tapp (ih hξ) hB

/-- Weakening at the front: a term typed in `Γ` is typed, shifted, under one more binder. -/
theorem shift {Δ : Nat} {Γ : List Ty} {t : Tm} {A B : Ty} (h : HasType Δ Γ t A) :
    HasType Δ (B :: Γ) (t.ren Nat.succ) A :=
  h.ren (fun _ _ hn => hn)

/-- A closed term types in any context. -/
theorem weaken_closed {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Δ [] t A) :
    HasType Δ Γ t A := by
  have := h.ren (Γ' := Γ) (ξ := id) (fun _ _ hn => by simp at hn)
  rwa [Tm.ren_id] at this

theorem map_ren_succ_comm (Γ : List Ty) (ξ : Nat → Nat) :
    (Γ.map (Ty.ren Nat.succ)).map (Ty.ren (upRen ξ)) = (Γ.map (Ty.ren ξ)).map (Ty.ren Nat.succ) := by
  simp only [List.map_map]
  congr 1
  funext B
  simp only [Function.comp, Ty.ren_ren]
  rfl

/-- **Renaming the type variables of a judgement.** -/
theorem tren {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Δ Γ t A) :
    ∀ {Δ' : Nat} {ξ : Nat → Nat}, (∀ n, n < Δ → ξ n < Δ') →
      HasType Δ' (Γ.map (Ty.ren ξ)) (t.tren ξ) (A.ren ξ) := by
  induction h with
  | var hn =>
      intro _ _ _
      exact .var (by rw [List.getElem?_map, hn]; rfl)
  | lam hA _ ih =>
      intro _ _ hξ
      exact .lam (Ty.wf_ren _ hξ hA) (ih hξ)
  | app _ _ ih₁ ih₂ => intro _ _ hξ; exact .app (ih₁ hξ) (ih₂ hξ)
  | @tlam Δ Γ t A _ ih =>
      intro Δ' ξ hξ
      have h' := ih (Δ' := Δ' + 1) (ξ := upRen ξ) (by
        intro n hn
        cases n with
        | zero => exact Nat.zero_lt_succ _
        | succ n => exact Nat.succ_lt_succ (hξ n (Nat.lt_of_succ_lt_succ hn)))
      rw [map_ren_succ_comm] at h'
      exact .tlam h'
  | @tapp Δ Γ t A B _ hB ih =>
      intro _ ξ hξ
      rw [Ty.ren_inst]
      exact .tapp (ih hξ) (Ty.wf_ren _ hξ hB)

theorem map_subst_up_comm (Γ : List Ty) (σ : Nat → Ty) :
    (Γ.map (Ty.ren Nat.succ)).map (Ty.subst (Ty.up σ)) =
      (Γ.map (Ty.subst σ)).map (Ty.ren Nat.succ) := by
  simp only [List.map_map]
  congr 1
  funext B
  simp only [Function.comp, Ty.subst_ren, Ty.ren_subst]
  rfl

/-- **Substituting for the type variables of a judgement.** -/
theorem tsubst {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Δ Γ t A) :
    ∀ {Δ' : Nat} {σ : Nat → Ty}, (∀ n, n < Δ → (σ n).wf Δ' = true) →
      HasType Δ' (Γ.map (Ty.subst σ)) (t.tsubst σ) (A.subst σ) := by
  induction h with
  | var hn =>
      intro _ _ _
      exact .var (by rw [List.getElem?_map, hn]; rfl)
  | lam hA _ ih =>
      intro _ _ hσ
      exact .lam (Ty.wf_subst _ hσ hA) (ih hσ)
  | app _ _ ih₁ ih₂ => intro _ _ hσ; exact .app (ih₁ hσ) (ih₂ hσ)
  | @tlam Δ Γ t A _ ih =>
      intro Δ' σ hσ
      have h' := ih (Δ' := Δ' + 1) (σ := Ty.up σ) (by
        intro n hn
        cases n with
        | zero => simp [Ty.up, Ty.wf]
        | succ n =>
            simp only [Ty.up_succ]
            exact Ty.wf_ren _ (fun m hm => Nat.succ_lt_succ hm)
              (hσ n (Nat.lt_of_succ_lt_succ hn)))
      rw [map_subst_up_comm] at h'
      exact .tlam h'
  | @tapp Δ Γ t A B _ hB ih =>
      intro _ σ hσ
      rw [Ty.subst_inst]
      exact .tapp (ih hσ) (Ty.wf_subst _ hσ hB)

/-- **The substitution lemma**: replacing each free term variable by a term of its type preserves
the typing. -/
theorem subst {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Δ Γ t A) :
    ∀ {Γ' : List Ty} {σ : Nat → Tm}, (∀ n B, Γ[n]? = some B → HasType Δ Γ' (σ n) B) →
      HasType Δ Γ' (t.subst σ) A := by
  induction h with
  | var hn => intro _ _ hσ; exact hσ _ _ hn
  | lam hA _ ih =>
      intro Γ' σ hσ
      refine .lam hA (ih ?_)
      intro n B hn
      cases n with
      | zero => exact .var hn
      | succ n => exact (hσ n B hn).shift
  | app _ _ ih₁ ih₂ => intro _ _ hσ; exact .app (ih₁ hσ) (ih₂ hσ)
  | tlam _ ih =>
      intro Γ' σ hσ
      refine .tlam (ih ?_)
      intro n B hn
      obtain ⟨B₀, hB₀, rfl⟩ := getElem?_map_eq_some hn
      exact (hσ n B₀ hB₀).tren (fun m hm => Nat.succ_lt_succ hm)
  | tapp _ hB ih => intro _ _ hσ; exact .tapp (ih hσ) hB

/-- β's typing: instantiating a body typed under `A :: Γ` with an argument of type `A`. -/
theorem inst {Δ : Nat} {Γ : List Ty} {t u : Tm} {A B : Ty}
    (ht : HasType Δ (A :: Γ) t B) (hu : HasType Δ Γ u A) : HasType Δ Γ (t.inst u) B := by
  refine ht.subst ?_
  intro n C hn
  cases n with
  | zero => cases hn; exact hu
  | succ n => exact .var hn

/-- Type-β's typing: instantiating a body typed under one more type variable with a well-formed
type. -/
theorem tinst {Δ : Nat} {Γ : List Ty} {t : Tm} {A B : Ty}
    (ht : HasType (Δ + 1) (Γ.map (Ty.ren Nat.succ)) t A) (hB : B.wf Δ = true) :
    HasType Δ Γ (t.tinst B) (A.inst B) := by
  have h := ht.tsubst (Δ' := Δ) (σ := scons B Ty.var) (by
    intro n hn
    cases n with
    | zero => exact hB
    | succ n => simp only [scons_succ, Ty.wf, decide_eq_true_eq]; exact Nat.lt_of_succ_lt_succ hn)
  have hΓ : (Γ.map (Ty.ren Nat.succ)).map (Ty.subst (scons B Ty.var)) = Γ := by
    have hf : (Ty.subst (scons B Ty.var) ∘ Ty.ren Nat.succ) = id := by
      funext C; exact Ty.ren_succ_inst C B
    rw [List.map_map, hf, List.map_id]
  rw [hΓ] at h
  exact h

end HasType

end LambdaLab.Languages.SystemF
