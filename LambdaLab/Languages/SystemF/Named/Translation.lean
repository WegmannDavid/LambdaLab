import LambdaLab.Languages.SystemF.Named.Basic
import LambdaLab.Languages.SystemF.DeBruijn.Syntax

/-!
# System F, named — the translation to de Bruijn

`Ty.toDB Θ` and `Tm.toDB Θ Γ` replace each variable by its position in a list of binder names,
innermost first (`lookupVar`; a name absent from the list goes to the list's length). α-equivalent
terms translate to the same term, which is what lets every property proved of the de Bruijn core
be read back here.

Two lemmas carry everything, each stated for type and term variables at once and each conditioned
only on how the *free* variables are looked up:

* **renaming** (`Ty.toDB_ren`, `Tm.toDB_ren`): translating against other binder lists is renaming
  the translation, provided the free variables are looked up consistently. Taking the identity
  gives relevance (only free variables matter); taking `succ` gives that a binder the term does
  not mention is a shift.
* **substitution** (`Ty.toDB_subst`, `Tm.toDB_subst`): translating a named substitution is a de
  Bruijn substitution of the translation, provided each free variable's image translates to what
  the de Bruijn substitution puts at its position.

The binder cases of the second are where capture-avoidance pays: a binder renamed away from what
the substitution brings in is exactly what lets the renaming lemma shift those images under it.
The single substitutions follow (`Ty.toDB_inst`, `Tm.toDB_inst`, `Tm.toDB_tinst`,
`Tm.toDB_trename`).
-/

namespace LambdaLab.Languages.SystemF.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N]

/-! ## Lookup -/

/-- The position of `x` among the binders `Γ`, innermost first; `Γ.length` if it is not there. -/
def lookupVar (x : N) : List N → Nat
  | [] => 0
  | y :: ys => if y = x then 0 else lookupVar x ys + 1

@[simp] theorem lookupVar_cons_self (x : N) (Γ : List N) : lookupVar x (x :: Γ) = 0 := by
  simp [lookupVar]

theorem lookupVar_cons_ne {x y : N} (Γ : List N) (h : x ≠ y) :
    lookupVar x (y :: Γ) = lookupVar x Γ + 1 := by
  simp [lookupVar, Ne.symm h]

theorem lookupVar_lt_iff {x : N} : ∀ {Γ : List N}, lookupVar x Γ < Γ.length ↔ x ∈ Γ
  | [] => by simp [lookupVar]
  | y :: ys => by
      by_cases h : x = y
      · subst h; simp
      · rw [lookupVar_cons_ne _ h]
        simp only [List.length_cons, List.mem_cons, h, false_or]
        exact ⟨fun hl => lookupVar_lt_iff.mp (by omega), fun hm => by
          have := lookupVar_lt_iff.mpr hm; omega⟩

/-! ## The translation -/

def Ty.toDB : List N → Ty N → DeBruijn.Ty
  | Θ, .var α => .var (lookupVar α Θ)
  | Θ, .arr A B => .arr (Ty.toDB Θ A) (Ty.toDB Θ B)
  | Θ, .all α A => .all (Ty.toDB (α :: Θ) A)

def Tm.toDB : List N → List N → Tm N → DeBruijn.Tm
  | _, Γ, .var x => .var (lookupVar x Γ)
  | Θ, Γ, .lam x A b => .lam (A.toDB Θ) (Tm.toDB Θ (x :: Γ) b)
  | Θ, Γ, .app t u => .app (Tm.toDB Θ Γ t) (Tm.toDB Θ Γ u)
  | Θ, Γ, .tlam α b => .tlam (Tm.toDB (α :: Θ) Γ b)
  | Θ, Γ, .tapp t B => .tapp (Tm.toDB Θ Γ t) (B.toDB Θ)

/-! ## Membership facts -/

theorem mem_ftv_arr_left {A B : Ty N} {α : N} (h : α ∈ A.ftv) : α ∈ (Ty.arr A B).ftv := by
  simp [Ty.ftv, h]
theorem mem_ftv_arr_right {A B : Ty N} {α : N} (h : α ∈ B.ftv) : α ∈ (Ty.arr A B).ftv := by
  simp [Ty.ftv, h]
theorem mem_ftv_all {A : Ty N} {α γ : N} (h : γ ∈ A.ftv) (hne : γ ≠ α) : γ ∈ (Ty.all α A).ftv := by
  simp [Ty.ftv, List.mem_filter, h, hne]

/-! ## Renaming -/

/-- **Renaming, for types.** -/
theorem Ty.toDB_ren : ∀ (A : Ty N) (Θ Θ' : List N) (ξ : Nat → Nat),
    (∀ α ∈ A.ftv, lookupVar α Θ' = ξ (lookupVar α Θ)) → A.toDB Θ' = (A.toDB Θ).ren ξ
  | .var α, _, _, _, h => by
      simp only [Ty.toDB, DeBruijn.Ty.ren, h α (by simp [Ty.ftv])]
  | .arr A B, Θ, Θ', ξ, h => by
      simp only [Ty.toDB, DeBruijn.Ty.ren]
      rw [Ty.toDB_ren A Θ Θ' ξ (fun α hα => h α (mem_ftv_arr_left hα)),
        Ty.toDB_ren B Θ Θ' ξ (fun α hα => h α (mem_ftv_arr_right hα))]
  | .all α A, Θ, Θ', ξ, h => by
      simp only [Ty.toDB, DeBruijn.Ty.ren]
      rw [Ty.toDB_ren A (α :: Θ) (α :: Θ') (DeBruijn.upRen ξ) (fun γ hγ => by
        by_cases hγα : γ = α
        · subst hγα; simp
        · rw [lookupVar_cons_ne _ hγα, lookupVar_cons_ne _ hγα, h γ (mem_ftv_all hγ hγα)]
          rfl)]

/-- A type does not notice a binder it does not mention. -/
theorem Ty.toDB_insert {A : Ty N} {β : N} (Θ : List N) (h : β ∉ A.ftv) :
    A.toDB (β :: Θ) = (A.toDB Θ).ren Nat.succ :=
  Ty.toDB_ren A Θ (β :: Θ) Nat.succ (fun _ hγ =>
    lookupVar_cons_ne _ (fun e => h (e ▸ hγ)))

/-- **Renaming, for terms**: both kinds of variable at once. -/
theorem Tm.toDB_ren : ∀ (t : Tm N) (Θ Θ' Γ Γ' : List N) (ζ ξ : Nat → Nat),
    (∀ α ∈ t.ftv, lookupVar α Θ' = ζ (lookupVar α Θ)) →
    (∀ x ∈ t.fv, lookupVar x Γ' = ξ (lookupVar x Γ)) →
    t.toDB Θ' Γ' = ((t.toDB Θ Γ).tren ζ).ren ξ
  | .var x, _, _, _, _, _, _, _, hx => by
      simp only [Tm.toDB, DeBruijn.Tm.tren, DeBruijn.Tm.ren, hx x (by simp [Tm.fv])]
  | .lam x A b, Θ, Θ', Γ, Γ', ζ, ξ, hT, hx => by
      simp only [Tm.toDB, DeBruijn.Tm.tren, DeBruijn.Tm.ren]
      rw [Ty.toDB_ren A Θ Θ' ζ (fun α hα => hT α (by simp [Tm.ftv, hα])),
        Tm.toDB_ren b Θ Θ' (x :: Γ) (x :: Γ') ζ (DeBruijn.upRen ξ)
          (fun α hα => hT α (by simp [Tm.ftv, hα])) (fun y hy => by
            by_cases hyx : y = x
            · subst hyx; simp
            · rw [lookupVar_cons_ne _ hyx, lookupVar_cons_ne _ hyx,
                hx y (by simp [Tm.fv, List.mem_filter, hy, hyx])]
              rfl)]
  | .app t u, Θ, Θ', Γ, Γ', ζ, ξ, hT, hx => by
      simp only [Tm.toDB, DeBruijn.Tm.tren, DeBruijn.Tm.ren]
      rw [Tm.toDB_ren t Θ Θ' Γ Γ' ζ ξ (fun α hα => hT α (by simp [Tm.ftv, hα]))
          (fun y hy => hx y (by simp [Tm.fv, hy])),
        Tm.toDB_ren u Θ Θ' Γ Γ' ζ ξ (fun α hα => hT α (by simp [Tm.ftv, hα]))
          (fun y hy => hx y (by simp [Tm.fv, hy]))]
  | .tlam α b, Θ, Θ', Γ, Γ', ζ, ξ, hT, hx => by
      simp only [Tm.toDB, DeBruijn.Tm.tren, DeBruijn.Tm.ren]
      rw [Tm.toDB_ren b (α :: Θ) (α :: Θ') Γ Γ' (DeBruijn.upRen ζ) ξ (fun γ hγ => by
            by_cases hγα : γ = α
            · subst hγα; simp
            · rw [lookupVar_cons_ne _ hγα, lookupVar_cons_ne _ hγα,
                hT γ (by simp [Tm.ftv, List.mem_filter, hγ, hγα])]
              rfl)
          (fun y hy => hx y (by simpa [Tm.fv] using hy))]
  | .tapp t B, Θ, Θ', Γ, Γ', ζ, ξ, hT, hx => by
      simp only [Tm.toDB, DeBruijn.Tm.tren, DeBruijn.Tm.ren]
      rw [Tm.toDB_ren t Θ Θ' Γ Γ' ζ ξ (fun α hα => hT α (by simp [Tm.ftv, hα]))
          (fun y hy => hx y (by simpa [Tm.fv] using hy)),
        Ty.toDB_ren B Θ Θ' ζ (fun α hα => hT α (by simp [Tm.ftv, hα]))]

/-! ## Substitution -/

/-- **Substitution, for types.** -/
theorem Ty.toDB_subst : ∀ (A : Ty N) (Θ Θ' : List N) (σ : N → Ty N) (γ : Nat → DeBruijn.Ty),
    (∀ α ∈ A.ftv, (σ α).toDB Θ = γ (lookupVar α Θ')) → (A.subst σ).toDB Θ = (A.toDB Θ').subst γ
  | .var α, _, _, _, _, h => by
      simp only [Ty.subst, Ty.toDB, DeBruijn.Ty.subst]
      exact h α (by simp [Ty.ftv])
  | .arr A B, Θ, Θ', σ, γ, h => by
      simp only [Ty.subst, Ty.toDB, DeBruijn.Ty.subst]
      rw [Ty.toDB_subst A Θ Θ' σ γ (fun α hα => h α (mem_ftv_arr_left hα)),
        Ty.toDB_subst B Θ Θ' σ γ (fun α hα => h α (mem_ftv_arr_right hα))]
  | .all α A, Θ, Θ', σ, γ, h => by
      simp only [Ty.subst, Ty.toDB, DeBruijn.Ty.subst]
      generalize hβ : pick α ((A.ftv.filter (· ≠ α)).flatMap (fun γ => (σ γ).ftv)) = β
      have hfresh : β ∉ (A.ftv.filter (· ≠ α)).flatMap (fun γ => (σ γ).ftv) := hβ ▸ pick_not_mem _ _
      congr 1
      apply Ty.toDB_subst A (β :: Θ) (α :: Θ') (upd σ α (.var β)) (DeBruijn.Ty.up γ)
      intro γ' hγ'
      by_cases h1 : γ' = α
      · subst h1; simp [Ty.toDB]
      · rw [upd_ne _ _ h1, lookupVar_cons_ne _ h1, DeBruijn.Ty.up_succ,
          Ty.toDB_ren (σ γ') Θ (β :: Θ) Nat.succ (fun δ hδ => lookupVar_cons_ne _ (fun e => by
            subst e
            exact hfresh (List.mem_flatMap.mpr ⟨γ', by simp [List.mem_filter, hγ', h1], hδ⟩))),
          h γ' (mem_ftv_all hγ' h1)]

/-- **Substitution, for terms**: both kinds of variable at once. -/
theorem Tm.toDB_subst : ∀ (t : Tm N) (Θ Θ' Γ Γ' : List N) (σ : N → Ty N) (τ : N → Tm N)
    (γT : Nat → DeBruijn.Ty) (γ : Nat → DeBruijn.Tm),
    (∀ α ∈ t.ftv, (σ α).toDB Θ = γT (lookupVar α Θ')) →
    (∀ x ∈ t.fv, (τ x).toDB Θ Γ = γ (lookupVar x Γ')) →
    (t.subst σ τ).toDB Θ Γ = ((t.toDB Θ' Γ').tsubst γT).subst γ
  | .var x, _, _, _, _, _, _, _, _, _, hx => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.tsubst, DeBruijn.Tm.subst]
      exact hx x (by simp [Tm.fv])
  | .lam x A b, Θ, Θ', Γ, Γ', σ, τ, γT, γ, hT, hx => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.tsubst, DeBruijn.Tm.subst]
      generalize hz : pick x ((b.fv.filter (· ≠ x)).flatMap (fun y => (τ y).fv)) = z
      have hfresh : z ∉ (b.fv.filter (· ≠ x)).flatMap (fun y => (τ y).fv) := hz ▸ pick_not_mem _ _
      rw [Ty.toDB_subst A Θ Θ' σ γT (fun α hα => hT α (by simp [Tm.ftv, hα]))]
      congr 1
      apply Tm.toDB_subst b Θ Θ' (z :: Γ) (x :: Γ') σ (upd τ x (.var z)) γT (DeBruijn.Tm.up γ)
        (fun α hα => hT α (by simp [Tm.ftv, hα]))
      intro y hy
      by_cases hyx : y = x
      · subst hyx; simp [Tm.toDB]
      · rw [upd_ne _ _ hyx, lookupVar_cons_ne _ hyx, DeBruijn.Tm.up_succ,
          Tm.toDB_ren (τ y) Θ Θ Γ (z :: Γ) id Nat.succ (fun _ _ => rfl)
            (fun w hw => lookupVar_cons_ne _ (fun e => by
              subst e
              exact hfresh (List.mem_flatMap.mpr ⟨y, by simp [List.mem_filter, hy, hyx], hw⟩))),
          DeBruijn.Tm.tren_id, hx y (by simp [Tm.fv, List.mem_filter, hy, hyx])]
  | .app t u, Θ, Θ', Γ, Γ', σ, τ, γT, γ, hT, hx => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.tsubst, DeBruijn.Tm.subst]
      rw [Tm.toDB_subst t Θ Θ' Γ Γ' σ τ γT γ (fun α hα => hT α (by simp [Tm.ftv, hα]))
          (fun y hy => hx y (by simp [Tm.fv, hy])),
        Tm.toDB_subst u Θ Θ' Γ Γ' σ τ γT γ (fun α hα => hT α (by simp [Tm.ftv, hα]))
          (fun y hy => hx y (by simp [Tm.fv, hy]))]
  | .tlam α b, Θ, Θ', Γ, Γ', σ, τ, γT, γ, hT, hx => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.tsubst, DeBruijn.Tm.subst]
      generalize hβ : pick α ((b.ftv.filter (· ≠ α)).flatMap (fun γ => (σ γ).ftv) ++
        b.fv.flatMap (fun y => (τ y).ftv)) = β
      have hfresh : β ∉ (b.ftv.filter (· ≠ α)).flatMap (fun γ => (σ γ).ftv) ++
          b.fv.flatMap (fun y => (τ y).ftv) := hβ ▸ pick_not_mem _ _
      congr 1
      apply Tm.toDB_subst b (β :: Θ) (α :: Θ') Γ Γ' (upd σ α (.var β)) τ (DeBruijn.Ty.up γT)
        (DeBruijn.Tm.tup γ)
      · intro γ' hγ'
        by_cases h1 : γ' = α
        · subst h1; simp [Ty.toDB]
        · rw [upd_ne _ _ h1, lookupVar_cons_ne _ h1, DeBruijn.Ty.up_succ,
            Ty.toDB_ren (σ γ') Θ (β :: Θ) Nat.succ (fun δ hδ => lookupVar_cons_ne _ (fun e => by
              subst e
              exact hfresh (List.mem_append_left _
                (List.mem_flatMap.mpr ⟨γ', by simp [List.mem_filter, hγ', h1], hδ⟩)))),
            hT γ' (by simp [Tm.ftv, List.mem_filter, hγ', h1])]
      · intro y hy
        rw [Tm.toDB_ren (τ y) Θ (β :: Θ) Γ Γ Nat.succ id
            (fun δ hδ => lookupVar_cons_ne _ (fun e => by
              subst e
              exact hfresh (List.mem_append_right _ (List.mem_flatMap.mpr ⟨y, hy, hδ⟩))))
            (fun _ _ => rfl),
          DeBruijn.Tm.ren_id, hx y (by simpa [Tm.fv] using hy)]
        rfl
  | .tapp t B, Θ, Θ', Γ, Γ', σ, τ, γT, γ, hT, hx => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.tsubst, DeBruijn.Tm.subst]
      rw [Tm.toDB_subst t Θ Θ' Γ Γ' σ τ γT γ (fun α hα => hT α (by simp [Tm.ftv, hα]))
          (fun y hy => hx y (by simpa [Tm.fv] using hy)),
        Ty.toDB_subst B Θ Θ' σ γT (fun α hα => hT α (by simp [Tm.ftv, hα]))]

/-! ## The single substitutions -/

theorem Ty.toDB_inst (A : Ty N) (α : N) (B : Ty N) (Θ : List N) :
    (A.inst α B).toDB Θ = (A.toDB (α :: Θ)).inst (B.toDB Θ) := by
  refine Ty.toDB_subst A Θ (α :: Θ) _ _ ?_
  intro γ' _
  by_cases h : γ' = α
  · subst h; simp
  · rw [upd_ne _ _ h, lookupVar_cons_ne _ h]
    rfl

/-- β commutes with the translation. -/
theorem Tm.toDB_inst (b : Tm N) (x : N) (u : Tm N) (Θ Γ : List N) :
    (b.inst x u).toDB Θ Γ = (b.toDB Θ (x :: Γ)).inst (u.toDB Θ Γ) := by
  rw [Tm.inst, Tm.toDB_subst b Θ Θ Γ (x :: Γ) Ty.var (upd Tm.var x u) DeBruijn.Ty.var
      (DeBruijn.scons (u.toDB Θ Γ) DeBruijn.Tm.var) (fun _ _ => rfl) (fun y _ => by
        by_cases h : y = x
        · subst h; simp
        · rw [upd_ne _ _ h, lookupVar_cons_ne _ h]
          rfl),
    DeBruijn.Tm.tsubst_var]
  rfl

/-- Type-β commutes with the translation. -/
theorem Tm.toDB_tinst (b : Tm N) (α : N) (B : Ty N) (Θ Γ : List N) :
    (b.tinst α B).toDB Θ Γ = (b.toDB (α :: Θ) Γ).tinst (B.toDB Θ) := by
  rw [Tm.tinst, Tm.toDB_subst b Θ (α :: Θ) Γ Γ (upd Ty.var α B) Tm.var
      (DeBruijn.scons (B.toDB Θ) DeBruijn.Ty.var) DeBruijn.Tm.var (fun γ' _ => by
        by_cases h : γ' = α
        · subst h; simp
        · rw [upd_ne _ _ h, lookupVar_cons_ne _ h]
          rfl) (fun _ _ => rfl),
    DeBruijn.Tm.subst_var]
  rfl

/-- Renaming a type variable to one the term does not mention changes nothing the translation
sees. -/
theorem Tm.toDB_trename (b : Tm N) {α β : N} (Θ Γ : List N) (hβ : β ∉ (Tm.tlam α b).ftv) :
    (b.trename α β).toDB (β :: Θ) Γ = b.toDB (α :: Θ) Γ := by
  rw [Tm.trename, Tm.tinst, Tm.toDB_subst b (β :: Θ) (α :: Θ) Γ Γ (upd Ty.var α (.var β)) Tm.var
      DeBruijn.Ty.var DeBruijn.Tm.var (fun γ' hγ' => by
        by_cases h : γ' = α
        · subst h; simp [Ty.toDB]
        · have hne : γ' ≠ β := fun e => hβ (by subst e; simp [Tm.ftv, List.mem_filter, hγ', h])
          rw [upd_ne _ _ h]
          simp only [Ty.toDB, lookupVar_cons_ne _ h, lookupVar_cons_ne _ hne]) (fun _ _ => rfl),
    DeBruijn.Tm.tsubst_var, DeBruijn.Tm.subst_var]

end LambdaLab.Languages.SystemF.Named
