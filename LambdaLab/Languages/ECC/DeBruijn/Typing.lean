import LambdaLab.Languages.ECC.DeBruijn.Subtyping

/-!
# ECC — typing

A context lists the types of the free variables, innermost first: `Γ = [A₀, A₁, …]` gives index
`0` the type `A₀` (shifted past its own binder), index `1` the type `A₁`, and so on.

    ──────────────────────          Γ.lookup n = some A
     Γ ⊢ s : succ s                 ─────────────────────
     (Prop : Type 0,                   Γ ⊢ n : A
      Type i : Type (i+1))

     Γ ⊢ A : s₁    A, Γ ⊢ B : s₂          Γ ⊢ A : s₁    A, Γ ⊢ t : B    A, Γ ⊢ B : s₂
    ──────────────────────────────       ──────────────────────────────────────────────
       Γ ⊢ Π A . B : pi s₁ s₂                        Γ ⊢ λ A . t : Π A . B

     Γ ⊢ t : Π A . B    Γ ⊢ u : A         Γ ⊢ t : A    Γ ⊢ B : s    A ≼ B
    ─────────────────────────────        ───────────────────────────────────
         Γ ⊢ t u : B[0 := u]                        Γ ⊢ t : B

`pi s₁ s₂` is `Prop` when `s₂` is — a proposition may quantify over anything, `Prop` itself
included — and otherwise the larger of the two universes (`Subtyping.lean`). The last rule is
**cumulativity**: it subsumes conversion, and lets a type of a smaller universe be used in a larger
one.

## Context validity is a separate judgement

The rules never check the context: the variable rule reads a type off it, nothing more, and
`Wf Γ` (every entry is a type in the context before it) is a predicate on its own. That keeps
`HasType` a single inductive — no mutual induction with a validity judgement — and it costs
nothing: every theorem that needs a valid context says so, and on valid contexts this is the usual
system. It also makes the structural lemmas below hold *unconditionally*: renaming
(`HasType.ren`), substitution (`HasType.subst`) and conversion of the context's head
(`HasType.ctx_conv`) ask only that the variables be typed alike, never that anything be valid.
-/

namespace LambdaLab.Languages.ECC.DeBruijn

/-! ## Contexts -/

abbrev Ctx := List Tm

/-- The type of variable `n`, as seen from the whole context: shifted past the entries before it
and past its own binder. -/
def Ctx.lookup : Ctx → Nat → Option Tm
  | [], _ => none
  | A :: _, 0 => some A.shift
  | _ :: Γ, n + 1 => (Ctx.lookup Γ n).map Tm.shift

@[simp] theorem Ctx.lookup_zero (A : Tm) (Γ : Ctx) : Ctx.lookup (A :: Γ) 0 = some A.shift := rfl
@[simp] theorem Ctx.lookup_succ (A : Tm) (Γ : Ctx) (n : Nat) :
    Ctx.lookup (A :: Γ) (n + 1) = (Ctx.lookup Γ n).map Tm.shift := rfl

/-! ## The judgement -/

/-- **`Γ ⊢ t : T`.** -/
inductive HasType : Ctx → Tm → Tm → Prop where
  | sort {Γ : Ctx} {s : Srt} : HasType Γ (.sort s) (.sort s.succ)
  | var {Γ : Ctx} {n : Nat} {A : Tm} : Γ.lookup n = some A → HasType Γ (.var n) A
  | pi {Γ : Ctx} {A B : Tm} {s₁ s₂ : Srt} :
      HasType Γ A (.sort s₁) → HasType (A :: Γ) B (.sort s₂) →
      HasType Γ (.pi A B) (.sort (s₁.pi s₂))
  | lam {Γ : Ctx} {A t B : Tm} {s₁ s₂ : Srt} :
      HasType Γ A (.sort s₁) → HasType (A :: Γ) t B → HasType (A :: Γ) B (.sort s₂) →
      HasType Γ (.lam A t) (.pi A B)
  | app {Γ : Ctx} {t u A B : Tm} :
      HasType Γ t (.pi A B) → HasType Γ u A → HasType Γ (.app t u) (B.inst u)
  | cumul {Γ : Ctx} {t A B : Tm} {s : Srt} :
      HasType Γ t A → HasType Γ B (.sort s) → Sub A B → HasType Γ t B

/-- **A valid context**: every entry is a type in the context before it. -/
def Wf : Ctx → Prop
  | [] => True
  | A :: Γ => Wf Γ ∧ ∃ s, HasType Γ A (.sort s)

@[simp] theorem Wf.nil : Wf [] := trivial

theorem Wf.cons {Γ : Ctx} {A : Tm} {s : Srt} (hΓ : Wf Γ) (hA : HasType Γ A (.sort s)) :
    Wf (A :: Γ) :=
  ⟨hΓ, s, hA⟩

/-- The product type of an abstraction is well-sorted. -/
theorem HasType.pi_of_lam {Γ : Ctx} {A B : Tm} {s₁ s₂ : Srt}
    (hA : HasType Γ A (.sort s₁)) (hB : HasType (A :: Γ) B (.sort s₂)) :
    HasType Γ (.pi A B) (.sort (s₁.pi s₂)) :=
  .pi hA hB

/-! ## Renaming -/

/-- `ξ` maps `Γ`'s variables to `Δ`'s, at the renamed types. -/
def RenOk (ξ : Nat → Nat) (Γ Δ : Ctx) : Prop :=
  ∀ n A, Γ.lookup n = some A → Δ.lookup (ξ n) = some (A.ren ξ)

theorem RenOk.up {ξ : Nat → Nat} {Γ Δ : Ctx} (h : RenOk ξ Γ Δ) (A : Tm) :
    RenOk (upRen ξ) (A :: Γ) (A.ren ξ :: Δ) := by
  intro n B hB
  cases n with
  | zero =>
      simp only [Ctx.lookup_zero, Option.some.injEq] at hB
      subst hB
      simp only [upRen_zero, Ctx.lookup_zero, Tm.shift_ren_upRen]
  | succ n =>
      simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at hB
      obtain ⟨C, hC, rfl⟩ := hB
      simp only [upRen_succ, Ctx.lookup_succ, h n C hC, Option.map_some, Tm.shift_ren_upRen]

theorem RenOk.shift (Γ : Ctx) (A : Tm) : RenOk Nat.succ Γ (A :: Γ) := by
  intro n B hB
  simp only [Ctx.lookup_succ, hB, Option.map_some]

/-- **Renaming preserves typing.** -/
theorem HasType.ren {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) :
    ∀ {Δ : Ctx} {ξ : Nat → Nat}, RenOk ξ Γ Δ → HasType Δ (t.ren ξ) (T.ren ξ) := by
  induction h with
  | sort => intro Δ ξ _; exact .sort
  | var hn => intro Δ ξ hξ; exact .var (hξ _ _ hn)
  | pi _ _ ihA ihB => intro Δ ξ hξ; exact .pi (ihA hξ) (ihB (hξ.up _))
  | lam _ _ _ ihA iht ihB => intro Δ ξ hξ; exact .lam (ihA hξ) (iht (hξ.up _)) (ihB (hξ.up _))
  | app _ _ iht ihu =>
      intro Δ ξ hξ
      rw [Tm.ren_inst]
      exact .app (iht hξ) (ihu hξ)
  | cumul _ _ hc iht ihB => intro Δ ξ hξ; exact .cumul (iht hξ) (ihB hξ) (hc.ren ξ)

/-- **Weakening**: a judgement survives a new innermost variable. -/
theorem HasType.weaken {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (A : Tm) :
    HasType (A :: Γ) t.shift T.shift :=
  h.ren (RenOk.shift Γ A)

/-! ## Substitution -/

/-- `σ` sends each of `Γ`'s variables to a term of `Δ` at the substituted type. -/
def SubstOk (σ : Nat → Tm) (Γ Δ : Ctx) : Prop :=
  ∀ n A, Γ.lookup n = some A → HasType Δ (σ n) (A.subst σ)

theorem SubstOk.up {σ : Nat → Tm} {Γ Δ : Ctx} (h : SubstOk σ Γ Δ) (A : Tm) :
    SubstOk (Tm.up σ) (A :: Γ) (A.subst σ :: Δ) := by
  intro n B hB
  cases n with
  | zero =>
      simp only [Ctx.lookup_zero, Option.some.injEq] at hB
      subst hB
      rw [Tm.shift_subst_up]
      exact .var (by simp)
  | succ n =>
      simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at hB
      obtain ⟨C, hC, rfl⟩ := hB
      rw [Tm.shift_subst_up]
      exact (h n C hC).weaken _

/-- **Substitution preserves typing.** -/
theorem HasType.subst {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) :
    ∀ {Δ : Ctx} {σ : Nat → Tm}, SubstOk σ Γ Δ → HasType Δ (t.subst σ) (T.subst σ) := by
  induction h with
  | sort => intro Δ σ _; exact .sort
  | var hn => intro Δ σ hσ; exact hσ _ _ hn
  | pi _ _ ihA ihB => intro Δ σ hσ; exact .pi (ihA hσ) (ihB (hσ.up _))
  | lam _ _ _ ihA iht ihB => intro Δ σ hσ; exact .lam (ihA hσ) (iht (hσ.up _)) (ihB (hσ.up _))
  | app _ _ iht ihu =>
      intro Δ σ hσ
      rw [Tm.subst_inst]
      exact .app (iht hσ) (ihu hσ)
  | cumul _ _ hc iht ihB => intro Δ σ hσ; exact .cumul (iht hσ) (ihB hσ) (hc.subst σ)

/-- **Instantiation**: substituting a term of the bound variable's type for it. -/
theorem HasType.inst {Γ : Ctx} {A t T u : Tm} (ht : HasType (A :: Γ) t T) (hu : HasType Γ u A) :
    HasType Γ (t.inst u) (T.inst u) := by
  refine ht.subst (fun n B hB => ?_)
  cases n with
  | zero =>
      simp only [Ctx.lookup_zero, Option.some.injEq] at hB
      subst hB
      rw [show A.shift.subst (scons u Tm.var) = A from Tm.shift_inst A u]
      exact hu
  | succ n =>
      simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at hB
      obtain ⟨C, hC, rfl⟩ := hB
      rw [show C.shift.subst (scons u Tm.var) = C from Tm.shift_inst C u]
      exact .var hC

/-- **Narrowing the type of the innermost variable** to a subtype. The old type must be
well-sorted — the variable is lifted back to it — the new one need not be. -/
theorem HasType.ctx_sub {Γ : Ctx} {A A' t T : Tm} {s : Srt} (h : HasType (A :: Γ) t T)
    (hA : HasType Γ A (.sort s)) (hc : Sub A' A) :
    HasType (A' :: Γ) t T := by
  have := h.subst (σ := Tm.var) (Δ := A' :: Γ) (fun n B hB => ?_)
  · rwa [Tm.subst_var, Tm.subst_var] at this
  cases n with
  | zero =>
      simp only [Ctx.lookup_zero, Option.some.injEq] at hB
      subst hB
      rw [Tm.subst_var]
      exact .cumul (.var (by simp)) (hA.weaken A') (hc.ren Nat.succ)
  | succ n =>
      rw [Tm.subst_var]
      simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at hB
      obtain ⟨C, hC, rfl⟩ := hB
      exact .var (by simp [hC])

/-- Converting the type of the innermost variable. -/
theorem HasType.ctx_conv {Γ : Ctx} {A A' t T : Tm} {s : Srt} (h : HasType (A :: Γ) t T)
    (hA : HasType Γ A (.sort s)) (hc : Conv A A') :
    HasType (A' :: Γ) t T :=
  h.ctx_sub hA hc.symm.toSub

/-! ## Valid contexts type their variables -/

theorem Wf.lookup : ∀ {Γ : Ctx}, Wf Γ → ∀ {n : Nat} {A : Tm}, Γ.lookup n = some A →
    ∃ s, HasType Γ A (.sort s)
  | [], _, _, _, h => by simp [Ctx.lookup] at h
  | B :: Γ, ⟨hΓ, s, hB⟩, n, A, h => by
      cases n with
      | zero =>
          simp only [Ctx.lookup_zero, Option.some.injEq] at h
          subst h
          exact ⟨s, hB.weaken B⟩
      | succ n =>
          simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at h
          obtain ⟨C, hC, rfl⟩ := h
          obtain ⟨s', hs'⟩ := Wf.lookup hΓ hC
          exact ⟨s', hs'.weaken B⟩

end LambdaLab.Languages.ECC.DeBruijn
