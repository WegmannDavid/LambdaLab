/-!
# System F — syntax, de Bruijn, with parallel substitution

The core calculus every other file here is about:

    A, B ::= n | A → B | ∀ A                         (types; `n` a de Bruijn index)
    t, u ::= n | λ A . t | t u | Λ . t | t [A]       (terms)

Type variables and term variables are **separate index spaces**: `λ` binds a term variable, `Λ` a
type variable, and neither shifts the other's indices. That is what lets a term carry two families
of operations — `ren`/`subst` on its term variables, `tren`/`tsubst` on the type variables in its
annotations — which commute with each other in the ways collected at the end.

## Why parallel substitution

Every operation takes a whole map: a renaming `ξ : Nat → Nat`, or a substitution `σ : Nat → Ty`
(resp. `Nat → Tm`), and crossing a binder lifts it (`upRen`, `Ty.up`, `Tm.up`, `Tm.tup`). Single
substitution is a special case (`scons u var`), and so is shifting (`ren succ`). The payoff is that
the algebra is a handful of composition laws — rename after rename, substitute after rename,
rename after substitute, substitute after substitute — each proved once by induction, after which
the facts the metatheory needs are rewriting rather than index arithmetic.

Equality of types is syntactic: there are no names to be α-equivalent.
-/

namespace LambdaLab.Languages.SystemF.DeBruijn

/-! ## Maps on indices -/

/-- Prepend `x` to the map `σ`: index `0` goes to `x`, index `n + 1` to `σ n`. -/
def scons {X : Type} (x : X) (σ : Nat → X) : Nat → X
  | 0 => x
  | n + 1 => σ n

@[simp] theorem scons_zero {X : Type} (x : X) (σ : Nat → X) : scons x σ 0 = x := rfl
@[simp] theorem scons_succ {X : Type} (x : X) (σ : Nat → X) (n : Nat) :
    scons x σ (n + 1) = σ n := rfl

theorem scons_comp_succ {X : Type} (x : X) (σ : Nat → X) : (fun n => scons x σ (n + 1)) = σ := rfl

/-- A renaming lifted under one binder: `0` stays, everything else moves up with `ξ`. -/
def upRen (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

@[simp] theorem upRen_zero (ξ : Nat → Nat) : upRen ξ 0 = 0 := rfl
@[simp] theorem upRen_succ (ξ : Nat → Nat) (n : Nat) : upRen ξ (n + 1) = ξ n + 1 := rfl

theorem upRen_id : upRen id = id := by
  funext n; cases n <;> rfl

theorem upRen_comp (ξ ζ : Nat → Nat) : upRen (ξ ∘ ζ) = upRen ξ ∘ upRen ζ := by
  funext n; cases n <;> rfl

/-! ## Types -/

inductive Ty where
  | var : Nat → Ty
  | arr : Ty → Ty → Ty
  | all : Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

/-- Rename the free type variables. -/
def ren (ξ : Nat → Nat) : Ty → Ty
  | var n => var (ξ n)
  | arr A B => arr (A.ren ξ) (B.ren ξ)
  | all A => all (A.ren (upRen ξ))

/-- A type substitution lifted under one binder. -/
def up (σ : Nat → Ty) : Nat → Ty
  | 0 => var 0
  | n + 1 => (σ n).ren Nat.succ

/-- Substitute for the free type variables. -/
def subst (σ : Nat → Ty) : Ty → Ty
  | var n => σ n
  | arr A B => arr (A.subst σ) (B.subst σ)
  | all A => all (A.subst (up σ))

/-- Instantiate the outermost bound variable: `A.inst B` is `A[0 := B]`. -/
def inst (A B : Ty) : Ty := A.subst (scons B var)

@[simp] theorem up_zero (σ : Nat → Ty) : up σ 0 = var 0 := rfl
@[simp] theorem up_succ (σ : Nat → Ty) (n : Nat) : up σ (n + 1) = (σ n).ren Nat.succ := rfl

theorem ren_id : ∀ A : Ty, A.ren id = A
  | var _ => rfl
  | arr A B => by simp only [ren, ren_id A, ren_id B]
  | all A => by simp only [ren, upRen_id, ren_id A]

theorem ren_ren : ∀ (A : Ty) (ξ ζ : Nat → Nat), (A.ren ζ).ren ξ = A.ren (ξ ∘ ζ)
  | var _, _, _ => rfl
  | arr A B, ξ, ζ => by simp only [ren, ren_ren A, ren_ren B]
  | all A, ξ, ζ => by simp only [ren, ren_ren A, upRen_comp]

theorem up_ren (σ : Nat → Ty) (ξ : Nat → Nat) : (fun n => up σ (upRen ξ n)) = up (σ ∘ ξ) := by
  funext n; cases n <;> rfl

theorem subst_ren : ∀ (A : Ty) (σ : Nat → Ty) (ξ : Nat → Nat), (A.ren ξ).subst σ = A.subst (σ ∘ ξ)
  | var _, _, _ => rfl
  | arr A B, σ, ξ => by simp only [ren, subst, subst_ren A, subst_ren B]
  | all A, σ, ξ => by
      simp only [ren, subst, subst_ren A]
      congr 2
      exact up_ren σ ξ

theorem ren_up (σ : Nat → Ty) (ξ : Nat → Nat) :
    (fun n => (up σ n).ren (upRen ξ)) = up (fun n => (σ n).ren ξ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [up_succ, ren_ren]
      rfl

theorem ren_subst : ∀ (A : Ty) (σ : Nat → Ty) (ξ : Nat → Nat),
    (A.subst σ).ren ξ = A.subst (fun n => (σ n).ren ξ)
  | var _, _, _ => rfl
  | arr A B, σ, ξ => by simp only [subst, ren, ren_subst A, ren_subst B]
  | all A, σ, ξ => by
      simp only [subst, ren, ren_subst A]
      congr 2
      exact ren_up σ ξ

theorem up_subst (σ τ : Nat → Ty) :
    (fun n => (up σ n).subst (up τ)) = up (fun n => (σ n).subst τ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [up_succ, subst_ren, ren_subst]
      rfl

theorem subst_subst : ∀ (A : Ty) (σ τ : Nat → Ty),
    (A.subst σ).subst τ = A.subst (fun n => (σ n).subst τ)
  | var _, _, _ => rfl
  | arr A B, σ, τ => by simp only [subst, subst_subst A, subst_subst B]
  | all A, σ, τ => by
      simp only [subst, subst_subst A]
      congr 2
      exact up_subst σ τ

theorem up_var : up var = var := by
  funext n; cases n <;> rfl

theorem subst_var : ∀ A : Ty, A.subst var = A
  | var _ => rfl
  | arr A B => by simp only [subst, subst_var A, subst_var B]
  | all A => by simp only [subst, up_var, subst_var A]

/-- Renaming is substituting variables. -/
theorem ren_eq_subst : ∀ (A : Ty) (ξ : Nat → Nat), A.ren ξ = A.subst (var ∘ ξ)
  | A, ξ => by
      have := subst_ren A var ξ
      rw [subst_var] at this
      exact this

/-- Shifting a type and then instantiating the new variable gives the type back. -/
theorem ren_succ_inst (A B : Ty) : (A.ren Nat.succ).inst B = A := by
  simp only [inst, subst_ren]
  exact subst_var A

/-- Instantiation after a substitution: the substitution moves under the binder. -/
theorem subst_inst (A B : Ty) (σ : Nat → Ty) :
    (A.inst B).subst σ = (A.subst (up σ)).inst (B.subst σ) := by
  simp only [inst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [scons_succ, subst, up_succ, subst_ren]
      exact (subst_var (σ n)).symm

theorem ren_inst (A B : Ty) (ξ : Nat → Nat) :
    (A.inst B).ren ξ = (A.ren (upRen ξ)).inst (B.ren ξ) := by
  rw [ren_eq_subst, ren_eq_subst A, ren_eq_subst B, subst_inst]
  congr 2
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

end Ty

/-! ## Terms -/

inductive Tm where
  | var : Nat → Tm
  | lam : Ty → Tm → Tm
  | app : Tm → Tm → Tm
  | tlam : Tm → Tm
  | tapp : Tm → Ty → Tm
  deriving DecidableEq, Repr

namespace Tm

/-! ### Operations on the type variables of a term -/

/-- Rename the free type variables in a term's annotations. -/
def tren (ξ : Nat → Nat) : Tm → Tm
  | var n => var n
  | lam A t => lam (A.ren ξ) (t.tren ξ)
  | app t u => app (t.tren ξ) (u.tren ξ)
  | tlam t => tlam (t.tren (upRen ξ))
  | tapp t A => tapp (t.tren ξ) (A.ren ξ)

/-- Substitute for the free type variables in a term's annotations. -/
def tsubst (σ : Nat → Ty) : Tm → Tm
  | var n => var n
  | lam A t => lam (A.subst σ) (t.tsubst σ)
  | app t u => app (t.tsubst σ) (u.tsubst σ)
  | tlam t => tlam (t.tsubst (Ty.up σ))
  | tapp t A => tapp (t.tsubst σ) (A.subst σ)

/-- Instantiate a term's outermost type variable: the body of `Λ . t` at `B`. -/
def tinst (t : Tm) (B : Ty) : Tm := t.tsubst (scons B Ty.var)

theorem tren_id : ∀ t : Tm, t.tren id = t
  | var _ => rfl
  | lam A t => by simp only [tren, Ty.ren_id, tren_id t]
  | app t u => by simp only [tren, tren_id t, tren_id u]
  | tlam t => by simp only [tren, upRen_id, tren_id t]
  | tapp t A => by simp only [tren, tren_id t, Ty.ren_id]

theorem tren_tren : ∀ (t : Tm) (ξ ζ : Nat → Nat), (t.tren ζ).tren ξ = t.tren (ξ ∘ ζ)
  | var _, _, _ => rfl
  | lam A t, ξ, ζ => by simp only [tren, Ty.ren_ren, tren_tren t]
  | app t u, ξ, ζ => by simp only [tren, tren_tren t, tren_tren u]
  | tlam t, ξ, ζ => by simp only [tren, tren_tren t, upRen_comp]
  | tapp t A, ξ, ζ => by simp only [tren, tren_tren t, Ty.ren_ren]

theorem tsubst_tren : ∀ (t : Tm) (σ : Nat → Ty) (ξ : Nat → Nat),
    (t.tren ξ).tsubst σ = t.tsubst (σ ∘ ξ)
  | var _, _, _ => rfl
  | lam A t, σ, ξ => by simp only [tren, tsubst, Ty.subst_ren, tsubst_tren t]
  | app t u, σ, ξ => by simp only [tren, tsubst, tsubst_tren t, tsubst_tren u]
  | tlam t, σ, ξ => by
      simp only [tren, tsubst, tsubst_tren t]
      congr 2
      exact Ty.up_ren σ ξ
  | tapp t A, σ, ξ => by simp only [tren, tsubst, tsubst_tren t, Ty.subst_ren]

theorem tren_tsubst : ∀ (t : Tm) (σ : Nat → Ty) (ξ : Nat → Nat),
    (t.tsubst σ).tren ξ = t.tsubst (fun n => (σ n).ren ξ)
  | var _, _, _ => rfl
  | lam A t, σ, ξ => by simp only [tsubst, tren, Ty.ren_subst, tren_tsubst t]
  | app t u, σ, ξ => by simp only [tsubst, tren, tren_tsubst t, tren_tsubst u]
  | tlam t, σ, ξ => by
      simp only [tsubst, tren, tren_tsubst t]
      congr 2
      exact Ty.ren_up σ ξ
  | tapp t A, σ, ξ => by simp only [tsubst, tren, tren_tsubst t, Ty.ren_subst]

theorem tsubst_tsubst : ∀ (t : Tm) (σ τ : Nat → Ty),
    (t.tsubst σ).tsubst τ = t.tsubst (fun n => (σ n).subst τ)
  | var _, _, _ => rfl
  | lam A t, σ, τ => by simp only [tsubst, Ty.subst_subst, tsubst_tsubst t]
  | app t u, σ, τ => by simp only [tsubst, tsubst_tsubst t, tsubst_tsubst u]
  | tlam t, σ, τ => by
      simp only [tsubst, tsubst_tsubst t]
      congr 2
      exact Ty.up_subst σ τ
  | tapp t A, σ, τ => by simp only [tsubst, tsubst_tsubst t, Ty.subst_subst]

theorem tsubst_var : ∀ t : Tm, t.tsubst Ty.var = t
  | var _ => rfl
  | lam A t => by simp only [tsubst, Ty.subst_var, tsubst_var t]
  | app t u => by simp only [tsubst, tsubst_var t, tsubst_var u]
  | tlam t => by simp only [tsubst, Ty.up_var, tsubst_var t]
  | tapp t A => by simp only [tsubst, tsubst_var t, Ty.subst_var]

/-- Shifting a term's type variables and instantiating the new one gives the term back. -/
theorem tren_succ_tinst (t : Tm) (B : Ty) : (t.tren Nat.succ).tinst B = t := by
  simp only [tinst, tsubst_tren]
  exact tsubst_var t

/-! ### Operations on the term variables of a term -/

/-- Rename the free term variables. `Λ` binds no term variable, so it is crossed unlifted. -/
def ren (ξ : Nat → Nat) : Tm → Tm
  | var n => var (ξ n)
  | lam A t => lam A (t.ren (upRen ξ))
  | app t u => app (t.ren ξ) (u.ren ξ)
  | tlam t => tlam (t.ren ξ)
  | tapp t A => tapp (t.ren ξ) A

/-- A term substitution lifted under a `λ`. -/
def up (σ : Nat → Tm) : Nat → Tm
  | 0 => var 0
  | n + 1 => (σ n).ren Nat.succ

/-- A term substitution carried under a `Λ`: the substituted terms now sit under one more type
binder, so their type variables shift. -/
def tup (σ : Nat → Tm) : Nat → Tm := fun n => (σ n).tren Nat.succ

/-- Substitute for the free term variables. -/
def subst (σ : Nat → Tm) : Tm → Tm
  | var n => σ n
  | lam A t => lam A (t.subst (up σ))
  | app t u => app (t.subst σ) (u.subst σ)
  | tlam t => tlam (t.subst (tup σ))
  | tapp t A => tapp (t.subst σ) A

/-- Instantiate the outermost bound term variable: the body of `λ A . t` at `u`. -/
def inst (t u : Tm) : Tm := t.subst (scons u var)

@[simp] theorem up_zero (σ : Nat → Tm) : up σ 0 = var 0 := rfl
@[simp] theorem up_succ (σ : Nat → Tm) (n : Nat) : up σ (n + 1) = (σ n).ren Nat.succ := rfl

/-! #### The two kinds of operation commute -/

theorem ren_tren : ∀ (t : Tm) (ξ ζ : Nat → Nat), (t.tren ζ).ren ξ = (t.ren ξ).tren ζ
  | var _, _, _ => rfl
  | lam A t, ξ, ζ => by simp only [tren, ren, ren_tren t]
  | app t u, ξ, ζ => by simp only [tren, ren, ren_tren t, ren_tren u]
  | tlam t, ξ, ζ => by simp only [tren, ren, ren_tren t]
  | tapp t A, ξ, ζ => by simp only [tren, ren, ren_tren t]

theorem ren_tsubst : ∀ (t : Tm) (ξ : Nat → Nat) (σ : Nat → Ty), (t.tsubst σ).ren ξ = (t.ren ξ).tsubst σ
  | var _, _, _ => rfl
  | lam A t, ξ, σ => by simp only [tsubst, ren, ren_tsubst t]
  | app t u, ξ, σ => by simp only [tsubst, ren, ren_tsubst t, ren_tsubst u]
  | tlam t, ξ, σ => by simp only [tsubst, ren, ren_tsubst t]
  | tapp t A, ξ, σ => by simp only [tsubst, ren, ren_tsubst t]

/-! #### Term renaming and substitution -/

theorem ren_id : ∀ t : Tm, t.ren id = t
  | var _ => rfl
  | lam A t => by simp only [ren, upRen_id, ren_id t]
  | app t u => by simp only [ren, ren_id t, ren_id u]
  | tlam t => by simp only [ren, ren_id t]
  | tapp t A => by simp only [ren, ren_id t]

theorem ren_ren : ∀ (t : Tm) (ξ ζ : Nat → Nat), (t.ren ζ).ren ξ = t.ren (ξ ∘ ζ)
  | var _, _, _ => rfl
  | lam A t, ξ, ζ => by simp only [ren, ren_ren t, upRen_comp]
  | app t u, ξ, ζ => by simp only [ren, ren_ren t, ren_ren u]
  | tlam t, ξ, ζ => by simp only [ren, ren_ren t]
  | tapp t A, ξ, ζ => by simp only [ren, ren_ren t]

theorem up_ren (σ : Nat → Tm) (ξ : Nat → Nat) : (fun n => up σ (upRen ξ n)) = up (σ ∘ ξ) := by
  funext n; cases n <;> rfl

theorem subst_ren : ∀ (t : Tm) (σ : Nat → Tm) (ξ : Nat → Nat), (t.ren ξ).subst σ = t.subst (σ ∘ ξ)
  | var _, _, _ => rfl
  | lam A t, σ, ξ => by
      simp only [ren, subst, subst_ren t]
      congr 2
      exact up_ren σ ξ
  | app t u, σ, ξ => by simp only [ren, subst, subst_ren t, subst_ren u]
  | tlam t, σ, ξ => by simp only [ren, subst, subst_ren t]; rfl
  | tapp t A, σ, ξ => by simp only [ren, subst, subst_ren t]

theorem ren_up (σ : Nat → Tm) (ξ : Nat → Nat) :
    (fun n => (up σ n).ren (upRen ξ)) = up (fun n => (σ n).ren ξ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [up_succ, ren_ren]
      rfl

theorem ren_tup (σ : Nat → Tm) (ξ : Nat → Nat) :
    (fun n => (tup σ n).ren ξ) = tup (fun n => (σ n).ren ξ) := by
  funext n
  simp only [tup, ren_tren]

theorem ren_subst : ∀ (t : Tm) (σ : Nat → Tm) (ξ : Nat → Nat),
    (t.subst σ).ren ξ = t.subst (fun n => (σ n).ren ξ)
  | var _, _, _ => rfl
  | lam A t, σ, ξ => by
      simp only [subst, ren, ren_subst t]
      congr 2
      exact ren_up σ ξ
  | app t u, σ, ξ => by simp only [subst, ren, ren_subst t, ren_subst u]
  | tlam t, σ, ξ => by
      simp only [subst, ren, ren_subst t]
      congr 2
      exact ren_tup σ ξ
  | tapp t A, σ, ξ => by simp only [subst, ren, ren_subst t]

/-- Term substitution commutes with renaming the type variables, provided the substituted terms
are renamed too. -/
theorem tren_subst : ∀ (t : Tm) (σ : Nat → Tm) (ξ : Nat → Nat),
    (t.subst σ).tren ξ = (t.tren ξ).subst (fun n => (σ n).tren ξ)
  | var _, _, _ => rfl
  | lam A t, σ, ξ => by
      simp only [subst, tren, tren_subst t]
      congr 2
      funext n
      cases n with
      | zero => rfl
      | succ n => simp only [up_succ, ren_tren]
  | app t u, σ, ξ => by simp only [subst, tren, tren_subst t, tren_subst u]
  | tlam t, σ, ξ => by
      simp only [subst, tren, tren_subst t]
      congr 2
      funext n
      simp only [tup, tren_tren]
      rfl
  | tapp t A, σ, ξ => by simp only [subst, tren, tren_subst t]

/-- …and with substituting for them. -/
theorem tsubst_subst : ∀ (t : Tm) (σ : Nat → Tm) (τ : Nat → Ty),
    (t.subst σ).tsubst τ = (t.tsubst τ).subst (fun n => (σ n).tsubst τ)
  | var _, _, _ => rfl
  | lam A t, σ, τ => by
      simp only [subst, tsubst, tsubst_subst t]
      congr 2
      funext n
      cases n with
      | zero => rfl
      | succ n => simp only [up_succ, ren_tsubst]
  | app t u, σ, τ => by simp only [subst, tsubst, tsubst_subst t, tsubst_subst u]
  | tlam t, σ, τ => by
      simp only [subst, tsubst, tsubst_subst t]
      congr 2
      funext n
      simp only [tup, tsubst_tren, tren_tsubst]
      rfl
  | tapp t A, σ, τ => by simp only [subst, tsubst, tsubst_subst t]

theorem up_subst (σ τ : Nat → Tm) :
    (fun n => (up σ n).subst (up τ)) = up (fun n => (σ n).subst τ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [up_succ, subst_ren, ren_subst]
      rfl

theorem tup_subst (σ τ : Nat → Tm) :
    (fun n => (tup σ n).subst (tup τ)) = tup (fun n => (σ n).subst τ) := by
  funext n
  simp only [tup, tren_subst]
  rfl

theorem subst_subst : ∀ (t : Tm) (σ τ : Nat → Tm),
    (t.subst σ).subst τ = t.subst (fun n => (σ n).subst τ)
  | var _, _, _ => rfl
  | lam A t, σ, τ => by
      simp only [subst, subst_subst t]
      congr 2
      exact up_subst σ τ
  | app t u, σ, τ => by simp only [subst, subst_subst t, subst_subst u]
  | tlam t, σ, τ => by
      simp only [subst, subst_subst t]
      congr 2
      exact tup_subst σ τ
  | tapp t A, σ, τ => by simp only [subst, subst_subst t]

theorem up_var : up var = var := by
  funext n; cases n <;> rfl

theorem tup_var : tup var = var := by
  funext n; rfl

theorem subst_var : ∀ t : Tm, t.subst var = t
  | var _ => rfl
  | lam A t => by simp only [subst, up_var, subst_var t]
  | app t u => by simp only [subst, subst_var t, subst_var u]
  | tlam t => by simp only [subst, tup_var, subst_var t]
  | tapp t A => by simp only [subst, subst_var t]

theorem ren_eq_subst (t : Tm) (ξ : Nat → Nat) : t.ren ξ = t.subst (var ∘ ξ) := by
  have := subst_ren t var ξ
  rw [subst_var] at this
  exact this

/-! #### Instantiation, in the forms reduction needs -/

/-- β under a substitution: substituting into `t[0 := u]` is substituting under the binder and
then instantiating with the substituted argument. -/
theorem inst_subst (t u : Tm) (σ : Nat → Tm) :
    (t.inst u).subst σ = (t.subst (up σ)).inst (u.subst σ) := by
  simp only [inst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [scons_succ, subst, up_succ, subst_ren]
      exact (subst_var (σ n)).symm

/-- β under a type substitution. -/
theorem inst_tsubst (t u : Tm) (σ : Nat → Ty) :
    (t.inst u).tsubst σ = (t.tsubst σ).inst (u.tsubst σ) := by
  simp only [inst, tsubst_subst]
  congr 1
  funext n
  cases n <;> rfl

/-- Type-β under a term substitution. -/
theorem tinst_subst (t : Tm) (B : Ty) (σ : Nat → Tm) :
    (t.tinst B).subst σ = (t.subst (tup σ)).tinst B := by
  simp only [tinst, tsubst_subst]
  congr 1
  funext n
  simp only [tup, tsubst_tren]
  exact (tsubst_var (σ n)).symm

/-- Type-β under a type substitution. -/
theorem tinst_tsubst (t : Tm) (B : Ty) (σ : Nat → Ty) :
    (t.tinst B).tsubst σ = (t.tsubst (Ty.up σ)).tinst (B.subst σ) := by
  simp only [tinst, tsubst_tsubst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [scons_succ, Ty.subst, Ty.up_succ, Ty.subst_ren]
      exact (Ty.subst_var (σ n)).symm

end Tm

end LambdaLab.Languages.SystemF.DeBruijn
