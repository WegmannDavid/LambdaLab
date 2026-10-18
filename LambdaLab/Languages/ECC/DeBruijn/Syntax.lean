/-!
# ECC — syntax, de Bruijn, with parallel substitution

Luo's Extended Calculus of Constructions, without Σ-types: the Calculus of Constructions with an
impredicative `Prop` under a cumulative hierarchy of predicative universes. Terms and types are
one syntax:

    s    ::= Prop | Type i                            (sorts, `i` a natural number)
    t, A ::= n | s | Π A . B | λ A . t | t u           (`n` a de Bruijn index)

`Π A . B` and `λ A . t` bind index `0` in `B` resp. `t`. There is a single index space — a type
may mention a term variable and a term a type variable alike — so there is one renaming and one
substitution, unlike System F's two of each.

## Why parallel substitution

As in System F (`Languages/SystemF/DeBruijn/Syntax.lean`): every operation takes a whole map — a
renaming `ξ : Nat → Nat` or a substitution `σ : Nat → Tm` — and crossing a binder lifts it
(`upRen`, `up`). Single substitution (`inst`) and shifting (`shift`) are special cases, and the
algebra is four composition laws, each proved once by induction.
-/

namespace LambdaLab.Languages.ECC.DeBruijn

/-! ## Maps on indices -/

/-- Prepend `x` to the map `σ`: index `0` goes to `x`, index `n + 1` to `σ n`. -/
def scons {X : Type} (x : X) (σ : Nat → X) : Nat → X
  | 0 => x
  | n + 1 => σ n

@[simp] theorem scons_zero {X : Type} (x : X) (σ : Nat → X) : scons x σ 0 = x := rfl
@[simp] theorem scons_succ {X : Type} (x : X) (σ : Nat → X) (n : Nat) :
    scons x σ (n + 1) = σ n := rfl

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

/-! ## Terms -/

/-- The sorts: `Prop`, impredicative, and the predicative universes `Type 0, Type 1, …`. -/
inductive Srt where
  | prop
  | type (i : Nat)
  deriving DecidableEq, Repr

inductive Tm where
  | var : Nat → Tm
  | sort : Srt → Tm
  | pi : Tm → Tm → Tm
  | lam : Tm → Tm → Tm
  | app : Tm → Tm → Tm
  deriving DecidableEq, Repr

namespace Tm

/-- Rename the free variables. -/
def ren (ξ : Nat → Nat) : Tm → Tm
  | var n => var (ξ n)
  | sort s => sort s
  | pi A B => pi (A.ren ξ) (B.ren (upRen ξ))
  | lam A t => lam (A.ren ξ) (t.ren (upRen ξ))
  | app t u => app (t.ren ξ) (u.ren ξ)

/-- Shift every free variable up by one: the term, seen under one more binder. -/
abbrev shift (t : Tm) : Tm := t.ren Nat.succ

/-- A substitution lifted under one binder. -/
def up (σ : Nat → Tm) : Nat → Tm
  | 0 => var 0
  | n + 1 => (σ n).shift

/-- Substitute for the free variables. -/
def subst (σ : Nat → Tm) : Tm → Tm
  | var n => σ n
  | sort s => sort s
  | pi A B => pi (A.subst σ) (B.subst (up σ))
  | lam A t => lam (A.subst σ) (t.subst (up σ))
  | app t u => app (t.subst σ) (u.subst σ)

/-- Instantiate the outermost bound variable: `t.inst u` is `t[0 := u]`. -/
def inst (t u : Tm) : Tm := t.subst (scons u var)

@[simp] theorem up_zero (σ : Nat → Tm) : up σ 0 = var 0 := rfl
@[simp] theorem up_succ (σ : Nat → Tm) (n : Nat) : up σ (n + 1) = (σ n).ren Nat.succ := rfl

/-! ## The composition laws -/

theorem ren_id : ∀ t : Tm, t.ren id = t
  | var _ => rfl
  | sort _ => rfl
  | pi A B => by simp only [ren, upRen_id, ren_id A, ren_id B]
  | lam A t => by simp only [ren, upRen_id, ren_id A, ren_id t]
  | app t u => by simp only [ren, ren_id t, ren_id u]

theorem ren_ren : ∀ (t : Tm) (ξ ζ : Nat → Nat), (t.ren ζ).ren ξ = t.ren (ξ ∘ ζ)
  | var _, _, _ => rfl
  | sort _, _, _ => rfl
  | pi A B, ξ, ζ => by simp only [ren, ren_ren A, ren_ren B, upRen_comp]
  | lam A t, ξ, ζ => by simp only [ren, ren_ren A, ren_ren t, upRen_comp]
  | app t u, ξ, ζ => by simp only [ren, ren_ren t, ren_ren u]

theorem up_ren (σ : Nat → Tm) (ξ : Nat → Nat) : (fun n => up σ (upRen ξ n)) = up (σ ∘ ξ) := by
  funext n; cases n <;> rfl

theorem subst_ren : ∀ (t : Tm) (σ : Nat → Tm) (ξ : Nat → Nat), (t.ren ξ).subst σ = t.subst (σ ∘ ξ)
  | var _, _, _ => rfl
  | sort _, _, _ => rfl
  | pi A B, σ, ξ => by
      simp only [ren, subst, subst_ren A, subst_ren B]
      congr 2
      exact up_ren σ ξ
  | lam A t, σ, ξ => by
      simp only [ren, subst, subst_ren A, subst_ren t]
      congr 2
      exact up_ren σ ξ
  | app t u, σ, ξ => by simp only [ren, subst, subst_ren t, subst_ren u]

theorem ren_up (σ : Nat → Tm) (ξ : Nat → Nat) :
    (fun n => (up σ n).ren (upRen ξ)) = up (fun n => (σ n).ren ξ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [up_succ, ren_ren]
      rfl

theorem ren_subst : ∀ (t : Tm) (σ : Nat → Tm) (ξ : Nat → Nat),
    (t.subst σ).ren ξ = t.subst (fun n => (σ n).ren ξ)
  | var _, _, _ => rfl
  | sort _, _, _ => rfl
  | pi A B, σ, ξ => by
      simp only [subst, ren, ren_subst A, ren_subst B]
      congr 2
      exact ren_up σ ξ
  | lam A t, σ, ξ => by
      simp only [subst, ren, ren_subst A, ren_subst t]
      congr 2
      exact ren_up σ ξ
  | app t u, σ, ξ => by simp only [subst, ren, ren_subst t, ren_subst u]

theorem up_subst (σ τ : Nat → Tm) :
    (fun n => (up σ n).subst (up τ)) = up (fun n => (σ n).subst τ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [up_succ, subst_ren, ren_subst]
      rfl

theorem subst_subst : ∀ (t : Tm) (σ τ : Nat → Tm),
    (t.subst σ).subst τ = t.subst (fun n => (σ n).subst τ)
  | var _, _, _ => rfl
  | sort _, _, _ => rfl
  | pi A B, σ, τ => by
      simp only [subst, subst_subst A, subst_subst B]
      congr 2
      exact up_subst σ τ
  | lam A t, σ, τ => by
      simp only [subst, subst_subst A, subst_subst t]
      congr 2
      exact up_subst σ τ
  | app t u, σ, τ => by simp only [subst, subst_subst t, subst_subst u]

theorem up_var : up var = var := by
  funext n; cases n <;> rfl

theorem subst_var : ∀ t : Tm, t.subst var = t
  | var _ => rfl
  | sort _ => rfl
  | pi A B => by simp only [subst, up_var, subst_var A, subst_var B]
  | lam A t => by simp only [subst, up_var, subst_var A, subst_var t]
  | app t u => by simp only [subst, subst_var t, subst_var u]

/-- Renaming is substituting variables. -/
theorem ren_eq_subst (t : Tm) (ξ : Nat → Nat) : t.ren ξ = t.subst (var ∘ ξ) := by
  have := subst_ren t var ξ
  rw [subst_var] at this
  exact this

/-- Two substitutions that agree pointwise agree on every term. -/
theorem subst_congr {σ τ : Nat → Tm} (h : ∀ n, σ n = τ n) (t : Tm) : t.subst σ = t.subst τ := by
  rw [show σ = τ from funext h]

/-! ## Instantiation -/

/-- Shifting a term and then instantiating the new variable gives the term back. -/
theorem shift_inst (t u : Tm) : t.shift.inst u = t := by
  simp only [inst, shift, subst_ren]
  exact subst_var t

/-- A substitution after a shift is the shifted-away substitution. -/
theorem shift_subst (t : Tm) (σ : Nat → Tm) : t.shift.subst σ = t.subst (fun n => σ (n + 1)) :=
  subst_ren t σ Nat.succ

/-- Lifting a substitution and shifting commute. -/
theorem shift_subst_up (t : Tm) (σ : Nat → Tm) : t.shift.subst (up σ) = (t.subst σ).shift := by
  rw [shift_subst, shift, ren_subst]
  rfl

theorem shift_ren_upRen (t : Tm) (ξ : Nat → Nat) : t.shift.ren (upRen ξ) = (t.ren ξ).shift := by
  simp only [shift, ren_ren]
  rfl

/-- Instantiation after a substitution: the substitution moves under the binder. -/
theorem subst_inst (t u : Tm) (σ : Nat → Tm) :
    (t.inst u).subst σ = (t.subst (up σ)).inst (u.subst σ) := by
  simp only [inst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [scons_succ, subst, up_succ, subst_ren]
      exact (subst_var (σ n)).symm

theorem ren_inst (t u : Tm) (ξ : Nat → Nat) :
    (t.inst u).ren ξ = (t.ren (upRen ξ)).inst (u.ren ξ) := by
  rw [ren_eq_subst, ren_eq_subst t, ren_eq_subst u, subst_inst]
  congr 2
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

/-- Instantiating under a lifted substitution is substituting with the argument consed on. -/
theorem up_inst (t u : Tm) (σ : Nat → Tm) : (t.subst (up σ)).inst u = t.subst (scons u σ) := by
  simp only [inst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [up_succ, subst_ren]
      exact subst_var (σ n)

/-! ## Sizes -/

/-- A structural size, every constructor counting one. -/
def size : Tm → Nat
  | var _ => 1
  | sort _ => 1
  | pi A B => A.size + B.size + 1
  | lam A t => A.size + t.size + 1
  | app t u => t.size + u.size + 1

theorem size_ren : ∀ (t : Tm) (ξ : Nat → Nat), (t.ren ξ).size = t.size
  | var _, _ => rfl
  | sort _, _ => rfl
  | pi A B, ξ => by simp only [ren, size, size_ren A, size_ren B]
  | lam A t, ξ => by simp only [ren, size, size_ren A, size_ren t]
  | app t u, ξ => by simp only [ren, size, size_ren t, size_ren u]

end Tm

end LambdaLab.Languages.ECC.DeBruijn
