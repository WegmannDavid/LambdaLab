/-!
# CoC with inductive types — syntax, de Bruijn, with parallel substitution

The Calculus of Constructions (`Languages/CoC/`), extended with first-order inductive types:

    s    ::= * | □
    t, A ::= n | s | Π A . B | λ A . t | t u
           | Ind i                         the i-th inductive type of the signature
           | Ctor i k m [t₁, …, tₙ]        its k-th constructor, applied to all its arguments
           | Elim i C [b₁, …, bₘ] t        its recursor: into C, one branch per constructor

The inductive types live in a **signature** (`Typing.lean`), referred to by index. Constructor
and recursor applications are **saturated**: a node carries all its arguments. That keeps every
proof about the core structural — the one new reduction, ι, fires at a single node
(`Elim … (Ctor …) ⟶ …`, `Reduction.lean`), not on an application spine. A source program may
still use a constructor or recursor unapplied; elaboration makes a function of it.

The argument lists are terms themselves — `tnil` and `tcons` — so that a list is a subterm, and
renaming, substitution, reduction and every induction reach into it with no help. `m`, the
constructor's **recursion mask**, records which of its arguments are of the type itself; ι needs
it to know where to recurse, and keeping it on the node keeps reduction independent of the
signature.

## Why parallel substitution

As in CoC: every operation takes a whole map, and crossing a binder lifts it. Single substitution
(`inst`) and shifting (`shift`) are special cases.
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

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

/-- The two sorts: `*` (the impredicative sort of types and propositions) and `□` (of kinds). -/
inductive Srt where
  | star
  | box
  deriving DecidableEq, Repr

inductive Tm where
  | var : Nat → Tm
  | sort : Srt → Tm
  | pi : Tm → Tm → Tm
  | lam : Tm → Tm → Tm
  | app : Tm → Tm → Tm
  /-- The `i`-th inductive type. -/
  | ind : Nat → Tm
  /-- Constructor `k` of inductive `i`, with recursion mask `m`, applied to an argument list. -/
  | ctor : Nat → Nat → List Bool → Tm → Tm
  /-- The recursor of inductive `i`, into `C`, with a branch list, applied to a target. -/
  | elim : Nat → Tm → Tm → Tm → Tm
  /-- The empty argument list. -/
  | tnil : Tm
  /-- A nonempty argument list. -/
  | tcons : Tm → Tm → Tm
  deriving DecidableEq, Repr

namespace Tm

/-- Rename the free variables. -/
def ren (ξ : Nat → Nat) : Tm → Tm
  | var n => var (ξ n)
  | sort s => sort s
  | pi A B => pi (A.ren ξ) (B.ren (upRen ξ))
  | lam A t => lam (A.ren ξ) (t.ren (upRen ξ))
  | app t u => app (t.ren ξ) (u.ren ξ)
  | ind i => ind i
  | ctor i k m as => ctor i k m (as.ren ξ)
  | elim i C bs t => elim i (C.ren ξ) (bs.ren ξ) (t.ren ξ)
  | tnil => tnil
  | tcons a l => tcons (a.ren ξ) (l.ren ξ)

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
  | ind i => ind i
  | ctor i k m as => ctor i k m (as.subst σ)
  | elim i C bs t => elim i (C.subst σ) (bs.subst σ) (t.subst σ)
  | tnil => tnil
  | tcons a l => tcons (a.subst σ) (l.subst σ)

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
  | ind _ => rfl
  | ctor _ _ _ as => by simp only [ren, ren_id as]
  | elim _ C bs t => by simp only [ren, ren_id C, ren_id bs, ren_id t]
  | tnil => rfl
  | tcons a l => by simp only [ren, ren_id a, ren_id l]

theorem ren_ren : ∀ (t : Tm) (ξ ζ : Nat → Nat), (t.ren ζ).ren ξ = t.ren (ξ ∘ ζ)
  | var _, _, _ => rfl
  | sort _, _, _ => rfl
  | pi A B, ξ, ζ => by simp only [ren, ren_ren A, ren_ren B, upRen_comp]
  | lam A t, ξ, ζ => by simp only [ren, ren_ren A, ren_ren t, upRen_comp]
  | app t u, ξ, ζ => by simp only [ren, ren_ren t, ren_ren u]
  | ind _, _, _ => rfl
  | ctor _ _ _ as, ξ, ζ => by simp only [ren, ren_ren as]
  | elim _ C bs t, ξ, ζ => by simp only [ren, ren_ren C, ren_ren bs, ren_ren t]
  | tnil, _, _ => rfl
  | tcons a l, ξ, ζ => by simp only [ren, ren_ren a, ren_ren l]

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
  | ind _, _, _ => rfl
  | ctor _ _ _ as, σ, ξ => by simp only [ren, subst, subst_ren as]
  | elim _ C bs t, σ, ξ => by simp only [ren, subst, subst_ren C, subst_ren bs, subst_ren t]
  | tnil, _, _ => rfl
  | tcons a l, σ, ξ => by simp only [ren, subst, subst_ren a, subst_ren l]

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
  | ind _, _, _ => rfl
  | ctor _ _ _ as, σ, ξ => by simp only [subst, ren, ren_subst as]
  | elim _ C bs t, σ, ξ => by simp only [subst, ren, ren_subst C, ren_subst bs, ren_subst t]
  | tnil, _, _ => rfl
  | tcons a l, σ, ξ => by simp only [subst, ren, ren_subst a, ren_subst l]

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
  | ind _, _, _ => rfl
  | ctor _ _ _ as, σ, τ => by simp only [subst, subst_subst as]
  | elim _ C bs t, σ, τ => by simp only [subst, subst_subst C, subst_subst bs, subst_subst t]
  | tnil, _, _ => rfl
  | tcons a l, σ, τ => by simp only [subst, subst_subst a, subst_subst l]

theorem up_var : up var = var := by
  funext n; cases n <;> rfl

theorem subst_var : ∀ t : Tm, t.subst var = t
  | var _ => rfl
  | sort _ => rfl
  | pi A B => by simp only [subst, up_var, subst_var A, subst_var B]
  | lam A t => by simp only [subst, up_var, subst_var A, subst_var t]
  | app t u => by simp only [subst, subst_var t, subst_var u]
  | ind _ => rfl
  | ctor _ _ _ as => by simp only [subst, subst_var as]
  | elim _ C bs t => by simp only [subst, subst_var C, subst_var bs, subst_var t]
  | tnil => rfl
  | tcons a l => by simp only [subst, subst_var a, subst_var l]

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

/-! ## Argument lists -/

/-- The elements of an argument list (junk past a non-list tail). -/
def toList : Tm → List Tm
  | tcons a l => a :: l.toList
  | _ => []

/-- Is this a well-formed argument list? -/
def isList : Tm → Bool
  | tnil => true
  | tcons _ l => l.isList
  | _ => false

/-- An argument list from a list. -/
def ofList : List Tm → Tm
  | [] => tnil
  | a :: as => tcons a (ofList as)

/-- The `k`-th element (junk past the end). -/
def nth (l : Tm) (k : Nat) : Tm := l.toList.getD k (sort .star)

@[simp] theorem nth_tcons_zero (a l : Tm) : (tcons a l).nth 0 = a := rfl
@[simp] theorem nth_tcons_succ (a l : Tm) (k : Nat) : (tcons a l).nth (k + 1) = l.nth k := rfl

theorem toList_subst : ∀ (l : Tm) (σ : Nat → Tm), l.isList = true →
    (l.subst σ).toList = l.toList.map (·.subst σ)
  | tnil, _, _ => rfl
  | tcons a l, σ, h => by
      simp only [isList] at h
      simp only [subst, toList, toList_subst l σ h, List.map_cons]
  | var _, _, h => by simp [isList] at h
  | sort _, _, h => by simp [isList] at h
  | pi _ _, _, h => by simp [isList] at h
  | lam _ _, _, h => by simp [isList] at h
  | app _ _, _, h => by simp [isList] at h
  | ind _, _, h => by simp [isList] at h
  | ctor _ _ _ _, _, h => by simp [isList] at h
  | elim _ _ _ _, _, h => by simp [isList] at h

theorem isList_subst : ∀ (l : Tm) (σ : Nat → Tm), l.isList = true → (l.subst σ).isList = true
  | tnil, _, _ => rfl
  | tcons _ l, σ, h => isList_subst l σ h
  | var _, _, h => by simp [isList] at h
  | sort _, _, h => by simp [isList] at h
  | pi _ _, _, h => by simp [isList] at h
  | lam _ _, _, h => by simp [isList] at h
  | app _ _, _, h => by simp [isList] at h
  | ind _, _, h => by simp [isList] at h
  | ctor _ _ _ _, _, h => by simp [isList] at h
  | elim _ _ _ _, _, h => by simp [isList] at h

theorem isList_ren (l : Tm) (ξ : Nat → Nat) (h : l.isList = true) : (l.ren ξ).isList = true := by
  rw [ren_eq_subst]; exact isList_subst l _ h

theorem toList_ren (l : Tm) (ξ : Nat → Nat) (hl : l.isList = true) :
    (l.ren ξ).toList = l.toList.map (·.ren ξ) := by
  rw [ren_eq_subst, toList_subst l _ hl]
  congr 1
  funext t
  exact (ren_eq_subst t ξ).symm

theorem nth_subst {l : Tm} (hl : l.isList = true) (σ : Nat → Tm) (k : Nat) :
    (l.subst σ).nth k = (l.nth k).subst σ := by
  simp only [nth, toList_subst l σ hl]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l.toList[k]? <;> rfl

theorem nth_ren {l : Tm} (hl : l.isList = true) (ξ : Nat → Nat) (k : Nat) :
    (l.ren ξ).nth k = (l.nth k).ren ξ := by
  rw [ren_eq_subst, nth_subst hl, ← ren_eq_subst]

/-! ## Application spines, and the ι contractum -/

/-- Apply a term to a list of arguments, left to right. -/
def apps (h : Tm) : List Tm → Tm
  | [] => h
  | a :: as => apps (app h a) as

theorem apps_subst : ∀ (h : Tm) (as : List Tm) (σ : Nat → Tm),
    (apps h as).subst σ = apps (h.subst σ) (as.map (·.subst σ))
  | _, [], _ => rfl
  | h, a :: as, σ => by simp only [apps, apps_subst (app h a) as σ, subst, List.map_cons]

/-- The recursive calls a constructor's arguments call for, in order: one per argument the mask
marks as recursive. -/
def recCalls (i : Nat) (C bs : Tm) (as : List Tm) (mask : List Bool) : List Tm :=
  (as.zip mask).filterMap fun p => if p.2 then some (elim i C bs p.1) else none

/-- **The ι contractum**: the `k`-th branch, applied to the constructor's arguments and then to
the results of recursing on its recursive ones. -/
def iotaRhs (i : Nat) (C bs : Tm) (k : Nat) (mask : List Bool) (as : Tm) : Tm :=
  apps (bs.nth k) (as.toList ++ recCalls i C bs as.toList mask)

theorem recCalls_subst (i : Nat) (C bs : Tm) (σ : Nat → Tm) :
    ∀ (as : List Tm) (mask : List Bool),
      (recCalls i C bs as mask).map (·.subst σ) =
        recCalls i (C.subst σ) (bs.subst σ) (as.map (·.subst σ)) mask
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: as, r :: mask => by
      have ih := recCalls_subst i C bs σ as mask
      simp only [recCalls, List.zip_cons_cons, List.filterMap_cons] at ih ⊢
      cases r <;> simp [ih, subst]

theorem iotaRhs_subst (i : Nat) (C : Tm) {bs as : Tm} (hbs : bs.isList = true)
    (has : as.isList = true) (k : Nat) (mask : List Bool) (σ : Nat → Tm) :
    (iotaRhs i C bs k mask as).subst σ =
      iotaRhs i (C.subst σ) (bs.subst σ) k mask (as.subst σ) := by
  simp only [iotaRhs, apps_subst, nth_subst hbs, List.map_append, toList_subst as σ has,
    recCalls_subst]

theorem iotaRhs_ren (i : Nat) (C : Tm) {bs as : Tm} (hbs : bs.isList = true)
    (has : as.isList = true) (k : Nat) (mask : List Bool) (ξ : Nat → Nat) :
    (iotaRhs i C bs k mask as).ren ξ = iotaRhs i (C.ren ξ) (bs.ren ξ) k mask (as.ren ξ) := by
  simp only [ren_eq_subst, iotaRhs_subst i C hbs has]

/-! ## Scoping -/

/-- Every free variable is below `n`. -/
def Scoped : Nat → Tm → Prop
  | n, var i => i < n
  | _, sort _ => True
  | n, pi A B => A.Scoped n ∧ B.Scoped (n + 1)
  | n, lam A t => A.Scoped n ∧ t.Scoped (n + 1)
  | n, app t u => t.Scoped n ∧ u.Scoped n
  | _, ind _ => True
  | n, ctor _ _ _ as => as.Scoped n
  | n, elim _ C bs t => C.Scoped n ∧ bs.Scoped n ∧ t.Scoped n
  | _, tnil => True
  | n, tcons a l => a.Scoped n ∧ l.Scoped n

/-- A substitution that fixes the variables a term mentions fixes the term. -/
theorem subst_scoped : ∀ {t : Tm} {n : Nat} {σ : Nat → Tm}, t.Scoped n →
    (∀ i < n, σ i = var i) → t.subst σ = t
  | var _, _, _, h, hσ => hσ _ h
  | sort _, _, _, _, _ => rfl
  | pi A B, n, σ, ⟨hA, hB⟩, hσ => by
      simp only [subst, subst_scoped hA hσ, subst_scoped (σ := up σ) hB (fun i hi => by
        cases i with
        | zero => rfl
        | succ i => simp only [up_succ, hσ i (by omega)]; rfl)]
  | lam A t, n, σ, ⟨hA, ht⟩, hσ => by
      simp only [subst, subst_scoped hA hσ, subst_scoped (σ := up σ) ht (fun i hi => by
        cases i with
        | zero => rfl
        | succ i => simp only [up_succ, hσ i (by omega)]; rfl)]
  | app t u, _, _, ⟨ht, hu⟩, hσ => by simp only [subst, subst_scoped ht hσ, subst_scoped hu hσ]
  | ind _, _, _, _, _ => rfl
  | ctor _ _ _ as, _, _, h, hσ => by simp only [subst, subst_scoped (t := as) h hσ]
  | elim _ C bs t, _, _, ⟨hC, hb, ht⟩, hσ => by
      simp only [subst, subst_scoped hC hσ, subst_scoped hb hσ, subst_scoped ht hσ]
  | tnil, _, _, _, _ => rfl
  | tcons a l, _, _, ⟨ha, hl⟩, hσ => by simp only [subst, subst_scoped ha hσ, subst_scoped hl hσ]

/-- **A closed term is fixed by every substitution.** -/
theorem subst_closed {t : Tm} (h : t.Scoped 0) (σ : Nat → Tm) : t.subst σ = t :=
  subst_scoped h (fun _ hi => absurd hi (Nat.not_lt_zero _))

/-- …and by every renaming. -/
theorem ren_closed {t : Tm} (h : t.Scoped 0) (ξ : Nat → Nat) : t.ren ξ = t := by
  rw [ren_eq_subst]; exact subst_closed h _

/-! ## Sizes -/

/-- A structural size, every constructor counting one. -/
def size : Tm → Nat
  | var _ => 1
  | sort _ => 1
  | pi A B => A.size + B.size + 1
  | lam A t => A.size + t.size + 1
  | app t u => t.size + u.size + 1
  | ind _ => 1
  | ctor _ _ _ as => as.size + 1
  | elim _ C bs t => C.size + bs.size + t.size + 1
  | tnil => 1
  | tcons a l => a.size + l.size + 1

end Tm

end LambdaLab.Languages.CoIC.DeBruijn
