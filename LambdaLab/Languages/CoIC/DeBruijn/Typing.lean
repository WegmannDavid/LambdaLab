import LambdaLab.Languages.CoIC.DeBruijn.Confluence

/-!
# CoC with inductive types — typing

A context lists the types of the free variables, innermost first: `Γ = [A₀, A₁, …]` gives index
`0` the type `A₀` (shifted past its own binder), index `1` the type `A₁`, and so on. The CoC rules
are unchanged (`Languages/CoC/DeBruijn/Typing.lean`); what is new is relative to a **signature**
`sg`, the inductive types declared so far.

## Signatures

An inductive type is a list of constructors, a constructor a list of argument specifications:
`none` for an argument of the type itself, `some A` for an argument of the closed type `A`. So
`Nat` is `[[], [none]]` — `zero` and `succ` — and a binary tree of naturals `[[], [none, some
Nat, none]]`. There are no parameters, and recursion is only ever on the type itself: the types
are first-order.

    i < |sg|                 sg i k = [o₁, …, oₙ]    Γ ⊢ aⱼ : ⟦oⱼ⟧   (⟦none⟧ = Ind i, ⟦some A⟧ = A)
    ─────────────────        ────────────────────────────────────────────────────────────────
    Γ ⊢ Ind i : *                         Γ ⊢ Ctor i k [a₁, …, aₙ] : Ind i

    Γ ⊢ C : *    Γ ⊢ bₖ : ⟦o₁⟧ → … → ⟦oₙ⟧ → C → … → C → C  (one C per recursive argument)
    Γ ⊢ t : Ind i
    ─────────────────────────────────────────────────────────────────────────────────────
                          Γ ⊢ Elim i C [b₁, …, bₘ] t : C

The recursor is non-dependent: it computes a value of a fixed type `C`, by primitive recursion.
Every argument type in a signature is closed (`IndSpec.closed`) — it lives at the top level — so
renaming and substitution never touch it, and the structural lemmas stay unconditional.

## Context validity is a separate judgement

As in CoC: the rules never check the context, and `Wf sg Γ` is a predicate on its own; every
theorem that needs it says so.
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

variable {sg : Sig}

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

/-! ## Signatures -/

/-- A constructor's arguments: `none` for one of the type itself, `some A` for one of the closed
type `A`. -/
abbrev CtorSpec := List (Option Tm)

/-- **An inductive type**: its constructors, every argument type closed. -/
structure IndSpec where
  ctors : List CtorSpec
  closed : ∀ c ∈ ctors, ∀ A, some A ∈ c → A.Scoped 0

/-- **A signature**: the inductive types, by index. -/
abbrev Sig := List IndSpec

/-- The arguments of constructor `k` of inductive `i`. -/
def Sig.ctorArgs (sg : Sig) (i k : Nat) : Option CtorSpec := sg[i]?.bind fun I => I.ctors[k]?

/-- The number of constructors of inductive `i`. -/
def Sig.numCtors (sg : Sig) (i : Nat) : Option Nat := sg[i]?.map fun I => I.ctors.length

/-- The type of an argument: the inductive itself, or the given type. -/
def argTy (i : Nat) : Option Tm → Tm
  | none => .ind i
  | some A => A

/-- How many of a constructor's arguments are recursive. -/
def CtorSpec.recCount (c : CtorSpec) : Nat := (c.filter (·.isNone)).length

/-- The recursion mask of a constructor. -/
def CtorSpec.mask (c : CtorSpec) : List Bool := c.map (·.isNone)

/-- Non-dependent products: `d₁ → … → dₙ → c`, each part read in the outer context. -/
def arrows : List Tm → Tm → Tm
  | [], c => c
  | d :: ds, c => .pi d (arrows ds c).shift

/-- **The type of a recursor branch**: the constructor's arguments, then one result per
recursive argument, to the result. -/
def branchTy (i : Nat) (c : CtorSpec) (C : Tm) : Tm :=
  arrows (c.map (argTy i) ++ List.replicate c.recCount C) C

theorem Sig.ctorArgs_lt {sg : Sig} {i k : Nat} {c : CtorSpec} (h : sg.ctorArgs i k = some c) :
    i < sg.length := by
  simp only [Sig.ctorArgs, Option.bind_eq_some_iff] at h
  obtain ⟨I, hI, _⟩ := h
  exact (List.getElem?_eq_some_iff.mp hI).1

theorem Sig.ctorArgs_closed {sg : Sig} {i k : Nat} {c : CtorSpec} (h : sg.ctorArgs i k = some c) :
    ∀ o ∈ c, (argTy i o).Scoped 0 := by
  simp only [Sig.ctorArgs, Option.bind_eq_some_iff] at h
  obtain ⟨I, _, hk⟩ := h
  intro o ho
  cases o with
  | none => trivial
  | some A => exact I.closed c (List.mem_of_getElem? hk) A ho

theorem arrows_subst : ∀ (ds : List Tm) (c : Tm) (σ : Nat → Tm),
    (arrows ds c).subst σ = arrows (ds.map (·.subst σ)) (c.subst σ)
  | [], _, _ => rfl
  | d :: ds, c, σ => by
      simp only [arrows, Tm.subst, List.map_cons, Tm.shift_subst_up, arrows_subst ds c σ]

theorem arrows_ren (ds : List Tm) (c : Tm) (ξ : Nat → Nat) :
    (arrows ds c).ren ξ = arrows (ds.map (·.ren ξ)) (c.ren ξ) := by
  rw [Tm.ren_eq_subst, arrows_subst]
  congr 1
  · apply List.map_congr_left
    intro e _
    exact (Tm.ren_eq_subst e ξ).symm
  · exact (Tm.ren_eq_subst c ξ).symm

theorem branchTy_subst {sg : Sig} {i k : Nat} {c : CtorSpec} (h : sg.ctorArgs i k = some c)
    (C : Tm) (σ : Nat → Tm) : (branchTy i c C).subst σ = branchTy i c (C.subst σ) := by
  simp only [branchTy, arrows_subst, List.map_append, List.map_map, List.map_replicate]
  congr 2
  apply List.map_congr_left
  intro o ho
  exact Tm.subst_closed (sg.ctorArgs_closed h o ho) σ

theorem branchTy_ren {sg : Sig} {i k : Nat} {c : CtorSpec} (h : sg.ctorArgs i k = some c)
    (C : Tm) (ξ : Nat → Nat) : (branchTy i c C).ren ξ = branchTy i c (C.ren ξ) := by
  rw [Tm.ren_eq_subst, branchTy_subst h, ← Tm.ren_eq_subst]

/-! ## The judgement -/

/-- **`Γ ⊢ t : T`.** -/
inductive HasType (sg : Sig) : Ctx → Tm → Tm → Prop where
  | sort {Γ : Ctx} : HasType sg Γ (.sort .star) (.sort .box)
  | var {Γ : Ctx} {n : Nat} {A : Tm} : Γ.lookup n = some A → HasType sg Γ (.var n) A
  | pi {Γ : Ctx} {A B : Tm} {s₁ s₂ : Srt} :
      HasType sg Γ A (.sort s₁) → HasType sg (A :: Γ) B (.sort s₂) →
      HasType sg Γ (.pi A B) (.sort s₂)
  | lam {Γ : Ctx} {A t B : Tm} {s₁ s₂ : Srt} :
      HasType sg Γ A (.sort s₁) → HasType sg (A :: Γ) t B → HasType sg (A :: Γ) B (.sort s₂) →
      HasType sg Γ (.lam A t) (.pi A B)
  | app {Γ : Ctx} {t u A B : Tm} :
      HasType sg Γ t (.pi A B) → HasType sg Γ u A → HasType sg Γ (.app t u) (B.inst u)
  | conv {Γ : Ctx} {t A B : Tm} {s : Srt} :
      HasType sg Γ t A → HasType sg Γ B (.sort s) → Conv A B → HasType sg Γ t B
  | ind {Γ : Ctx} {i : Nat} : i < sg.length → HasType sg Γ (.ind i) (.sort .star)
  | ctor {Γ : Ctx} {i k : Nat} {mask : List Bool} {as : Tm} {c : CtorSpec} :
      sg.ctorArgs i k = some c → mask = c.mask → as.isList = true → as.toList.length = c.length →
      (∀ j < c.length, HasType sg Γ (as.nth j) (argTy i (c.getD j none))) →
      HasType sg Γ (.ctor i k mask as) (.ind i)
  | elim {Γ : Ctx} {i m : Nat} {C bs t : Tm} :
      sg.numCtors i = some m → HasType sg Γ C (.sort .star) → bs.isList = true →
      bs.toList.length = m →
      (∀ k c, sg.ctorArgs i k = some c → HasType sg Γ (bs.nth k) (branchTy i c C)) →
      (∀ k c, sg.ctorArgs i k = some c → ∀ o ∈ c, HasType sg Γ (argTy i o) (.sort .star)) →
      HasType sg Γ t (.ind i) → HasType sg Γ (.elim i C bs t) C

/-- **A valid context**: every entry is a type in the context before it. -/
def Wf (sg : Sig) : Ctx → Prop
  | [] => True
  | A :: Γ => Wf sg Γ ∧ ∃ s, HasType sg Γ A (.sort s)

@[simp] theorem Wf.nil : Wf sg [] := trivial

theorem Wf.cons {Γ : Ctx} {A : Tm} {s : Srt} (hΓ : Wf sg Γ) (hA : HasType sg Γ A (.sort s)) :
    Wf sg (A :: Γ) :=
  ⟨hΓ, s, hA⟩

/-- The product type of an abstraction is well-sorted. -/
theorem HasType.pi_of_lam {Γ : Ctx} {A B : Tm} {s₁ s₂ : Srt}
    (hA : HasType sg Γ A (.sort s₁)) (hB : HasType sg (A :: Γ) B (.sort s₂)) :
    HasType sg Γ (.pi A B) (.sort s₂) :=
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
theorem HasType.ren {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) :
    ∀ {Δ : Ctx} {ξ : Nat → Nat}, RenOk ξ Γ Δ → HasType sg Δ (t.ren ξ) (T.ren ξ) := by
  induction h with
  | sort => intro Δ ξ _; exact .sort
  | var hn => intro Δ ξ hξ; exact .var (hξ _ _ hn)
  | pi _ _ ihA ihB => intro Δ ξ hξ; exact .pi (ihA hξ) (ihB (hξ.up _))
  | lam _ _ _ ihA iht ihB => intro Δ ξ hξ; exact .lam (ihA hξ) (iht (hξ.up _)) (ihB (hξ.up _))
  | app _ _ iht ihu =>
      intro Δ ξ hξ
      rw [Tm.ren_inst]
      exact .app (iht hξ) (ihu hξ)
  | conv _ _ hc iht ihB => intro Δ ξ hξ; exact .conv (iht hξ) (ihB hξ) (hc.ren ξ)
  | ind hi => intro Δ ξ _; exact .ind hi
  | @ctor Γ i k mask as c hc hm hl hlen _ ih =>
      intro Δ ξ hξ
      refine .ctor hc hm (Tm.isList_ren _ _ hl)
        (by rw [Tm.toList_ren _ _ hl, List.length_map, hlen])
        (fun j hj => ?_)
      have := ih j hj hξ
      rwa [← Tm.nth_ren hl, Tm.ren_closed (sg.ctorArgs_closed hc _ (by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        exact List.getElem_mem hj))] at this
  | @elim Γ i m C bs t hm _ hl hlen _ _ _ ihC ihb iha iht =>
      intro Δ ξ hξ
      refine .elim hm (ihC hξ) (Tm.isList_ren _ _ hl)
        (by rw [Tm.toList_ren _ _ hl, List.length_map, hlen]) (fun k c hc => ?_)
        (fun k c hc o ho => ?_) (iht hξ)
      · have := ihb k c hc hξ
        rwa [← Tm.nth_ren hl, branchTy_ren hc] at this
      · have := iha k c hc o ho hξ
        rwa [Tm.ren_closed (sg.ctorArgs_closed hc o ho)] at this

/-- **Weakening**: a judgement survives a new innermost variable. -/
theorem HasType.weaken {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) (A : Tm) :
    HasType sg (A :: Γ) t.shift T.shift :=
  h.ren (RenOk.shift Γ A)

/-! ## Substitution -/

/-- `σ` sends each of `Γ`'s variables to a term of `Δ` at the substituted type. -/
def SubstOk (sg : Sig) (σ : Nat → Tm) (Γ Δ : Ctx) : Prop :=
  ∀ n A, Γ.lookup n = some A → HasType sg Δ (σ n) (A.subst σ)

theorem SubstOk.up {σ : Nat → Tm} {Γ Δ : Ctx} (h : SubstOk sg σ Γ Δ) (A : Tm) :
    SubstOk sg (Tm.up σ) (A :: Γ) (A.subst σ :: Δ) := by
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
theorem HasType.subst {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) :
    ∀ {Δ : Ctx} {σ : Nat → Tm}, SubstOk sg σ Γ Δ → HasType sg Δ (t.subst σ) (T.subst σ) := by
  induction h with
  | sort => intro Δ σ _; exact .sort
  | var hn => intro Δ σ hσ; exact hσ _ _ hn
  | pi _ _ ihA ihB => intro Δ σ hσ; exact .pi (ihA hσ) (ihB (hσ.up _))
  | lam _ _ _ ihA iht ihB => intro Δ σ hσ; exact .lam (ihA hσ) (iht (hσ.up _)) (ihB (hσ.up _))
  | app _ _ iht ihu =>
      intro Δ σ hσ
      rw [Tm.subst_inst]
      exact .app (iht hσ) (ihu hσ)
  | conv _ _ hc iht ihB => intro Δ σ hσ; exact .conv (iht hσ) (ihB hσ) (hc.subst σ)
  | ind hi => intro Δ σ _; exact .ind hi
  | @ctor Γ i k mask as c hc hm hl hlen _ ih =>
      intro Δ σ hσ
      refine .ctor hc hm (Tm.isList_subst _ _ hl)
        (by rw [Tm.toList_subst _ _ hl, List.length_map, hlen]) (fun j hj => ?_)
      have := ih j hj hσ
      rwa [← Tm.nth_subst hl, Tm.subst_closed (sg.ctorArgs_closed hc _ (by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        exact List.getElem_mem hj))] at this
  | @elim Γ i m C bs t hm _ hl hlen _ _ _ ihC ihb iha iht =>
      intro Δ σ hσ
      refine .elim hm (ihC hσ) (Tm.isList_subst _ _ hl)
        (by rw [Tm.toList_subst _ _ hl, List.length_map, hlen]) (fun k c hc => ?_)
        (fun k c hc o ho => ?_) (iht hσ)
      · have := ihb k c hc hσ
        rwa [← Tm.nth_subst hl, branchTy_subst hc] at this
      · have := iha k c hc o ho hσ
        rwa [Tm.subst_closed (sg.ctorArgs_closed hc o ho)] at this

/-- **Instantiation**: substituting a term of the bound variable's type for it. -/
theorem HasType.inst {Γ : Ctx} {A t T u : Tm} (ht : HasType sg (A :: Γ) t T)
    (hu : HasType sg Γ u A) :
    HasType sg Γ (t.inst u) (T.inst u) := by
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

/-- **Converting the type of the innermost variable** to a convertible one. The old type must be
well-sorted — the variable is converted back to it — the new one need not be. -/
theorem HasType.ctx_conv {Γ : Ctx} {A A' t T : Tm} {s : Srt} (h : HasType sg (A :: Γ) t T)
    (hA : HasType sg Γ A (.sort s)) (hc : Conv A A') :
    HasType sg (A' :: Γ) t T := by
  have := h.subst (σ := Tm.var) (Δ := A' :: Γ) (fun n B hB => ?_)
  · rwa [Tm.subst_var, Tm.subst_var] at this
  cases n with
  | zero =>
      simp only [Ctx.lookup_zero, Option.some.injEq] at hB
      subst hB
      rw [Tm.subst_var]
      exact .conv (.var (by simp)) (hA.weaken A') ((hc.ren Nat.succ).symm)
  | succ n =>
      rw [Tm.subst_var]
      simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at hB
      obtain ⟨C, hC, rfl⟩ := hB
      exact .var (by simp [hC])

/-! ## Valid contexts type their variables -/

theorem Wf.lookup : ∀ {Γ : Ctx}, Wf sg Γ → ∀ {n : Nat} {A : Tm}, Γ.lookup n = some A →
    ∃ s, HasType sg Γ A (.sort s)
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

/-! ## Valid signatures -/

/-- Every inductive type the term mentions is below `n`. -/
def Tm.indsLt (n : Nat) : Tm → Prop
  | .ind i => i < n
  | .ctor i _ _ as => i < n ∧ as.indsLt n
  | .elim i C bs t => i < n ∧ C.indsLt n ∧ bs.indsLt n ∧ t.indsLt n
  | .pi A B => A.indsLt n ∧ B.indsLt n
  | .lam A t => A.indsLt n ∧ t.indsLt n
  | .app t u => t.indsLt n ∧ u.indsLt n
  | .tcons a l => a.indsLt n ∧ l.indsLt n
  | _ => True

/-- **A valid signature**: every argument type is a type, and mentions only inductive types
declared before its own — so a type is never defined through itself except as a direct
recursive argument. -/
def WfSig (sg : Sig) : Prop :=
  ∀ i k c, sg.ctorArgs i k = some c → ∀ A, some A ∈ c →
    HasType sg [] A (.sort .star) ∧ A.indsLt i

/-! ## Closed judgements, arrows and spines -/

/-- A closed judgement holds in every context. -/
theorem HasType.weaken_closed {t T : Tm} (h : HasType sg [] t T) (ht : t.Scoped 0)
    (hT : T.Scoped 0) (Γ : Ctx) : HasType sg Γ t T := by
  have := h.ren (Δ := Γ) (ξ := id) (fun n A hn => by simp [Ctx.lookup] at hn)
  rwa [Tm.ren_closed ht, Tm.ren_closed hT] at this

/-- An argument type of a constructor is a type, in any context. -/
theorem WfSig.argTy {Γ : Ctx} (hsg : WfSig sg) {i k : Nat} {c : CtorSpec}
    (hc : sg.ctorArgs i k = some c) {o : Option Tm} (ho : o ∈ c) :
    HasType sg Γ (argTy i o) (.sort .star) := by
  cases o with
  | none => exact .ind (Sig.ctorArgs_lt hc)
  | some A =>
      exact (hsg i k c hc A ho).1.weaken_closed (sg.ctorArgs_closed hc _ ho) trivial Γ

/-- **Arrows between types are a type.** -/
theorem HasType.arrows_sort : ∀ {Γ : Ctx} {ds : List Tm} {c : Tm},
    (∀ d ∈ ds, HasType sg Γ d (.sort .star)) → HasType sg Γ c (.sort .star) →
    HasType sg Γ (arrows ds c) (.sort .star)
  | _, [], _, _, hc => hc
  | _, d :: ds, _, hd, hc =>
      .pi (hd d (by simp))
        ((HasType.arrows_sort (fun e he => hd e (by simp [he])) hc).weaken d)

/-- Terms typed pointwise by a list of types. -/
inductive TyList (sg : Sig) (Γ : Ctx) : List Tm → List Tm → Prop where
  | nil : TyList sg Γ [] []
  | cons {a d : Tm} {as ds : List Tm} : HasType sg Γ a d → TyList sg Γ as ds →
      TyList sg Γ (a :: as) (d :: ds)

theorem TyList.append {Γ : Ctx} {as ds bs es : List Tm} (h₁ : TyList sg Γ as ds)
    (h₂ : TyList sg Γ bs es) : TyList sg Γ (as ++ bs) (ds ++ es) := by
  induction h₁ with
  | nil => exact h₂
  | cons ha _ ih => exact .cons ha ih

theorem shift_arrows_inst (ds : List Tm) (c a : Tm) : (arrows ds c).shift.inst a = arrows ds c :=
  Tm.shift_inst _ _

/-- **Applying a function of arrow type to arguments of the domains.** -/
theorem HasType.apps {Γ : Ctx} {f c : Tm} {as ds : List Tm} (hf : HasType sg Γ f (arrows ds c))
    (ha : TyList sg Γ as ds) : HasType sg Γ (Tm.apps f as) c := by
  induction ha generalizing f with
  | nil => exact hf
  | cons ha _ ih =>
      have := HasType.app hf ha
      rw [shift_arrows_inst] at this
      exact ih this

end LambdaLab.Languages.CoIC.DeBruijn
