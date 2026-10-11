import LambdaLab.Languages.CoIC.DeBruijn.Preservation

/-!
# CoC — kinds, constructors, objects

A well-typed term of CoC lives at exactly one of three levels:

* a **kind** is typed by `□` — `*`, or a product ending in `*` (`Π A . *`, `Π X : * . * → *`);
* a **constructor** is typed by a kind — types (`Π x : A . B : *`) and type operators;
* an **object** is typed by a type.

The strong normalization proof (`Normalization.lean`) interprets the first two semantically and
must know, of every subterm, which level it is at. That is decided **syntactically** here and
proved to agree with typing.

## Kinds

`Tm.isKind` recognizes a product spine ending in `*`. For a well-typed term it is exactly "typed by
`□`" (`HasType.isKind_iff`), and a sorted term is a kind exactly when its sort is `□`
(`HasType.sort_box_iff`). So it is stable under well-typed reduction (`HasType.isKind_step`).

## Skeletons

A kind's **skeleton** (`Tm.skel`) forgets everything but its higher-order shape: products over
types disappear, products over kinds become arrows. `Π X : * . Π x : X . *` has skeleton `* ⇒ *`.
These are the kinds of Fω, and the semantic interpretation of a constructor will be a function of
the shape its kind's skeleton says. Skeletons too are stable under well-typed reduction
(`HasType.skel_step`) — reductions inside a kind happen in its types, which the skeleton forgets,
or in its sub-kinds — so convertible kinds have equal skeletons (`HasType.kind_conv`).

## Classes

`cls ρ t` computes, from the class `ρ n` of each free variable (the skeleton of its kind, or
`none` for an object variable), the class of `t`: its kind's skeleton if it is a constructor,
`none` if it is an object. On a well-typed term it is what typing says (`HasType.cls_eq`).
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

/-! ## Skeletons: the kinds of Fω -/

/-- A kind's shape: `*`, or an arrow between shapes. -/
inductive SK where
  | star
  | arr : SK → SK → SK
  deriving DecidableEq, Repr

namespace Tm

/-- Is this a kind: a product spine ending in `*`? -/
def isKind : Tm → Bool
  | sort .star => true
  | pi _ B => B.isKind
  | _ => false

/-- **The skeleton of a kind**: products over kinds become arrows, products over types vanish.
Anything that is not a kind has skeleton `*`. -/
def skel : Tm → SK
  | pi A B => if B.isKind then (if A.isKind then .arr A.skel B.skel else B.skel) else .star
  | _ => .star

theorem skel_of_not_isKind : ∀ {t : Tm}, t.isKind = false → t.skel = .star
  | var _, _ => rfl
  | sort _, _ => rfl
  | pi A B, h => by simp only [isKind] at h; simp [skel, h]
  | lam _ _, _ => rfl
  | app _ _, _ => rfl

theorem isKind_ren : ∀ (t : Tm) (ξ : Nat → Nat), (t.ren ξ).isKind = t.isKind
  | var _, _ => rfl
  | sort _, _ => rfl
  | pi _ B, ξ => by simp only [ren, isKind, isKind_ren B]
  | lam _ _, _ => rfl
  | app _ _, _ => rfl

theorem skel_ren : ∀ (t : Tm) (ξ : Nat → Nat), (t.ren ξ).skel = t.skel
  | var _, _ => rfl
  | sort _, _ => rfl
  | pi A B, ξ => by simp only [ren, skel, isKind_ren, skel_ren A, skel_ren B]
  | lam _ _, _ => rfl
  | app _ _, _ => rfl

theorem isKind_subst {σ : Nat → Tm} (hσ : ∀ n, (σ n).isKind = false) :
    ∀ t : Tm, (t.subst σ).isKind = t.isKind
  | var n => hσ n
  | sort _ => rfl
  | pi _ B => by
      simp only [subst, isKind]
      exact isKind_subst (σ := up σ) (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp only [up_succ, isKind_ren, hσ n]) B
  | lam _ _ => rfl
  | app _ _ => rfl

theorem up_not_kind {σ : Nat → Tm} (hσ : ∀ n, (σ n).isKind = false) :
    ∀ n, (up σ n).isKind = false
  | 0 => rfl
  | n + 1 => by simp only [up_succ, isKind_ren, hσ n]

theorem skel_subst {σ : Nat → Tm} (hσ : ∀ n, (σ n).isKind = false) :
    ∀ t : Tm, (t.subst σ).skel = t.skel
  | var n => by simp only [subst, skel_of_not_isKind (hσ n)]; rfl
  | sort _ => rfl
  | pi A B => by
      simp only [subst, skel, isKind_subst hσ, isKind_subst (up_not_kind hσ), skel_subst hσ A,
        skel_subst (up_not_kind hσ) B]
  | lam _ _ => rfl
  | app _ _ => rfl

theorem scons_not_kind {u : Tm} (hu : u.isKind = false) : ∀ n, (scons u var n).isKind = false
  | 0 => hu
  | _ + 1 => rfl

end Tm

/-! ## Kinds are what `□` types -/

/-- A kind's only types are `□`. -/
theorem HasType.box_of_isKind {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hk : t.isKind = true) : T = .sort .box := by
  induction h with
  | sort => rfl
  | var => simp [Tm.isKind] at hk
  | @pi Γ A B s₁ s₂ hA _ _ ihB =>
      simp only [Tm.isKind] at hk
      exact ihB (hΓ.cons hA) hk
  | lam => simp [Tm.isKind] at hk
  | app => simp [Tm.isKind] at hk
  | conv _ hB hc iht _ =>
      rw [iht hΓ hk] at hc
      exact (hB.conv_box_eq hΓ hc).elim

/-- What `□` types is a kind. -/
theorem HasType.isKind_of_box {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hT : T = .sort .box) : t.isKind = true := by
  induction h with
  | sort => rfl
  | var hn =>
      subst hT
      obtain ⟨s, hs⟩ := hΓ.lookup hn
      exact (hs.ne_box rfl).elim
  | @pi Γ A B s₁ s₂ hA _ _ ihB =>
      cases hT
      exact ihB (hΓ.cons hA) rfl
  | lam => cases hT
  | app ht hu _ _ =>
      obtain ⟨s, hs⟩ := ht.inst_sorted hu hΓ
      rw [hT] at hs
      exact (hs.ne_box rfl).elim
  | conv _ hB _ _ _ =>
      subst hT
      exact (hB.ne_box rfl).elim

/-- **For a well-typed term, being a kind is being typed by `□`.** -/
theorem HasType.isKind_iff {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ) :
    t.isKind = true ↔ T = .sort .box :=
  ⟨h.box_of_isKind hΓ, h.isKind_of_box hΓ⟩

/-- A sorted term is a kind exactly when its sort is `□`. -/
theorem HasType.sort_box_iff {Γ : Ctx} {T : Tm} {s : Srt} (h : HasType Γ T (.sort s))
    (hΓ : Wf Γ) : s = .box ↔ T.isKind = true := by
  rw [h.isKind_iff hΓ]
  exact ⟨fun h => by rw [h], fun h => by cases h; rfl⟩

/-- A term whose type is not `□` is not a kind. -/
theorem HasType.not_kind {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hT : T ≠ .sort .box) : t.isKind = false := by
  cases hk : t.isKind with
  | false => rfl
  | true => exact (hT (h.box_of_isKind hΓ hk)).elim

/-- A term typed by a sorted type is not a kind. -/
theorem HasType.not_kind_of_sorted {Γ : Ctx} {t T : Tm} {s : Srt} (h : HasType Γ t T)
    (hT : HasType Γ T (.sort s)) (hΓ : Wf Γ) : t.isKind = false :=
  h.not_kind hΓ (fun e => hT.ne_box e)

/-- A well-typed substitution substitutes no kind. -/
theorem SubstOk.not_kind {σ : Nat → Tm} {Γ Δ : Ctx} (hσ : SubstOk σ Γ Δ) (hΓ : Wf Γ)
    (hΔ : Wf Δ) {n : Nat} {A : Tm} (hn : Γ.lookup n = some A) : (σ n).isKind = false := by
  obtain ⟨s, hs⟩ := hΓ.lookup hn
  exact (hσ n A hn).not_kind_of_sorted (hs.subst hσ) hΔ

/-! ## Stability under reduction and conversion -/

/-- **Being a kind is stable under well-typed reduction.** -/
theorem HasType.isKind_step {Γ : Ctx} {t t' T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hs : Step t t') : t'.isKind = t.isKind := by
  have h' := h.preservation hΓ hs
  cases hk : t.isKind with
  | true => exact (h'.isKind_iff hΓ).mpr ((h.isKind_iff hΓ).mp hk)
  | false =>
      cases hk' : t'.isKind with
      | false => rfl
      | true =>
          rw [(h'.isKind_iff hΓ).mp hk'] at h
          rw [h.isKind_of_box hΓ rfl] at hk
          cases hk

/-- **A kind's skeleton is stable under well-typed reduction.** -/
theorem HasType.skel_step {Γ : Ctx} {K K' : Tm} (h : HasType Γ K (.sort .box)) (hΓ : Wf Γ)
    (hs : Step K K') : K'.skel = K.skel := by
  induction hs generalizing Γ with
  | @piA A A' B hA ihA =>
      obtain ⟨s₁, s₂, hA₁, hB, hc⟩ := h.gen_pi
      have hk := hA₁.isKind_step hΓ hA
      simp only [Tm.skel, hk]
      cases hAk : A.isKind with
      | false => rfl
      | true =>
          have hs₁ := (hA₁.sort_box_iff hΓ).mpr hAk
          subst hs₁
          rw [ihA hA₁ hΓ]
  | @piB A B B' hB ihB =>
      obtain ⟨s₁, s₂, hA₁, hB₂, hc⟩ := h.gen_pi
      have hs₂ := Conv.sort_inj hc
      subst hs₂
      have hΓ' := hΓ.cons hA₁
      have hk := hB₂.isKind_step hΓ' hB
      simp only [Tm.skel, hk, ihB hB₂ hΓ']
  | beta => exact absurd (h.isKind_of_box hΓ rfl) (by simp [Tm.isKind])
  | appL => exact absurd (h.isKind_of_box hΓ rfl) (by simp [Tm.isKind])
  | appR => exact absurd (h.isKind_of_box hΓ rfl) (by simp [Tm.isKind])
  | lamA => exact absurd (h.isKind_of_box hΓ rfl) (by simp [Tm.isKind])
  | lamB => exact absurd (h.isKind_of_box hΓ rfl) (by simp [Tm.isKind])

theorem HasType.isKind_red {Γ : Ctx} {t t' T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hr : Red t t') : t'.isKind = t.isKind := by
  induction hr with
  | refl => rfl
  | tail hr hs ih => exact ((h.preservation_red hΓ hr).isKind_step hΓ hs).trans ih

theorem HasType.skel_red {Γ : Ctx} {K K' : Tm} (h : HasType Γ K (.sort .box)) (hΓ : Wf Γ)
    (hr : Red K K') : K'.skel = K.skel := by
  induction hr with
  | refl => rfl
  | tail hr hs ih => exact ((h.preservation_red hΓ hr).skel_step hΓ hs).trans ih

/-- **Convertible sorted terms have the same sort, and — if kinds — the same skeleton.** -/
theorem HasType.kind_conv {Γ : Ctx} {A B : Tm} {s s' : Srt} (hA : HasType Γ A (.sort s))
    (hB : HasType Γ B (.sort s')) (hΓ : Wf Γ) (hc : Conv A B) :
    s = s' ∧ (s = .box → A.skel = B.skel) := by
  obtain ⟨C, hAC, hBC⟩ := hc
  have hk : A.isKind = B.isKind := (hA.isKind_red hΓ hAC).symm.trans (hB.isKind_red hΓ hBC)
  have hss : s = s' := by
    cases s <;> cases s'
    · rfl
    · have := (hB.sort_box_iff hΓ).mp rfl
      rw [← hk, ← (hA.sort_box_iff hΓ)] at this
      cases this
    · have := (hA.sort_box_iff hΓ).mp rfl
      rw [hk, ← (hB.sort_box_iff hΓ)] at this
      cases this
    · rfl
  subst hss
  refine ⟨rfl, fun hbox => ?_⟩
  subst hbox
  exact (hA.skel_red hΓ hAC).symm.trans (hB.skel_red hΓ hBC)

/-! ## Classes -/

/-- The class of each variable of a context: its kind's skeleton for a constructor variable,
`none` for an object variable. -/
def Ctx.shape (Γ : Ctx) (n : Nat) : Option SK :=
  match Γ.lookup n with
  | some A => if A.isKind then some A.skel else none
  | none => none

/-- The class of a type, as the variable it is the type of would have it. -/
def Tm.cls₀ (A : Tm) : Option SK := if A.isKind then some A.skel else none

theorem Ctx.shape_cons (A : Tm) (Γ : Ctx) : Ctx.shape (A :: Γ) = scons A.cls₀ Γ.shape := by
  funext n
  cases n with
  | zero => simp [Ctx.shape, Tm.cls₀, Tm.isKind_ren, Tm.skel_ren]
  | succ n =>
      simp only [Ctx.shape, Ctx.lookup_succ, scons_succ]
      cases Γ.lookup n <;> simp [Tm.isKind_ren, Tm.skel_ren]

/-- **The class of a term**, from the classes of its free variables. -/
def cls (ρ : Nat → Option SK) : Tm → Option SK
  | .var n => ρ n
  | .sort _ => none
  | .pi _ _ => some .star
  | .lam A t =>
      if A.isKind then (cls (scons (some A.skel) ρ) t).map (.arr A.skel) else cls (scons none ρ) t
  | .app t u =>
      match cls ρ u with
      | some _ =>
          match cls ρ t with
          | some (.arr _ b) => some b
          | _ => none
      | none => cls ρ t

theorem cls_ren : ∀ (t : Tm) (ρ : Nat → Option SK) (ξ : Nat → Nat),
    cls ρ (t.ren ξ) = cls (ρ ∘ ξ) t
  | .var _, _, _ => rfl
  | .sort _, _, _ => rfl
  | .pi _ _, _, _ => rfl
  | .lam A t, ρ, ξ => by
      have e : ∀ x : Option SK, scons x ρ ∘ upRen ξ = scons x (ρ ∘ ξ) := fun x => by
        funext n; cases n <;> rfl
      simp only [cls, Tm.ren, Tm.isKind_ren, Tm.skel_ren, cls_ren t, e]
  | .app t u, ρ, ξ => by simp only [cls, Tm.ren, cls_ren t, cls_ren u]

/-- **On a well-typed term the class is what typing says**: the skeleton of its kind for a
constructor, `none` for an object. -/
theorem HasType.cls_eq {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hT : T ≠ .sort .box) : cls Γ.shape t = T.cls₀ := by
  induction h with
  | sort => exact (hT rfl).elim
  | var hn => simp [cls, Ctx.shape, hn, Tm.cls₀]
  | @pi Γ A B s₁ s₂ _ _ _ _ =>
      cases s₂ with
      | star => rfl
      | box => exact (hT rfl).elim
  | @lam Γ A t B s₁ s₂ hA _ hB _ iht _ =>
      have ht := iht (hΓ.cons hA) (fun e => hB.ne_box e)
      rw [Ctx.shape_cons] at ht
      simp only [cls, Tm.cls₀, Tm.isKind, Tm.skel] at ht ⊢
      cases hAk : A.isKind <;> cases hBk : B.isKind <;> simp_all [Tm.cls₀]
  | @app Γ t u A B ht hu iht ihu =>
      obtain ⟨s, hs⟩ := (ht.correct hΓ).resolve_left (by intro e; cases e)
      obtain ⟨s₁, s₂, hA, hB, _⟩ := hs.gen_pi
      have hu' := ihu hΓ (fun e => hA.ne_box e)
      have ht' := iht hΓ (fun e => by cases e)
      have huk : u.isKind = false := hu.not_kind_of_sorted hA hΓ
      simp only [cls, hu', ht', Tm.cls₀, Tm.isKind, Tm.skel, Tm.inst,
        Tm.isKind_subst (Tm.scons_not_kind huk), Tm.skel_subst (Tm.scons_not_kind huk)]
      cases hAk : A.isKind <;> cases hBk : B.isKind <;> simp
  | @conv Γ t A B s ht hB hc iht _ =>
      have hA : A ≠ .sort .box := fun e => by subst e; exact hB.conv_box_eq hΓ hc
      rw [iht hΓ hA]
      obtain ⟨s', hs'⟩ := (ht.correct hΓ).resolve_left hA
      obtain ⟨hss, hsk⟩ := hs'.kind_conv hB hΓ hc
      subst hss
      have hk : A.isKind = B.isKind := by
        cases s' with
        | box => rw [(hs'.sort_box_iff hΓ).mp rfl, (hB.sort_box_iff hΓ).mp rfl]
        | star =>
            rw [hs'.not_kind_of_sorted .sort hΓ, hB.not_kind_of_sorted .sort hΓ]
      simp only [Tm.cls₀, hk]
      cases hBk : B.isKind with
      | false => rfl
      | true =>
          have : s' = .box := (hB.sort_box_iff hΓ).mpr hBk
          rw [hsk this]

end LambdaLab.Languages.CoIC.DeBruijn
