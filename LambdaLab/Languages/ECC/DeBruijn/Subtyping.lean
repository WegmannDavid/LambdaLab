import LambdaLab.Languages.ECC.DeBruijn.Confluence

/-!
# ECC — the sorts, and cumulativity

## The sorts

`Prop : Type 0 : Type 1 : …` (`Srt.succ`). A product lives in `Prop` whenever its codomain does,
whatever its domain — that is the impredicativity of `Prop` — and otherwise in the larger of the
two universes (`Srt.pi`), `Prop` counting as level `0`.

## Cumulativity

The universes are **cumulative**: `Prop ≤ Type 0 ≤ Type 1 ≤ …` (`Srt.le`), and a type in a
smaller universe is a type in every larger one. Typing therefore compares types not by conversion
but by **subtyping** `A ≼ B` (`Sub`): `A` and `B` reduce to terms that are equal except that sorts
may grow in covariant positions — at the top, and in the codomain of a product (`Leq`). The
domain of a product is compared by conversion, as in Luo's ECC.

`Leq` is a simulation for reduction in both directions (`Leq.red_left`, `Leq.red_right`), so by
confluence `Sub` is transitive (`Sub.trans`), and like conversion it cannot confuse rigid shapes:
products compare componentwise (`Sub.pi_inv`), and sorts by their order (`Sub.sort_inv`).
Conversion is the special case `Leq = Eq` (`Conv.toSub`).
-/

namespace LambdaLab.Languages.ECC.DeBruijn

open LambdaLab (RTC)

/-! ## The sorts -/

/-- The universe a sort is a member of: `Prop : Type 0`, `Type i : Type (i + 1)`. -/
def Srt.succ : Srt → Srt
  | .prop => .type 0
  | .type i => .type (i + 1)

/-- A sort's level, `Prop` counting as `0`. -/
def Srt.lvl : Srt → Nat
  | .prop => 0
  | .type i => i

/-- **The sort of a product** with domain in `s₁` and codomain in `s₂`: `Prop` if the codomain
is a proposition, otherwise the larger universe. -/
def Srt.pi (s₁ : Srt) : Srt → Srt
  | .prop => .prop
  | .type j => .type (max s₁.lvl j)

/-- **Cumulativity of the sorts**: `Prop ≤ Type 0 ≤ Type 1 ≤ …`. -/
def Srt.le : Srt → Srt → Prop
  | .prop, _ => True
  | .type _, .prop => False
  | .type i, .type j => i ≤ j

instance : DecidableRel Srt.le
  | .prop, _ => isTrue trivial
  | .type _, .prop => isFalse id
  | .type i, .type j => inferInstanceAs (Decidable (i ≤ j))

theorem Srt.le_refl : ∀ s : Srt, s.le s
  | .prop => trivial
  | .type i => Nat.le_refl i

theorem Srt.le_trans : ∀ {a b c : Srt}, a.le b → b.le c → a.le c
  | .prop, _, _, _, _ => trivial
  | .type _, .prop, _, h, _ => h.elim
  | .type _, .type _, .prop, _, h => h.elim
  | .type _, .type _, .type _, h₁, h₂ => Nat.le_trans h₁ h₂

theorem Srt.le_succ : ∀ s : Srt, s.le s.succ
  | .prop => trivial
  | .type i => Nat.le_succ i

theorem Srt.succ_mono : ∀ {a b : Srt}, a.le b → a.succ.le b.succ
  | .prop, .prop, _ => Nat.le_refl 0
  | .prop, .type _, _ => Nat.zero_le _
  | .type _, .prop, h => h.elim
  | .type _, .type _, h => Nat.succ_le_succ h

theorem Srt.pi_mono {a a' b b' : Srt} (ha : a.le a') (hb : b.le b') : (a.pi b).le (a'.pi b') := by
  have hl : a.lvl ≤ a'.lvl := by
    cases a <;> cases a' <;> simp_all [Srt.lvl, Srt.le]
  cases b with
  | prop => trivial
  | type j =>
      cases b' with
      | prop => exact hb.elim
      | type j' =>
          show max _ _ ≤ max _ _
          have : j ≤ j' := hb
          omega

/-- A domain's sort is below its product's, unless the product is a proposition. -/
theorem Srt.le_pi_left {a : Srt} : ∀ {b : Srt}, b ≠ .prop → a.le (a.pi b)
  | .prop, h => absurd rfl h
  | .type j, _ => by
      cases a with
      | prop => trivial
      | type i => exact Nat.le_max_left i j

theorem Srt.le_pi_right (a : Srt) : ∀ b : Srt, b.le (a.pi b)
  | .prop => trivial
  | .type j => Nat.le_max_right _ j

/-! ## Syntactic cumulativity -/

/-- **Syntactic cumulativity**: equal terms, except that a sort may grow in a covariant position —
the whole term, or a product's codomain. -/
inductive Leq : Tm → Tm → Prop where
  | refl (t : Tm) : Leq t t
  | sort {s s' : Srt} : s.le s' → Leq (.sort s) (.sort s')
  | pi {A B B' : Tm} : Leq B B' → Leq (.pi A B) (.pi A B')

theorem Leq.trans {a b c : Tm} (h₁ : Leq a b) (h₂ : Leq b c) : Leq a c := by
  induction h₁ generalizing c with
  | refl => exact h₂
  | sort hs =>
      cases h₂ with
      | refl => exact .sort hs
      | sort hs' => exact .sort (Srt.le_trans hs hs')
  | pi _ ih =>
      cases h₂ with
      | refl => exact .pi (ih (.refl _))
      | pi h => exact .pi (ih h)

theorem Leq.subst {a b : Tm} (h : Leq a b) : ∀ σ : Nat → Tm, Leq (a.subst σ) (b.subst σ) := by
  induction h with
  | refl => intro σ; exact .refl _
  | sort hs => intro σ; exact .sort hs
  | pi _ ih => intro σ; exact .pi (ih _)

theorem Leq.ren {a b : Tm} (h : Leq a b) (ξ : Nat → Nat) : Leq (a.ren ξ) (b.ren ξ) := by
  rw [Tm.ren_eq_subst, Tm.ren_eq_subst]; exact h.subst _

/-- A step on the left is matched on the right. -/
theorem Leq.step_left {a b a' : Tm} (h : Leq a b) (hs : Step a a') :
    ∃ b', Step b b' ∧ Leq a' b' := by
  induction h generalizing a' with
  | refl => exact ⟨a', hs, .refl _⟩
  | sort => cases hs
  | pi _ ih =>
      cases hs with
      | piA h => exact ⟨_, .piA h, .pi (by assumption)⟩
      | piB h =>
          obtain ⟨b', hb, hl⟩ := ih h
          exact ⟨_, .piB hb, .pi hl⟩

/-- A step on the right is matched on the left. -/
theorem Leq.step_right {a b b' : Tm} (h : Leq a b) (hs : Step b b') :
    ∃ a', Step a a' ∧ Leq a' b' := by
  induction h generalizing b' with
  | refl => exact ⟨b', hs, .refl _⟩
  | sort => cases hs
  | pi _ ih =>
      cases hs with
      | piA h => exact ⟨_, .piA h, .pi (by assumption)⟩
      | piB h =>
          obtain ⟨a', ha, hl⟩ := ih h
          exact ⟨_, .piB ha, .pi hl⟩

theorem Leq.red_left {a b a' : Tm} (h : Leq a b) (hr : Red a a') :
    ∃ b', Red b b' ∧ Leq a' b' := by
  induction hr with
  | refl => exact ⟨b, .refl, h⟩
  | tail _ hs ih =>
      obtain ⟨b₁, hb₁, hl⟩ := ih
      obtain ⟨b₂, hb₂, hl'⟩ := hl.step_left hs
      exact ⟨b₂, hb₁.tail hb₂, hl'⟩

theorem Leq.red_right {a b b' : Tm} (h : Leq a b) (hr : Red b b') :
    ∃ a', Red a a' ∧ Leq a' b' := by
  induction hr with
  | refl => exact ⟨a, .refl, h⟩
  | tail _ hs ih =>
      obtain ⟨a₁, ha₁, hl⟩ := ih
      obtain ⟨a₂, ha₂, hl'⟩ := hl.step_right hs
      exact ⟨a₂, ha₁.tail ha₂, hl'⟩

/-! ## Subtyping -/

/-- **`A ≼ B`**: `A` and `B` reduce to syntactically cumulative terms. -/
def Sub (A B : Tm) : Prop := ∃ A' B', Red A A' ∧ Red B B' ∧ Leq A' B'

theorem Conv.toSub {A B : Tm} (h : Conv A B) : Sub A B :=
  let ⟨c, h1, h2⟩ := h
  ⟨c, c, h1, h2, .refl _⟩

theorem Sub.refl (A : Tm) : Sub A A := (Conv.refl A).toSub

/-- **Subtyping is transitive**, by confluence. -/
theorem Sub.trans {A B C : Tm} (h₁ : Sub A B) (h₂ : Sub B C) : Sub A C := by
  obtain ⟨A₁, B₁, hA, hB, hl⟩ := h₁
  obtain ⟨B₂, C₁, hB', hC, hl'⟩ := h₂
  obtain ⟨B₃, h13, h23⟩ := Red.confluent hB hB'
  obtain ⟨A₃, hA₃, hlA⟩ := hl.red_right h13
  obtain ⟨C₃, hC₃, hlC⟩ := hl'.red_left h23
  exact ⟨A₃, C₃, RTC.trans hA hA₃, RTC.trans hC hC₃, hlA.trans hlC⟩

theorem Sub.subst {A B : Tm} (h : Sub A B) (σ : Nat → Tm) : Sub (A.subst σ) (B.subst σ) :=
  let ⟨_, _, hA, hB, hl⟩ := h
  ⟨_, _, hA.subst σ, hB.subst σ, hl.subst σ⟩

theorem Sub.ren {A B : Tm} (h : Sub A B) (ξ : Nat → Nat) : Sub (A.ren ξ) (B.ren ξ) :=
  let ⟨_, _, hA, hB, hl⟩ := h
  ⟨_, _, hA.ren ξ, hB.ren ξ, hl.ren ξ⟩

theorem Sub.conv_left {A A' B : Tm} (hc : Conv A A') (h : Sub A' B) : Sub A B :=
  hc.toSub.trans h

theorem Sub.conv_right {A B B' : Tm} (h : Sub A B) (hc : Conv B B') : Sub A B' :=
  h.trans hc.toSub

theorem Sub.sort {s s' : Srt} (h : s.le s') : Sub (.sort s) (.sort s') :=
  ⟨_, _, .refl, .refl, .sort h⟩

theorem Sub.pi {A A' B B' : Tm} (hA : Conv A A') (hB : Sub B B') : Sub (.pi A B) (.pi A' B') := by
  obtain ⟨C, hAC, hA'C⟩ := hA
  obtain ⟨B₁, B₁', hB₁, hB₁', hl⟩ := hB
  exact ⟨.pi C B₁, .pi C B₁', Red.pi hAC hB₁, Red.pi hA'C hB₁', .pi hl⟩

/-- A term cumulative with a sort is a sort below it. -/
theorem Leq.to_sort {a : Tm} {s : Srt} (h : Leq a (.sort s)) : ∃ s', a = .sort s' ∧ s'.le s := by
  cases h with
  | refl => exact ⟨s, rfl, Srt.le_refl s⟩
  | sort hs => exact ⟨_, rfl, hs⟩

/-- A term a sort is cumulative with is a sort above it. -/
theorem Leq.of_sort {b : Tm} {s : Srt} (h : Leq (.sort s) b) : ∃ s', b = .sort s' ∧ s.le s' := by
  cases h with
  | refl => exact ⟨s, rfl, Srt.le_refl s⟩
  | sort hs => exact ⟨_, rfl, hs⟩

/-- A term cumulative with a product is a product with the same domain. -/
theorem Leq.to_pi {a A B : Tm} (h : Leq a (.pi A B)) : ∃ B₀, a = .pi A B₀ ∧ Leq B₀ B := by
  cases h with
  | refl => exact ⟨B, rfl, .refl _⟩
  | pi h => exact ⟨_, rfl, h⟩

theorem Leq.of_pi {b A B : Tm} (h : Leq (.pi A B) b) : ∃ B₁, b = .pi A B₁ ∧ Leq B B₁ := by
  cases h with
  | refl => exact ⟨B, rfl, .refl _⟩
  | pi h => exact ⟨_, rfl, h⟩

/-- **Sorts compare by their order.** -/
theorem Sub.sort_inv {s s' : Srt} (h : Sub (.sort s) (.sort s')) : s.le s' := by
  obtain ⟨a, b, ha, hb, hl⟩ := h
  rw [Red.sort_inv ha, Red.sort_inv hb] at hl
  obtain ⟨_, e, hs⟩ := hl.of_sort
  cases e
  exact hs

/-- **Products compare componentwise**: domains by conversion, codomains by subtyping. -/
theorem Sub.pi_inv {A A' B B' : Tm} (h : Sub (.pi A B) (.pi A' B')) : Conv A A' ∧ Sub B B' := by
  obtain ⟨a, b, ha, hb, hl⟩ := h
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Red.pi_inv ha
  obtain ⟨A₂, B₂, rfl, hA₂, hB₂⟩ := Red.pi_inv hb
  obtain ⟨_, e, hl'⟩ := hl.of_pi
  cases e
  exact ⟨⟨_, hA₁, hA₂⟩, ⟨_, _, hB₁, hB₂, hl'⟩⟩

theorem Sub.sort_pi {s : Srt} {A B : Tm} : ¬ Sub (.sort s) (.pi A B) := by
  rintro ⟨a, b, ha, hb, hl⟩
  rw [Red.sort_inv ha] at hl
  obtain ⟨_, _, rfl, _, _⟩ := Red.pi_inv hb
  obtain ⟨_, e, _⟩ := hl.of_sort
  cases e

theorem Sub.pi_sort {s : Srt} {A B : Tm} : ¬ Sub (.pi A B) (.sort s) := by
  rintro ⟨a, b, ha, hb, hl⟩
  rw [Red.sort_inv hb] at hl
  obtain ⟨_, _, rfl, _, _⟩ := Red.pi_inv ha
  obtain ⟨_, e, _⟩ := hl.to_sort
  cases e

/-- Whatever is below a sort reduces to a smaller sort. -/
theorem Sub.to_sort {T : Tm} {s : Srt} (h : Sub T (.sort s)) : ∃ s', Red T (.sort s') ∧ s'.le s := by
  obtain ⟨a, b, ha, hb, hl⟩ := h
  rw [Red.sort_inv hb] at hl
  obtain ⟨s', rfl, hs⟩ := hl.to_sort
  exact ⟨s', ha, hs⟩

/-- Whatever is below a product reduces to a product. -/
theorem Sub.to_pi {T A B : Tm} (h : Sub T (.pi A B)) :
    ∃ A₀ B₀, Red T (.pi A₀ B₀) ∧ Conv A₀ A ∧ Sub B₀ B := by
  obtain ⟨a, b, ha, hb, hl⟩ := h
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Red.pi_inv hb
  obtain ⟨B₀, rfl, hl'⟩ := hl.to_pi
  exact ⟨A₁, B₀, ha, ⟨A₁, .refl, hA₁⟩, ⟨B₀, B₁, .refl, hB₁, hl'⟩⟩

end LambdaLab.Languages.ECC.DeBruijn
