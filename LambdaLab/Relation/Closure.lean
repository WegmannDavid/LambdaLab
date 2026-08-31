/-!
# Closures of a relation

`RTC r` is the reflexive-transitive closure of `r`, `TC r` the transitive one. Three
developments in this repository need one of them — full-beta multi-step reduction in both
STLC variants (`Stlc/DeBruijn/Step/MStep.lean`, `Stlc/Named/Step/MStep.lean`) and the mixfix
precedence order (`Parser/IsoParser/Mixfix/Basic.lean`) — and before this file each rolled
its own.

## Why not `Mathlib.Logic.Relation`

Mathlib has exactly these, as `Relation.ReflTransGen` / `Relation.TransGen`, with a far
larger API, and using them was measured. It is not affordable here: all three call sites are
inside the `stlc`/`arith` executables' import cone, and `Mathlib.Logic.Relation` transitively
imports `Mathlib.Init`, which pulls in `Lean.Linter.Sets`, `ImportGraph.Tools` and
`Batteries.Tactic.Lint` — i.e. the Lean elaborator and tactic frontend. Only 57 Mathlib
modules end up in the closure, but linking them took `stlc` from 4.9 MB to 154 MB (113.7 MB
stripped), and invalidated the premise `.github/workflows/publish.yml` is built on, that
nothing in the executables' cone imports Mathlib. Neither call site can be moved out of that
cone: `MStep` arrives through the `Preservation` field of `LawfulTypeSystem`, which is a
field precisely so it cannot be skipped, and `Tighter` is the parser's own precedence order.

The definitions below therefore deliberately mirror Mathlib's names and constructor shapes,
so that a call site reads the same either way and switching back is a change of prefix.

## `tail` vs `head`

The constructors are snoc-shaped (`refl`/`tail`), as in Mathlib. Most proofs about a closure
map over the chain and do not care about orientation, so they go by the default recursion.
For the ones that genuinely consume a step from the front there is `head_induction_on`, and
for a one-step-from-the-front case split, `cases_head`.

Note that `a` is a *parameter* of `RTC`, not an index: only the right endpoint varies under
the default recursion. That is what lets a hypothesis about the left endpoint stay in scope
during an induction instead of having to be reverted into the motive.
-/

universe u

namespace LambdaLab

variable {α : Type u} {r : α → α → Prop} {a b c : α}

/-- Reflexive-transitive closure of `r`. -/
inductive RTC {α : Type u} (r : α → α → Prop) (a : α) : α → Prop where
  | refl : RTC r a a
  | tail {b c : α} : RTC r a b → r b c → RTC r a c

attribute [refl] RTC.refl

/-- Transitive closure of `r`: one or more steps. -/
inductive TC {α : Type u} (r : α → α → Prop) (a : α) : α → Prop where
  | single {b : α} : r a b → TC r a b
  | tail {b c : α} : TC r a b → r b c → TC r a c

/-! ## `RTC` -/

theorem RTC.single (h : r a b) : RTC r a b := RTC.refl.tail h

theorem RTC.head (hab : r a b) (hbc : RTC r b c) : RTC r a c := by
  induction hbc with
  | refl => exact RTC.refl.tail hab
  | tail _ hcd ih => exact ih.tail hcd

theorem RTC.trans (hab : RTC r a b) (hbc : RTC r b c) : RTC r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ h ih => exact ih.tail h

/-- Induction consuming a step from the *front* of the chain, with the right endpoint `b`
fixed and the left endpoint varying. The counterpart of the `head` constructor the bespoke
closures this file replaced used to have. -/
@[elab_as_elim]
theorem RTC.head_induction_on {b : α} {motive : ∀ a : α, RTC r a b → Prop} {a : α}
    (h : RTC r a b) (refl : motive b RTC.refl)
    (head : ∀ {a c : α} (h' : r a c) (h : RTC r c b), motive c h → motive a (h.head h')) :
    motive a h := by
  induction h with
  | refl => exact refl
  | @tail b c _ hbc ih =>
      apply ih
      · exact head hbc _ refl
      · exact fun h1 h2 => head h1 (h2.tail hbc)

/-- Split a chain on its *first* step. -/
theorem RTC.cases_head (h : RTC r a b) : a = b ∨ ∃ c, r a c ∧ RTC r c b := by
  induction h using RTC.head_induction_on with
  | refl => exact Or.inl rfl
  | head h' hrest _ => exact Or.inr ⟨_, h', hrest⟩

/-! ## `TC`, and the two closures against each other -/

theorem TC.toRTC (h : TC r a b) : RTC r a b := by
  induction h with
  | single h => exact RTC.single h
  | tail _ hbc ih => exact ih.tail hbc

theorem TC.transLeft (hab : TC r a b) (hbc : RTC r b c) : TC r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hcd ih => exact ih.tail hcd

theorem TC.head (hab : r a b) (hbc : TC r b c) : TC r a c :=
  TC.transLeft (TC.single hab) hbc.toRTC

/-- A reflexive-transitive chain is either trivial or a genuinely transitive one. -/
theorem RTC.eq_or_tc (h : RTC r a b) : a = b ∨ TC r a b := by
  induction h using RTC.head_induction_on with
  | refl => exact Or.inl rfl
  | head h' _ ih =>
      cases ih with
      | inl heq => exact Or.inr (heq ▸ TC.single h')
      | inr ht => exact Or.inr (TC.head h' ht)

/-- One step into a chain that continues reflexive-transitively is a strict chain. -/
theorem TC.ofMemRTC (hab : r a b) (h : RTC r b c) : TC r a c :=
  TC.transLeft (TC.single hab) h

/-- A reflexive-transitive chain followed by a strict one is strict. The mirror of
`TC.transLeft`. -/
theorem TC.ofRTC (hab : RTC r a b) (hbc : TC r b c) : TC r a c := by
  induction hab using RTC.head_induction_on with
  | refl => exact hbc
  | head h' _ ih => exact TC.head h' ih

/-- A strict chain, viewed from the front: one real step, then anything. -/
theorem TC.head_iff : TC r a b ↔ ∃ c, r a c ∧ RTC r c b := by
  constructor
  · intro h
    induction h with
    | single h => exact ⟨_, h, RTC.refl⟩
    | tail _ hbc ih =>
        obtain ⟨d, had, hdb⟩ := ih
        exact ⟨d, had, hdb.tail hbc⟩
  · rintro ⟨d, had, hdb⟩
    exact TC.ofMemRTC had hdb

/-- Induction consuming a step from the front of a strict chain. -/
@[elab_as_elim]
theorem TC.head_induction_on {b : α} {motive : ∀ a : α, TC r a b → Prop} {a : α} (h : TC r a b)
    (single : ∀ {a : α} (h : r a b), motive a (TC.single h))
    (head : ∀ {a c : α} (h' : r a c) (h : TC r c b), motive c h → motive a (h.head h')) :
    motive a h := by
  induction h with
  | single h => exact single h
  | @tail b c _ hbc ih =>
      apply ih
      · exact fun h => head h (TC.single hbc) (single hbc)
      · exact fun hab hbc => head hab _

end LambdaLab
