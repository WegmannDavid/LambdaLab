import LambdaLab.Biparser.Mixfix.Tree

/-!
# Precedence rank — the termination measure

A `Nat` rank for each operator, derived from an entry's well-founded `tighter`
graph (`tighter_wf`): stepping to a strictly-tighter operator strictly decreases
the rank (`Entry.rank_lt`). `Level.base` lifts this to a per-level `Nat`, giving
the measure the deterministic parser will recurse on — `(input.length, base l)`
lexicographic — so a fall-through to a tighter level decreases even when the input
is unchanged.

Ported from the reference `Parser/Mixfix/Parse.lean`; it depends only on `Entry`
and `Level`, not on any parser or leftover representation.
-/

namespace LambdaLab.Biparser.Mixfix

/-- An element of a list is `≤` its `Nat.max`-fold. -/
theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr Nat.max 0 := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-- A `Nat` rank derived from an entry's well-founded `tighter` graph:
`1 + max` of the ranks of the immediately-tighter operators. -/
def Entry.rank {sep : Char → Bool} {Ent : Type} (E : Entry sep Ent) (a : E.Op) : Nat :=
  E.tighter_wf.fix (C := fun _ => Nat)
    (fun a ih => ((E.tighter a).attach.map (fun b => ih b.1 b.2 + 1)).foldr Nat.max 0) a

theorem Entry.rank_eq {sep : Char → Bool} {Ent : Type} (E : Entry sep Ent) (a : E.Op) :
    E.rank a = ((E.tighter a).attach.map (fun b => E.rank b.1 + 1)).foldr Nat.max 0 :=
  WellFounded.fix_eq _ _ _

/-- Stepping to an immediately-tighter operator strictly decreases the rank. -/
theorem Entry.rank_lt {sep : Char → Bool} {Ent : Type} (E : Entry sep Ent) {a b : E.Op}
    (h : b ∈ E.tighter a) : E.rank b < E.rank a := by
  rw [E.rank_eq a]
  have hmem : E.rank b + 1 ∈ (E.tighter a).attach.map (fun c => E.rank c.1 + 1) :=
    List.mem_map.mpr ⟨⟨b, h⟩, List.mem_attach _ _, rfl⟩
  have := le_foldr_max hmem
  omega

/-- Reaching a strictly-tighter operator (transitively) strictly decreases the rank. -/
theorem Entry.rank_lt_of_tighter {sep : Char → Bool} {Ent : Type} (E : Entry sep Ent)
    {a b : E.Op} (h : Tighter E.tighter a b) : E.rank b < E.rank a := by
  induction h with
  | base hmem       => exact E.rank_lt hmem
  | step hmem _ ih  => exact Nat.lt_trans ih (E.rank_lt hmem)

/-- A rank strictly above every `loosest` operator — the base for the `loosest`
level, where the parser starts. -/
def Entry.topRank {sep : Char → Bool} {Ent : Type} (E : Entry sep Ent) : Nat :=
  (E.loosest.map E.rank).foldr Nat.max 0 + 1

theorem Entry.rank_lt_topRank {sep : Char → Bool} {Ent : Type} (E : Entry sep Ent) {r : E.Op}
    (h : r ∈ E.loosest) : E.rank r < E.topRank := by
  have hmem : E.rank r ∈ E.loosest.map E.rank := List.mem_map.mpr ⟨r, h, rfl⟩
  have := le_foldr_max hmem
  unfold Entry.topRank
  omega

/-- The `Nat` measure of a level: the looseness at which the parser is working.
`loosest` sits at `topRank`; an operand level sits at its operator's rank. -/
def Level.base {sep : Char → Bool} {Ent : Type} {E : Entry sep Ent} : Level E → Nat
  | .loosest     => E.topRank
  | .tighter a   => E.rank a
  | .tighterEq a => E.rank a

end LambdaLab.Biparser.Mixfix
