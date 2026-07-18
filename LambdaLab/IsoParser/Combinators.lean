import LambdaLab.IsoParser.Basic

/-!
# `IsoParser` combinators

Leaves and combinators for building isomorphic parsers. FOLLOW is carried in the index, so a
combinator's seam is a condition on the FIRST/FOLLOW predicates, never on parsed values.

Parse functions are named top-level defs (not anonymous structure fields) so their equation lemmas
drive `simp`/`split` in the law proofs.
-/

namespace LambdaLab.IsoParser

variable {α : Type}

/-! ## `sat` — one token satisfying a predicate -/

/-- Parse one token satisfying `pred`. -/
def satParse (pred : α → Bool) : (input : List α) →
    Option ({ a : α // pred a = true } × { r : List α // r.length < input.length })
  | [] => none
  | hd :: tl => if h : pred hd then some (⟨hd, h⟩, ⟨tl, by simp⟩) else none

/-- **One token satisfying `pred`.** FIRST is `pred`; FOLLOW is `⊤` — it consumes exactly one token,
so any continuation is admissible. The value carries its membership proof, so a value outside the
class is unrepresentable. -/
def sat (pred : α → Bool) :
    IsoParser α pred (fun _ => true) { a : α // pred a = true } where
  parse := satParse pred
  print a := [a.val]
  firstOk c rest hc := by simp [satParse, hc]
  parse_print a rest _ := by simp [satParse, a.property]
  print_parse input a r h := by
    cases input with
    | nil => simp [satParse] at h
    | cons hd tl =>
      simp only [satParse] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rfl
      · simp at h

/-! ## `tok` — a literal token -/

/-- Parse a literal token `t`. -/
def tokParse [DecidableEq α] (t : α) : (input : List α) →
    Option (Unit × { r : List α // r.length < input.length })
  | [] => none
  | hd :: tl => if hd = t then some ((), ⟨tl, by simp⟩) else none

/-- **A literal token `t`.** Carries no information: value `Unit`, printed `[t]`. FIRST `(· = t)`,
FOLLOW `⊤`. -/
def tok [DecidableEq α] (t : α) :
    IsoParser α (fun c => decide (c = t)) (fun _ => true) Unit where
  parse := tokParse t
  print _ := [t]
  firstOk c rest hc := by
    have : ¬ c = t := by simpa using hc
    simp [tokParse, this]
  parse_print _ rest _ := by simp [tokParse]
  print_parse input a r h := by
    cases input with
    | nil => simp [tokParse] at h
    | cons hd tl =>
      simp only [tokParse] at h
      split at h
      · rename_i hp
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; subst hp; rfl
      · simp at h

end LambdaLab.IsoParser
