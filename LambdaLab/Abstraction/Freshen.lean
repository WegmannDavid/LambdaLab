import LambdaLab.Abstraction.Basic

/-!
# Freshening — `_` becomes a fresh metavariable, as a morphism of `Abs`

`List α ⇝ blank-free List α`. The lossy map replaces every blank token (`_`) with a freshly
indexed metavariable token (`?n`); what it forgets — *which* mvar tokens the source elided —
goes in the annotation. This is the `annotated | infer` split that `Stlc/Named/Pipeline.lean`
promised itself: `_` cannot join the lossless core because it does not determine an index, so it
lives one stage above it, where the elision is annotation rather than value.

The stage had to be a morphism, not a preprocessor: anything that forgets outside the tower
falsifies `parseFile_complete` — a file written with `_` would be accepted but no annotation
could realize back to it. Inside the tower, both laws are one-liners.

## The target is the image, as always

The abstract carrier is `{ ts // blank ∉ ts }`, not `List α`. A blank-containing stream is not
something freshening produces, so its fiber is empty and `default` — which must inhabit every
fiber — would be unsatisfiable on the full carrier. Same decision, same reason, as
`Stages/Evaluate.lean`'s `Evaluated`. The successor stage, stated on the full carrier, plugs in
through `Abstraction.restrict` — its printer never emits a blank, which is exactly the
obligation `restrict` asks for.

## The annotation is the fiber, as elaboration's is

Which elision sets are legal is delicate — re-eliding `?5 ?6 ?7` at `?7` alone re-freshens to
`?5 ?6 ?7`, but at `?6` alone re-freshens to `?5 ?8 ?7` — only *top segments* of the index range
qualify, and enumerating them buys nothing. The fiber `{ input // freshenList input = ts }` is
the honest family: the annotation is the source as written, blanks and all, and the laws are
`rfl`-adjacent for the reason `elabStage`'s and `evalStage`'s are.

## Freshness is semantic, not lawful

No structure law forces the new indices past the written ones — any deterministic replacement
satisfies all four fields. Freshness is what makes the stage *mean* "infer this": a `_` that
collided with a written `?n` would silently share its solution. `lt_startIdx` is that statement,
kept as a theorem beside the morphism rather than smuggled into it.

Like evaluation, the stage never rejects: `abstract` is `some` unconditionally.
-/

set_option autoImplicit false

namespace LambdaLab.Abstraction

variable {α : Type}

/-- The lexical interface of holes: a blank token, an indexed metavariable spelling, and the
partial inverse that recognizes one. `idx` doubles as the recognizer (`none` = not an mvar
token), which is why two laws suffice: the spelling is faithful, and the blank is not a
spelling. -/
structure HoleSyntax (α : Type) where
  /-- The hole the user writes: `_`. -/
  blank : α
  /-- The spelling of metavariable `n`: `?n`. -/
  mkMvar : Nat → α
  /-- Recognize an mvar token and read its index. -/
  idx : α → Option Nat
  /-- The spelling is faithful. -/
  idx_mkMvar : ∀ n, idx (mkMvar n) = some n
  /-- The blank is not an mvar spelling. -/
  idx_blank : idx blank = none

namespace HoleSyntax

variable (H : HoleSyntax α)

/-- A spelled metavariable is never the blank — `idx` tells them apart. -/
theorem mkMvar_ne_blank (n : Nat) : H.mkMvar n ≠ H.blank := fun h => by
  have hn := H.idx_mkMvar n
  rw [h, H.idx_blank] at hn
  simp at hn

/-- The first index past every mvar written in `ts` — where freshening starts counting. -/
def startIdx : List α → Nat
  | [] => 0
  | t :: ts =>
      match H.idx t with
      | some n => max (n + 1) (startIdx ts)
      | none => startIdx ts

/-- **Freshness**: every index written in `ts` lies below `startIdx ts`, so the indices
freshening hands out collide with nothing the user wrote. -/
theorem lt_startIdx : ∀ {ts : List α} {t : α}, t ∈ ts → ∀ {n : Nat}, H.idx t = some n →
    n < H.startIdx ts
  | t' :: ts, t, ht, n, hn => by
    rw [startIdx]
    cases List.mem_cons.mp ht with
    | inl h =>
        subst h
        rw [hn]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_max_left _ _)
    | inr h =>
        have ih := lt_startIdx h hn
        cases hidx : H.idx t' with
        | none => exact ih
        | some m => exact Nat.lt_of_lt_of_le ih (Nat.le_max_right _ _)

variable [DecidableEq α]

/-- Replace each blank with the next index, counting up from `k`. -/
def replaceBlanks : List α → Nat → List α
  | [], _ => []
  | t :: ts, k =>
      if t = H.blank then H.mkMvar k :: replaceBlanks ts (k + 1)
      else t :: replaceBlanks ts k

/-- A blank-free stream is untouched, whatever the counter. -/
theorem replaceBlanks_of_not_mem : ∀ {ts : List α}, H.blank ∉ ts → ∀ (k : Nat),
    H.replaceBlanks ts k = ts
  | [], _, _ => rfl
  | t :: ts, h, k => by
    have hne : t ≠ H.blank := fun ht => h (List.mem_cons.mpr (Or.inl ht.symm))
    have hts : H.blank ∉ ts := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [replaceBlanks, if_neg hne, replaceBlanks_of_not_mem hts k]

/-- The output is blank-free: blanks are replaced, and their replacements are not blanks. -/
theorem blank_not_mem_replaceBlanks : ∀ (ts : List α) (k : Nat),
    H.blank ∉ H.replaceBlanks ts k
  | [], _ => by simp [replaceBlanks]
  | t :: ts, k => by
    rw [replaceBlanks]
    split
    · intro hm
      cases List.mem_cons.mp hm with
      | inl h => exact H.mkMvar_ne_blank k h.symm
      | inr h => exact blank_not_mem_replaceBlanks ts (k + 1) h
    · next hne =>
        intro hm
        cases List.mem_cons.mp hm with
        | inl h => exact hne h.symm
        | inr h => exact blank_not_mem_replaceBlanks ts k h

/-- Freshen a stream: replace each blank, counting up from past everything written. -/
def freshenList (ts : List α) : List α :=
  H.replaceBlanks ts (H.startIdx ts)

theorem freshenList_of_not_mem {ts : List α} (h : H.blank ∉ ts) : H.freshenList ts = ts :=
  H.replaceBlanks_of_not_mem h _

theorem blank_not_mem_freshenList (ts : List α) : H.blank ∉ H.freshenList ts :=
  H.blank_not_mem_replaceBlanks ts _

/-- **Freshening as an `Abs` morphism** `List α ⇝ blank-free List α`: `abstract` numbers the
blanks (total — this stage never rejects), the annotation over an output is the fiber — the
source as written, blanks and all — and `default` is the blank-free output itself, its own
spelling. -/
def freshen : Abstraction (List α) { ts : List α // H.blank ∉ ts }
    (fun ts => { input : List α // H.freshenList input = ts.val }) where
  abstract input := some ⟨H.freshenList input, H.blank_not_mem_freshenList input⟩
  realize ann := ann.val
  default {ts} := ⟨ts.val, H.freshenList_of_not_mem ts.property⟩
  abstract_realize _ ann := congrArg some (Subtype.ext ann.property)
  complete input _ts h := ⟨⟨input, congrArg Subtype.val (Option.some.inj h)⟩, rfl⟩

end HoleSyntax

end LambdaLab.Abstraction
