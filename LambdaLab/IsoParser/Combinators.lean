import LambdaLab.IsoParser.Basic
import LambdaLab.NEList

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

/-! ## Helper lemmas -/

variable {fst fol : α → Bool} {v : Type}

/-- Recover the underlying `parse` result from a `run` equation. -/
theorem run_eq_some {p : IsoParser α fst fol v} {input : List α} {a : v} {rest : List α}
    (h : p.run input = some (a, rest)) :
    ∃ r : { r : List α // r.length < input.length }, p.parse input = some (a, r) ∧ r.val = rest := by
  unfold IsoParser.run at h
  rcases hpp : p.parse input with _ | ⟨a', r⟩
  · rw [hpp] at h; simp at h
  · rw [hpp] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨r, rfl, rfl⟩

/-- `parse` fails on empty input (from `run_nil`). -/
theorem parse_nil (p : IsoParser α fst fol v) : p.parse [] = none := by
  have h := p.run_nil; unfold IsoParser.run at h
  rcases hpp : p.parse [] with _ | x
  · rfl
  · rw [hpp] at h; simp at h

/-- A printed value is never empty. -/
theorem print_ne_nil (p : IsoParser α fst fol v) (x : v) : p.print x ≠ [] := by
  intro h
  have hr := p.run_print_nil x
  rw [h, p.run_nil] at hr
  simp at hr

/-- A printed value starts with a FIRST token. -/
theorem print_head_fst (p : IsoParser α fst fol v) (x : v) (c : α) (cs : List α)
    (h : p.print x = c :: cs) : fst c = true := by
  cases hc : fst c with
  | true => rfl
  | false =>
    exfalso
    have hr := p.run_print_nil x
    rw [h] at hr
    unfold IsoParser.run at hr
    rw [p.firstOk c cs hc] at hr
    simp at hr

/-- `print x ++ rest` has a `g`-admissible head, for any `g ⊇ FIRST`. -/
theorem headIn_print_append (p : IsoParser α fst fol v) {g : α → Bool}
    (hg : ∀ c, fst c = true → g c = true) (x : v) (rest : List α) :
    HeadIn g (p.print x ++ rest) := by
  intro a ha
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (print_ne_nil p x)
  rw [hcs, List.cons_append, List.head?_cons, Option.some.injEq] at ha
  subst ha
  exact hg c (print_head_fst p x c cs hcs)

/-! ## `many1` — one or more -/

/-- Parse one-or-more `p`, greedily: keep going until `p` fails. -/
def many1Parse (p : IsoParser α fst fol v) : (input : List α) →
    Option (NEList v × { r : List α // r.length < input.length })
  | input =>
    match p.parse input with
    | none => none
    | some (x, r) =>
      match many1Parse p r.val with
      | none => some (NEList.singleton x, r)
      | some (xs, r2) =>
        some ((x, xs.toList), ⟨r2.val, Nat.lt_trans r2.property r.property⟩)
  termination_by input => input.length
  decreasing_by exact r.property

theorem many1Parse_none {p : IsoParser α fst fol v} {input : List α}
    (h : p.parse input = none) : many1Parse p input = none := by
  rw [many1Parse, h]

theorem many1Parse_cons {p : IsoParser α fst fol v} {input : List α} {x : v}
    {r : { r : List α // r.length < input.length }} (h : p.parse input = some (x, r)) :
    many1Parse p input =
      (match many1Parse p r.val with
        | none => some (NEList.singleton x, r)
        | some (xs, r2) =>
          some ((x, xs.toList), ⟨r2.val, Nat.lt_trans r2.property r.property⟩)) := by
  rw [many1Parse, h]

private theorem and_left_of {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with | true => rfl | false => simp at h

private theorem and_right_of {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with | true => simpa using h | false => simp at h

/-- The printout of a `many1` value: concatenate the elements' printouts. -/
def many1Print (p : IsoParser α fst fol v) : List v → List α
  | [] => []
  | x :: xs => p.print x ++ many1Print p xs

/-- **Round-trip for `many1`.** Parsing a concatenation of ≥1 printouts, followed by a `rest` whose
head is not in FIRST, recovers the elements and leaves `rest`. -/
theorem many1Parse_run (p : IsoParser α fst fol v) (hrep : ∀ c, fst c = true → fol c = true) :
    ∀ (x : v) (xs : List v) (rest : List α),
      HeadIn (fun c => fol c && !fst c) rest →
      (many1Parse p (many1Print p (x :: xs) ++ rest)).map (fun y => (y.1, y.2.val))
        = some ((x, xs), rest) := by
  intro x xs
  induction xs generalizing x with
  | nil =>
    intro rest hr
    rw [show many1Print p (x :: []) ++ rest = p.print x ++ rest by simp [many1Print]]
    have hfol : HeadIn fol rest := fun a ha => and_left_of (hr a ha)
    obtain ⟨r, hpar, hrv⟩ := run_eq_some (p.run_print x rest hfol)
    rw [many1Parse_cons hpar]
    have hstop : p.parse r.val = none := by
      rw [hrv]
      cases rest with
      | nil => exact parse_nil p
      | cons c cs =>
        have hc : fst c = false := by simpa using and_right_of (hr c (by simp))
        exact p.firstOk c cs hc
    rw [many1Parse_none hstop]
    simp [NEList.singleton, hrv]
  | cons y ys ih =>
    intro rest hr
    have hMore : HeadIn fol (many1Print p (y :: ys) ++ rest) := by
      rw [show many1Print p (y :: ys) ++ rest = p.print y ++ (many1Print p ys ++ rest) by
        simp [many1Print, List.append_assoc]]
      exact headIn_print_append p hrep y _
    rw [show many1Print p (x :: y :: ys) ++ rest
          = p.print x ++ (many1Print p (y :: ys) ++ rest) by simp [many1Print, List.append_assoc]]
    obtain ⟨r, hpar, hrv⟩ := run_eq_some (p.run_print x _ hMore)
    rw [many1Parse_cons hpar]
    have ihy := ih y rest hr
    rw [← hrv] at ihy
    rcases hM : many1Parse p r.val with _ | ⟨xs', r2⟩
    · rw [hM] at ihy; simp at ihy
    · rw [hM] at ihy
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ihy
      obtain ⟨rfl, hr2⟩ := ihy
      simp [NEList.toList, hr2]

/-- **Exactness for `many1`.** Whatever it parsed, `many1Print` reproduces. -/
theorem many1Parse_exact (p : IsoParser α fst fol v) :
    ∀ (n : Nat) (input : List α), input.length = n →
      ∀ (xs : NEList v) (r : { r : List α // r.length < input.length }),
        many1Parse p input = some (xs, r) → many1Print p xs.toList ++ r.val = input := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro input hn xs r hpar
    rcases hp : p.parse input with _ | ⟨x, r0⟩
    · rw [many1Parse_none hp] at hpar; simp at hpar
    · rw [many1Parse_cons hp] at hpar
      rcases hM : many1Parse p r0.val with _ | ⟨xs', r2⟩
      · rw [hM] at hpar
        simp only [Option.some.injEq, Prod.mk.injEq] at hpar
        obtain ⟨rfl, rfl⟩ := hpar
        rw [show many1Print p (NEList.singleton x).toList = p.print x by
          simp [NEList.singleton, NEList.toList, many1Print]]
        exact p.print_parse input x r0 hp
      · rw [hM] at hpar
        simp only [Option.some.injEq, Prod.mk.injEq] at hpar
        obtain ⟨rfl, rfl⟩ := hpar
        have hr0 : many1Print p xs'.toList ++ r2.val = r0.val :=
          ih r0.val.length (hn ▸ r0.property) r0.val rfl xs' r2 hM
        show p.print x ++ many1Print p xs'.toList ++ r2.val = input
        rw [List.append_assoc, hr0]
        exact p.print_parse input x r0 hp

/-- **One-or-more `p`.** FIRST is unchanged; FOLLOW forbids starting another element
(`fol && !fst`). `hrep : FIRST ⊆ FOLLOW` — an element's own output may follow it. -/
def many1 (p : IsoParser α fst fol v) (hrep : ∀ c, fst c = true → fol c = true) :
    IsoParser α fst (fun c => fol c && !fst c) (NEList v) where
  parse := many1Parse p
  print xs := many1Print p xs.toList
  firstOk c rest hc := many1Parse_none (p.firstOk c rest hc)
  parse_print xs rest hr := by
    obtain ⟨x, tail⟩ := xs
    exact many1Parse_run p hrep x tail rest hr
  print_parse input xs r h := many1Parse_exact p input.length input rfl xs r h

/-! ## `seq` — sequencing, and `imap` — an isomorphism on values -/

/-- Parse `p` then `q` on the leftover. -/
def seqParse {f1 fo1 f2 fo2 : α → Bool} {a b : Type}
    (p : IsoParser α f1 fo1 a) (q : IsoParser α f2 fo2 b) : (input : List α) →
    Option ((a × b) × { r : List α // r.length < input.length })
  | input =>
    match p.parse input with
    | none => none
    | some (x, r1) =>
      match q.parse r1.val with
      | none => none
      | some (y, r2) => some ((x, y), ⟨r2.val, Nat.lt_trans r2.property r1.property⟩)

/-- **Sequence two parsers.** Seam: `q`'s FIRST is in `p`'s FOLLOW, so `p` stops where `q` begins.
FIRST is `p`'s; FOLLOW is `q`'s. -/
def seq {f1 fo1 f2 fo2 : α → Bool} {a b : Type}
    (p : IsoParser α f1 fo1 a) (q : IsoParser α f2 fo2 b)
    (hseam : ∀ c, f2 c = true → fo1 c = true) :
    IsoParser α f1 fo2 (a × b) where
  parse := seqParse p q
  print := fun ab => p.print ab.1 ++ q.print ab.2
  firstOk c rest hc := by simp [seqParse, p.firstOk c rest hc]
  parse_print ab rest hr := by
    obtain ⟨x, y⟩ := ab
    have h1 : HeadIn fo1 (q.print y ++ rest) := headIn_print_append q hseam y rest
    obtain ⟨r1, hp1, hv1⟩ := run_eq_some (p.run_print x (q.print y ++ rest) h1)
    have hq : q.run r1.val = some (y, rest) := by rw [hv1]; exact q.run_print y rest hr
    obtain ⟨r2, hp2, hv2⟩ := run_eq_some hq
    rw [show p.print (x, y).1 ++ q.print (x, y).2 ++ rest
          = p.print x ++ (q.print y ++ rest) from by simp [List.append_assoc]]
    simp only [seqParse, hp1, hp2, Option.map_some]
    simp [hv2]
  print_parse input ab r h := by
    obtain ⟨x, y⟩ := ab
    simp only [seqParse] at h
    split at h
    · simp at h
    · next x' r1 hp1 =>
      split at h
      · simp at h
      · next y' r2 hp2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        have e1 := p.print_parse input x' r1 hp1
        have e2 := q.print_parse r1.val y' r2 hp2
        show p.print x' ++ q.print y' ++ r2.val = input
        rw [List.append_assoc, e2, e1]

/-- **Relabel the value along an isomorphism** `f`/`g`. FIRST and FOLLOW are unchanged. -/
def imap {a b : Type} (f : a → b) (g : b → a)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    (p : IsoParser α fst fol a) : IsoParser α fst fol b where
  parse input := (p.parse input).map (fun z => (f z.1, z.2))
  print y := p.print (g y)
  firstOk c rest hc := by simp [p.firstOk c rest hc]
  parse_print y rest hr := by
    obtain ⟨r, hp, hv⟩ := run_eq_some (p.run_print (g y) rest hr)
    simp [hp, hfg, hv]
  print_parse input y r h := by
    rcases hp : p.parse input with _ | ⟨x, r'⟩
    · rw [hp] at h; simp at h
    · rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [show g (f x) = x from hgf x]
      exact p.print_parse input x r' hp

end LambdaLab.IsoParser
