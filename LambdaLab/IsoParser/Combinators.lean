import LambdaLab.IsoParser.Basic
import LambdaLab.NEList

/-!
# `IsoParser` combinators (annotation-carrying)

Each combinator builds the value **and** the annotation family. No-choice leaves (`sat`, `tok`) have
`Ann = fun _ => PUnit`; `ws` collects a whitespace gap; `seq` pairs annotations; `many1` collects a
dependent list of them.
-/

namespace LambdaLab.IsoParser

variable {α : Type}

/-! ## `sat` / `tok` — no-choice leaves -/

/-- Parse one token satisfying `pred`. -/
def satParse (pred : α → Bool) : (input : List α) →
    Option ((Σ _ : { a : α // pred a = true }, PUnit) × { r : List α // r.length < input.length })
  | [] => none
  | hd :: tl => if h : pred hd then some (⟨⟨hd, h⟩, PUnit.unit⟩, ⟨tl, by simp⟩) else none

/-- **One token satisfying `pred`.** No choice, so `Ann = PUnit`. FIRST = `pred`, FOLLOW = `⊤`. -/
def sat (pred : α → Bool) :
    IsoParser α pred (fun _ => true) { a : α // pred a = true } (fun _ => PUnit) where
  parse := satParse pred
  print a _ := [a.val]
  firstOk c rest hc := by simp [satParse, hc]
  parse_print x u rest _ := by obtain ⟨⟩ := u; simp [satParse, x.property]
  print_parse input xa r h := by
    cases input with
    | nil => simp [satParse] at h
    | cons hd tl =>
      simp only [satParse] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rfl
      · simp at h

/-- Parse a literal token `t`. -/
def tokParse [DecidableEq α] (t : α) : (input : List α) →
    Option ((Σ _ : Unit, PUnit) × { r : List α // r.length < input.length })
  | [] => none
  | hd :: tl => if hd = t then some (⟨(), PUnit.unit⟩, ⟨tl, by simp⟩) else none

/-- **A literal token `t`.** Value `Unit`, `Ann = PUnit`. FIRST `(· = t)`, FOLLOW `⊤`. -/
def tok [DecidableEq α] (t : α) :
    IsoParser α (fun c => decide (c = t)) (fun _ => true) Unit (fun _ => PUnit) where
  parse := tokParse t
  print _ _ := [t]
  firstOk c rest hc := by
    have : ¬ c = t := by simpa using hc
    simp [tokParse, this]
  parse_print x u rest _ := by obtain ⟨⟩ := u; obtain ⟨⟩ := x; simp [tokParse]
  print_parse input xa r h := by
    obtain ⟨⟨⟩, ⟨⟩⟩ := xa
    cases input with
    | nil => simp [tokParse] at h
    | cons hd tl =>
      simp only [tokParse] at h
      split at h
      · rename_i hp
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        subst hp; rfl
      · simp at h

/-! ## Helper lemmas -/

variable {fst fol : α → Bool} {v : Type} {Ann : v → Type}

/-- Recover the underlying `parse` result from a `run` equation. -/
theorem run_eq_some {p : IsoParser α fst fol v Ann} {input : List α}
    {xa : Σ x : v, Ann x} {rest : List α} (h : p.run input = some (xa, rest)) :
    ∃ r : { r : List α // r.length < input.length }, p.parse input = some (xa, r) ∧ r.val = rest := by
  unfold IsoParser.run at h
  rcases hpp : p.parse input with _ | ⟨xa', r⟩
  · rw [hpp] at h; simp at h
  · rw [hpp] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨r, rfl, rfl⟩

/-- `parse` fails on empty input. -/
theorem parse_nil (p : IsoParser α fst fol v Ann) : p.parse [] = none := by
  have h := p.run_nil; unfold IsoParser.run at h
  rcases hpp : p.parse [] with _ | x
  · rfl
  · rw [hpp] at h; simp at h

/-- A printed value is never empty. -/
theorem print_ne_nil (p : IsoParser α fst fol v Ann) (x : v) (a : Ann x) :
    p.print x a ≠ [] := by
  intro h
  have hr := p.run_print_nil x a
  rw [h, p.run_nil] at hr
  simp at hr

/-- A printed value starts with a FIRST token. -/
theorem print_head_fst (p : IsoParser α fst fol v Ann) (x : v) (a : Ann x)
    (c : α) (cs : List α) (h : p.print x a = c :: cs) : fst c = true := by
  cases hc : fst c with
  | true => rfl
  | false =>
    exfalso
    have hr := p.run_print_nil x a
    rw [h] at hr
    unfold IsoParser.run at hr
    rw [p.firstOk c cs hc] at hr
    simp at hr

/-- `print x a ++ rest` has a `g`-admissible head, for any `g ⊇ FIRST`. -/
theorem headIn_print_append (p : IsoParser α fst fol v Ann) {g : α → Bool}
    (hg : ∀ c, fst c = true → g c = true) (x : v) (a : Ann x) (rest : List α) :
    HeadIn g (p.print x a ++ rest) := by
  intro d hd
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (print_ne_nil p x a)
  rw [hcs, List.cons_append, List.head?_cons, Option.some.injEq] at hd
  subst hd
  exact hg c (print_head_fst p x a c cs hcs)

private theorem and_left_of {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with | true => rfl | false => simp at h

private theorem and_right_of {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with | true => simpa using h | false => simp at h

/-! ## `seq` — sequencing, pairing annotations -/

/-- Parse `p` then `q`. -/
def seqParse {f1 fo1 f2 fo2 : α → Bool} {a b : Type} {Aa : a → Type} {Ab : b → Type}
    (p : IsoParser α f1 fo1 a Aa) (q : IsoParser α f2 fo2 b Ab) : (input : List α) →
    Option ((Σ xy : a × b, Aa xy.1 × Ab xy.2) × { r : List α // r.length < input.length })
  | input =>
    match p.parse input with
    | none => none
    | some (sx, r1) =>
      match q.parse r1.val with
      | none => none
      | some (sy, r2) =>
        some (⟨(sx.1, sy.1), (sx.2, sy.2)⟩, ⟨r2.val, Nat.lt_trans r2.property r1.property⟩)

/-- **Sequence two parsers**, pairing their annotations. Seam `FIRST(q) ⊆ FOLLOW(p)`. -/
def seq {f1 fo1 f2 fo2 : α → Bool} {a b : Type} {Aa : a → Type} {Ab : b → Type}
    (p : IsoParser α f1 fo1 a Aa) (q : IsoParser α f2 fo2 b Ab)
    (hseam : ∀ c, f2 c = true → fo1 c = true) :
    IsoParser α f1 fo2 (a × b) (fun xy => Aa xy.1 × Ab xy.2) where
  parse := seqParse p q
  print xy axy := p.print xy.1 axy.1 ++ q.print xy.2 axy.2
  firstOk c rest hc := by simp [seqParse, p.firstOk c rest hc]
  parse_print xy axy rest hr := by
    obtain ⟨x, y⟩ := xy
    obtain ⟨ax, ay⟩ := axy
    have h1 : HeadIn fo1 (q.print y ay ++ rest) := headIn_print_append q hseam y ay rest
    obtain ⟨r1, hp1, hv1⟩ := run_eq_some (p.run_print x ax (q.print y ay ++ rest) h1)
    have hq : q.run r1.val = some (⟨y, ay⟩, rest) := by rw [hv1]; exact q.run_print y ay rest hr
    obtain ⟨r2, hp2, hv2⟩ := run_eq_some hq
    rw [show p.print (x, y).1 (ax, ay).1 ++ q.print (x, y).2 (ax, ay).2 ++ rest
          = p.print x ax ++ (q.print y ay ++ rest) from by simp [List.append_assoc]]
    simp only [seqParse, hp1, hp2, Option.map_some]
    simp [hv2]
  print_parse input xab r h := by
    simp only [seqParse] at h
    split at h
    · simp at h
    · next sx r1 hp1 =>
      split at h
      · simp at h
      · next sy r2 hp2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hxab, rfl⟩ := h
        subst hxab
        have e1 := p.print_parse input sx r1 hp1
        have e2 := q.print_parse r1.val sy r2 hp2
        show p.print sx.1 sx.2 ++ q.print sy.1 sy.2 ++ r2.val = input
        rw [List.append_assoc, e2, e1]

/-! ## `many1` — one or more, collecting a list of annotations -/

/-- The annotation of a `many1` value: one element-annotation per element. -/
def ManyAnn {v : Type} (Ann : v → Type) : List v → Type
  | [] => PUnit
  | x :: xs => Ann x × ManyAnn Ann xs

/-- Print a list of values with their annotations. -/
def many1Print (p : IsoParser α fst fol v Ann) :
    (l : List v) → ManyAnn Ann l → List α
  | [], _ => []
  | x :: xs, a => p.print x a.1 ++ many1Print p xs a.2

/-- Parse one-or-more `p`, greedily, collecting values and annotations. -/
def many1Parse (p : IsoParser α fst fol v Ann) : (input : List α) →
    Option ((Σ nel : NEList v, ManyAnn Ann nel.toList) × { r : List α // r.length < input.length })
  | input =>
    match p.parse input with
    | none => none
    | some (sx, r) =>
      match many1Parse p r.val with
      | none => some (⟨(sx.1, []), (sx.2, PUnit.unit)⟩, r)
      | some (snel, r2) =>
        some (⟨(sx.1, snel.1.toList), (sx.2, snel.2)⟩,
              ⟨r2.val, Nat.lt_trans r2.property r.property⟩)
  termination_by input => input.length
  decreasing_by exact r.property

theorem many1Parse_none {p : IsoParser α fst fol v Ann} {input : List α}
    (h : p.parse input = none) : many1Parse p input = none := by
  rw [many1Parse, h]

theorem many1Parse_cons {p : IsoParser α fst fol v Ann} {input : List α}
    {sx : Σ x : v, Ann x} {r : { r : List α // r.length < input.length }}
    (h : p.parse input = some (sx, r)) :
    many1Parse p input =
      (match many1Parse p r.val with
        | none => some (⟨(sx.1, []), (sx.2, PUnit.unit)⟩, r)
        | some (snel, r2) =>
          some (⟨(sx.1, snel.1.toList), (sx.2, snel.2)⟩,
                ⟨r2.val, Nat.lt_trans r2.property r.property⟩)) := by
  rw [many1Parse, h]

/-- **Round-trip for `many1`.** -/
theorem many1Parse_run (p : IsoParser α fst fol v Ann)
    (hrep : ∀ c, fst c = true → fol c = true) :
    ∀ (x : v) (xs : List v) (a : ManyAnn Ann (x :: xs)) (rest : List α),
      HeadIn (fun c => fol c && !fst c) rest →
      (many1Parse p (many1Print p (x :: xs) a ++ rest)).map (fun z => (z.1, z.2.val))
        = some (⟨(x, xs), a⟩, rest) := by
  intro x xs
  induction xs generalizing x with
  | nil =>
    intro a rest hr
    obtain ⟨a1, ⟨⟩⟩ := a
    have hfol : HeadIn fol rest := fun c hc => and_left_of (hr c hc)
    rw [show many1Print p (x :: []) (a1, PUnit.unit) = p.print x a1 by simp [many1Print]]
    obtain ⟨r, hpar, hrv⟩ := run_eq_some (p.run_print x a1 rest hfol)
    rw [many1Parse_cons hpar]
    have hstop : p.parse r.val = none := by
      rw [hrv]
      cases rest with
      | nil => exact parse_nil p
      | cons c cs => exact p.firstOk c cs (by simpa using and_right_of (hr c (by simp)))
    rw [many1Parse_none hstop]
    simp [hrv]
  | cons y ys ih =>
    intro a rest hr
    obtain ⟨a1, arest⟩ := a
    have hMore : HeadIn fol (many1Print p (y :: ys) arest ++ rest) := by
      rw [show many1Print p (y :: ys) arest ++ rest
            = p.print y arest.1 ++ (many1Print p ys arest.2 ++ rest) by
          simp [many1Print, List.append_assoc]]
      exact headIn_print_append p hrep y arest.1 _
    rw [show many1Print p (x :: y :: ys) (a1, arest) ++ rest
          = p.print x a1 ++ (many1Print p (y :: ys) arest ++ rest) by
        simp [many1Print, List.append_assoc]]
    obtain ⟨r, hpar, hrv⟩ := run_eq_some (p.run_print x a1 _ hMore)
    rw [many1Parse_cons hpar]
    have ihy := ih y arest rest hr
    rw [← hrv] at ihy
    rcases hM : many1Parse p r.val with _ | ⟨snel, r2⟩
    · rw [hM] at ihy; simp at ihy
    · rw [hM] at ihy
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ihy
      obtain ⟨hsnel, hr2⟩ := ihy
      subst hsnel
      simp [NEList.toList, hr2]

/-- **Exactness for `many1`.** -/
theorem many1Parse_exact (p : IsoParser α fst fol v Ann) :
    ∀ (n : Nat) (input : List α), input.length = n →
      ∀ (snel : Σ nel : NEList v, ManyAnn Ann nel.toList)
        (r : { r : List α // r.length < input.length }),
        many1Parse p input = some (snel, r) →
        many1Print p snel.1.toList snel.2 ++ r.val = input := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro input hn snel r hpar
    rcases hp : p.parse input with _ | ⟨sx, r0⟩
    · rw [many1Parse_none hp] at hpar; simp at hpar
    · rw [many1Parse_cons hp] at hpar
      rcases hM : many1Parse p r0.val with _ | ⟨snel', r2⟩
      · rw [hM] at hpar
        simp only [Option.some.injEq, Prod.mk.injEq] at hpar
        obtain ⟨hsnel, rfl⟩ := hpar
        subst hsnel
        simp only [NEList.toList, many1Print, List.append_nil]
        exact p.print_parse input sx r0 hp
      · rw [hM] at hpar
        simp only [Option.some.injEq, Prod.mk.injEq] at hpar
        obtain ⟨hsnel, rfl⟩ := hpar
        subst hsnel
        have hr0 := ih r0.val.length (hn ▸ r0.property) r0.val rfl snel' r2 hM
        show p.print sx.1 sx.2 ++ many1Print p snel'.1.toList snel'.2 ++ r2.val = input
        rw [List.append_assoc, hr0]
        exact p.print_parse input sx r0 hp

/-- **One-or-more `p`**, collecting `ManyAnn` — a list of the elements' annotations. -/
def many1 (p : IsoParser α fst fol v Ann) (hrep : ∀ c, fst c = true → fol c = true) :
    IsoParser α fst (fun c => fol c && !fst c) (NEList v) (fun nel => ManyAnn Ann nel.toList) where
  parse := many1Parse p
  print nel a := many1Print p nel.toList a
  firstOk c rest hc := many1Parse_none (p.firstOk c rest hc)
  parse_print nel a rest hr := by
    obtain ⟨x, xs⟩ := nel
    exact many1Parse_run p hrep x xs a rest hr
  print_parse input snel r h := many1Parse_exact p input.length input rfl snel r h

/-! ## `hide` — move a value into the annotation -/

/-- **Hide a value in the annotation.** The value becomes `Unit`; what was the value (with its
annotation) becomes *the choice*. This is how a whitespace run's characters become an annotation. -/
def hide {V : Type} {PAnn : V → Type} (p : IsoParser α fst fol V PAnn) :
    IsoParser α fst fol Unit (fun _ => Σ x : V, PAnn x) where
  parse input := (p.parse input).map (fun z => (⟨(), z.1⟩, z.2))
  print _ sxa := p.print sxa.1 sxa.2
  firstOk c rest hc := by simp [p.firstOk c rest hc]
  parse_print u sxa rest hr := by
    obtain ⟨x, ax⟩ := sxa
    obtain ⟨r, hpar, hrv⟩ := run_eq_some (p.run_print x ax rest hr)
    simp [hpar, hrv]
  print_parse input usxa r h := by
    rcases hp : p.parse input with _ | ⟨sx, r'⟩
    · rw [hp] at h; simp at h
    · rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨husxa, rfl⟩ := h
      subst husxa
      exact p.print_parse input sx r' hp

/-! ## `orElse` — alternation (FIRST-disjoint) -/

/-- Try `p`, else `q`. -/
def orElseParse {f1 f2 fol : α → Bool} {a b : Type} {Aa : a → Type} {Ab : b → Type}
    (p : IsoParser α f1 fol a Aa) (q : IsoParser α f2 fol b Ab) : (input : List α) →
    Option ((Σ s : a ⊕ b, Sum.elim Aa Ab s) × { r : List α // r.length < input.length })
  | input =>
    match p.parse input with
    | some (sx, r) => some (⟨Sum.inl sx.1, sx.2⟩, r)
    | none =>
      match q.parse input with
      | some (sy, r) => some (⟨Sum.inr sy.1, sy.2⟩, r)
      | none => none

/-- **Alternation.** Value is a sum; annotation is `Sum.elim`. Seam: `FIRST(q)` tokens make `p` fail
(FIRST-disjoint), so the choice is deterministic and round-trips. Both share FOLLOW. -/
def orElse {f1 f2 fol : α → Bool} {a b : Type} {Aa : a → Type} {Ab : b → Type}
    (p : IsoParser α f1 fol a Aa) (q : IsoParser α f2 fol b Ab)
    (hdisj : ∀ c, f2 c = true → f1 c = false) :
    IsoParser α (fun c => f1 c || f2 c) fol (a ⊕ b) (Sum.elim Aa Ab) where
  parse := orElseParse p q
  print
    | .inl x, ann => p.print x ann
    | .inr y, ann => q.print y ann
  firstOk c rest hc := by
    simp only [Bool.or_eq_false_iff] at hc
    simp [orElseParse, p.firstOk c rest hc.1, q.firstOk c rest hc.2]
  parse_print s ann rest hr := by
    cases s with
    | inl x =>
      obtain ⟨r, hpar, hrv⟩ := run_eq_some (p.run_print x ann rest hr)
      simp only [orElseParse, hpar]
      simp [hrv]
    | inr y =>
      have hpn : p.parse (q.print y ann ++ rest) = none := by
        obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (print_ne_nil q y ann)
        rw [hcs, List.cons_append]
        exact p.firstOk c (cs ++ rest) (hdisj c (print_head_fst q y ann c cs hcs))
      obtain ⟨r, hpar, hrv⟩ := run_eq_some (q.run_print y ann rest hr)
      simp only [orElseParse, hpn, hpar]
      simp [hrv]
  print_parse input sann r h := by
    simp only [orElseParse] at h
    split at h
    · next sx r0 hp =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hsann, rfl⟩ := h
      subst hsann
      exact p.print_parse input sx r0 hp
    · split at h
      · next sy r0 hq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hsann, rfl⟩ := h
        subst hsann
        exact q.print_parse input sy r0 hq
      · simp at h

/-! ## `imapT` — relabel the value along an iso (trivial annotation) -/

/-- **Relabel the value** along an iso `f`/`g`, keeping the trivial `PUnit` annotation. Used to map a
combinator's sum-of-products value into a target type (e.g. an `Expr` constructor). -/
def imapT {a b : Type} (f : a → b) (g : b → a)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    (p : IsoParser α fst fol a (fun _ => PUnit)) :
    IsoParser α fst fol b (fun _ => PUnit) where
  parse input := (p.parse input).map (fun z => (⟨f z.1.1, PUnit.unit⟩, z.2))
  print y _ := p.print (g y) PUnit.unit
  firstOk c rest hc := by simp [p.firstOk c rest hc]
  parse_print y u rest hr := by
    obtain ⟨⟩ := u
    obtain ⟨r, hpar, hrv⟩ := run_eq_some (p.run_print (g y) PUnit.unit rest hr)
    simp [hpar, hrv, hfg]
  print_parse input yu r h := by
    rcases hp : p.parse input with _ | ⟨⟨sxv, ⟨⟩⟩, r'⟩
    · rw [hp] at h; simp at h
    · rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hyu, rfl⟩ := h
      subst hyu
      show p.print (g (f sxv)) PUnit.unit ++ r'.val = input
      rw [hgf sxv]
      exact p.print_parse input ⟨sxv, PUnit.unit⟩ r' hp

/-! ## `trivialize` — collapse a no-choice annotation to `PUnit` -/

/-- **Collapse a trivial annotation to `PUnit`.** When the annotation is uniquely determined
(`huniq`), it carries no information — e.g. the nested `PUnit` products `seq`/`many1`/`orElse` leave
behind. This normalizes it so the value can be reshaped by `imapT`. -/
def trivialize (p : IsoParser α fst fol v Ann) (dflt : ∀ x, Ann x)
    (huniq : ∀ x (a : Ann x), a = dflt x) :
    IsoParser α fst fol v (fun _ => PUnit) where
  parse input := (p.parse input).map (fun z => (⟨z.1.1, PUnit.unit⟩, z.2))
  print x _ := p.print x (dflt x)
  firstOk c rest hc := by simp [p.firstOk c rest hc]
  parse_print x u rest hr := by
    obtain ⟨⟩ := u
    obtain ⟨r, hpar, hrv⟩ := run_eq_some (p.run_print x (dflt x) rest hr)
    simp [hpar, hrv]
  print_parse input xu r h := by
    rcases hp : p.parse input with _ | ⟨sx, r'⟩
    · rw [hp] at h; simp at h
    · rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hxu, rfl⟩ := h
      subst hxu
      show p.print sx.1 (dflt sx.1) ++ r'.val = input
      rw [← huniq sx.1 sx.2]
      exact p.print_parse input sx r' hp

end LambdaLab.IsoParser
