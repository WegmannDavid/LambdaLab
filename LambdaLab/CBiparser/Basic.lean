import LambdaLab.NEList

/-!
# `CBiparser` — a consuming biparser over an arbitrary alphabet

The `Playground` prototype hardwired `List Char`. This is the same development generalized
over an alphabet `α`, which is what `Language1` needs (its alphabet is `Token`, not `Char`).

Two parameters beyond the alphabet, because parse and print pull in opposite directions:
`v` is the **value** we parse *into* (covariant), `w` is the **source** we print *from*
(contravariant). The printer returns `v × List α` — not just the output — so that `bind` can
recover the parsed value from the source.

Progress lives **in the type**: the leftover is a *strict* suffix. That single fact pays for
termination (every combinator's recursion is well-founded for free) and, later, for the
round-trip law (`run_nil`: every biparser provably fails on empty input).
-/

namespace LambdaLab.CBiparser

variable {α : Type} {w v v' : Type}

/-- A biparser that always consumes at least one symbol. -/
structure CBiparser (α : Type) (w v : Type) where
  parse : (input : List α) → Option (v × { r : List α // r.length < input.length })
  print : w → v × List α

/-- The parse result with the progress proof erased. Every law below is stated against `run`,
which keeps the `{r // r.length < _}` subtype out of the proofs entirely. -/
def CBiparser.run (p : CBiparser α w v) (input : List α) : Option (v × List α) :=
  (p.parse input).map (fun (a, r) => (a, r.val))

/-- **Every biparser fails on empty input** — a *theorem*, not an assumption: the leftover
must satisfy `r.length < [].length = 0`, and nothing does. This is progress-in-the-type
paying for the round-trip law: it is what discharges the top-level FOLLOW for free. -/
theorem run_nil (p : CBiparser α w v) : p.run [] = none := by
  simp only [CBiparser.run]
  rcases h : p.parse [] with _ | ⟨a, r, hr⟩
  · rfl
  · exact absurd hr (by simp)

instance : Functor (CBiparser α w) where
  map f p :=
    { parse := fun input => (p.parse input).map (fun (a, ⟨r, hr⟩) => (f a, ⟨r, hr⟩))
      print := fun u => let (a, o) := p.print u; (f a, o) }

instance : Bind (CBiparser α w) where
  bind p k :=
    { parse := fun input => do
        let (a, ⟨r, hr⟩) ← p.parse input
        let (b, ⟨r', hr'⟩) ← (k a).parse r
        some (b, ⟨r', Nat.lt_trans hr' hr⟩)
      print := fun u =>
        let (a, o1) := p.print u
        let (b, o2) := (k a).print u
        (b, o1 ++ o2) }

/-- Adapt the **source** (the contravariant slot). Parse ignores the source, so it is
untouched; `comap` is purely a print-side adapter. -/
def comap (f : w' → w) (p : CBiparser α w v) : CBiparser α w' v where
  parse := p.parse
  print u := p.print (f u)

/-! ## How each combinator decomposes — `_print` and `_run`, both at the erased level.

Keeping this uniform is what keeps every proof downstream a rewrite chain. The moment a
combinator reaches back into `parse` and its subtype, its proof balloons. -/

theorem map_print (f : v → v') (p : CBiparser α w v) (s : w) :
    (f <$> p).print s = (f (p.print s).1, (p.print s).2) := rfl

theorem map_run (f : v → v') (p : CBiparser α w v) (input : List α) :
    (f <$> p).run input = (p.run input).map (fun (a, r) => (f a, r)) := by
  simp only [CBiparser.run, Functor.map]
  cases p.parse input <;> rfl

theorem bind_print (p : CBiparser α w v) (k : v → CBiparser α w v') (s : w) :
    (p >>= k).print s =
      (((k (p.print s).1).print s).1, (p.print s).2 ++ ((k (p.print s).1).print s).2) := by
  simp only [Bind.bind]

theorem bind_run (p : CBiparser α w v) (k : v → CBiparser α w v') (input : List α) :
    (p >>= k).run input =
      match p.run input with
      | none => none
      | some (a, r) => (k a).run r := by
  simp only [CBiparser.run, Bind.bind]
  rcases hp : p.parse input with _ | ⟨a, r, hr⟩
  · simp
  · rcases hk : (k a).parse r with _ | ⟨b, r', hr'⟩ <;> simp [hk]

/-! ## One-or-more

Parse and print are *separate* recursions — parse well-founded on `input.length`, print
structural on the source list — bundled by `many1NE`. A single self-referential `where`-def
could not prove termination: the decreasing argument lives in the *field* arguments, not in
the combinator's own argument `p`.

The source is a `NEList`: `many1NE` never *parses* an empty list, so a `List w` source would
be wider than the printable set and would falsify the round-trip law. -/

def many1Parse (p : CBiparser α w v) (input : List α) :
    Option (List v × { r : List α // r.length < input.length }) :=
  match p.parse input with
  | none => none
  | some (a, ⟨r, hr⟩) =>
      match many1Parse p r with
      | none => some ([a], ⟨r, hr⟩)
      | some (as, ⟨r', hr'⟩) => some (a :: as, ⟨r', Nat.lt_trans hr' hr⟩)
termination_by input.length
decreasing_by exact hr

def many1Print (p : CBiparser α w v) : List w → List v × List α
  | [] => ([], [])
  | u :: us =>
      let (a, o)  := p.print u
      let (as, o') := many1Print p us
      (a :: as, o ++ o')

def many1NE (p : CBiparser α w v) : CBiparser α (NEList w) (List v) where
  parse := many1Parse p
  print := fun (u, us) => many1Print p (u :: us)

theorem many1Print_nil (p : CBiparser α w v) : many1Print p [] = ([], []) := rfl

theorem many1Print_cons_fst (p : CBiparser α w v) (x : w) (xs : List w) :
    (many1Print p (x :: xs)).1 = (p.print x).1 :: (many1Print p xs).1 := rfl

theorem many1Print_cons_snd (p : CBiparser α w v) (x : w) (xs : List w) :
    (many1Print p (x :: xs)).2 = (p.print x).2 ++ (many1Print p xs).2 := rfl

theorem many1Parse_eq (p : CBiparser α w v) (input : List α) :
    many1Parse p input =
      match p.parse input with
      | none => none
      | some (a, ⟨r, hr⟩) =>
          match many1Parse p r with
          | none => some ([a], ⟨r, hr⟩)
          | some (as, ⟨r', hr'⟩) => some (a :: as, ⟨r', Nat.lt_trans hr' hr⟩) := by
  conv => lhs; rw [many1Parse]

/-- The recursion restated at the erased level — no subtypes, so the round-trip proof is a
plain rewrite chain. It is a *recursion* equation, so it must be `rw`n once (as a `simp`
lemma it would loop). -/
theorem many1NE_run_eq (p : CBiparser α w v) (input : List α) :
    (many1NE p).run input =
      match p.run input with
      | none => none
      | some (a, r) =>
          match (many1NE p).run r with
          | none => some ([a], r)
          | some (as, r') => some (a :: as, r') := by
  show (many1Parse p input).map (fun (a, r) => (a, r.val)) = _
  rw [many1Parse_eq]
  rcases hp : p.parse input with _ | ⟨a, r, hr⟩
  · simp [CBiparser.run, hp]
  · rcases hm : many1Parse p r with _ | ⟨as, r', hr'⟩ <;>
      simp [CBiparser.run, many1NE, hp, hm]

end LambdaLab.CBiparser
