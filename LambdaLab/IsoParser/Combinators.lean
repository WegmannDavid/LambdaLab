import LambdaLab.IsoParser.Basic
import LambdaLab.NEList

/-!
# `IsoParser` combinators (split source/value model)

Each combinator rebuilds the round-trip law as it goes, so every parser assembled from these is
correct by construction. The toolkit:

* **leaves** — `sat` (a predicate-restricted symbol; aligned source), `tok` (a literal symbol;
  the source is *polymorphic*, so keywords need no `comap`);
* **plumbing** — `comap` (adapt the source), `map` (adapt the value);
* **sequencing** — `bind`, an *indexed* monadic bind (the seam `FIRST(k) ⊆ FOLLOW(p)` is its one
  obligation; `Notation.lean`'s `gdo` provides the do-syntax);
* **choice** — `orElse` (FIRST-disjoint; source and value are sums);
* **repetition** — `many1` (one-or-more; source `NEList w`), `chainl` (a seed then zero-or-more
  steps — the left-associative chain shape).

Composite parse functions are **named** (`bindParse`, `orElseParse`, `many1Parse`, `chainlParse`):
rewriting the input of an applied function has a clean motive, an inline `match` does not.
-/

namespace LambdaLab.IsoParser

variable {α : Type} {fst fol f₁ fo₁ f₂ fo₂ : α → Prop} {w w' v v' : Type}

/-! ## Helpers -/

/-- Recover a raw parse result (with its progress witness) from an erased equation — the generic
form of `run_eq_some`, for any named parse function. -/
theorem map_val_eq_some {β : Type} {input : List α}
    {o : Option (β × { r : List α // r.length < input.length })} {b : β} {rest : List α}
    (h : o.map (fun z => (z.1, z.2.val)) = some (b, rest)) :
    ∃ r, o = some (b, r) ∧ r.val = rest := by
  cases o with
  | none => simp at h
  | some z =>
    obtain ⟨b', r⟩ := z
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨r, rfl, rfl⟩

/-- A printed output starts with a FIRST symbol (no continuation hypothesis — printing then
parsing succeeds terminally, so `firstOk` pins the head). -/
theorem print_head_fst (p : IsoParser α fst fol w v) (a : w) (c : α) (cs : List α)
    (h : (p.print a).2 = c :: cs) : fst c := by
  refine Classical.byContradiction fun hf => ?_
  have hr := p.roundtrip a
  unfold IsoParser.run at hr
  rw [h, p.firstOk c cs hf] at hr
  simp at hr

/-- `print a ++ rest` has a `g`-admissible head, for any `g ⊇ FIRST` — the printed output is
nonempty, so its head (a FIRST symbol) is the head of the whole. -/
theorem headIn_print_append (p : IsoParser α fst fol w v) {g : α → Prop}
    (hg : ∀ c, fst c → g c) (a : w) (rest : List α) :
    HeadIn g ((p.print a).2 ++ rest) := by
  intro d hd
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (p.print_ne_nil a)
  rw [hcs, List.cons_append, List.head?_cons, Option.some.injEq] at hd
  subst hd
  exact hg c (print_head_fst p a c cs hcs)

/-! ## Leaves -/

/-- Parse one symbol satisfying `pred`. -/
def satParse (pred : α → Bool) : (input : List α) →
    Option ({ a : α // pred a = true } × { r : List α // r.length < input.length })
  | [] => none
  | hd :: tl => if h : pred hd then some (⟨hd, h⟩, ⟨tl, by simp⟩) else none

/-- **One symbol satisfying `pred`** — aligned (source = value). FIRST = `pred`, FOLLOW = ⊤. -/
def sat (pred : α → Bool) :
    IsoParser α (fun c => pred c = true) (fun _ => True)
      { a : α // pred a = true } { a : α // pred a = true } where
  parse := satParse pred
  print d := (d, [d.val])
  firstOk c rest hc := by simp [satParse, hc]
  ok d rest _ := by simp [satParse, d.property]

/-- Parse a literal symbol `t`. -/
def tokParse [DecidableEq α] (t : α) : (input : List α) →
    Option (Unit × { r : List α // r.length < input.length })
  | [] => none
  | hd :: tl => if hd = t then some ((), ⟨tl, by simp⟩) else none

/-- **A literal symbol `t`.** The *source is polymorphic* (printing is constant), so a keyword
plugs into any product source without a `comap`. FIRST `(· = t)`, FOLLOW ⊤. -/
def tok [DecidableEq α] (t : α) : IsoParser α (· = t) (fun _ => True) w Unit where
  parse := tokParse t
  print _ := ((), [t])
  firstOk c rest hc := by simp [tokParse, hc]
  ok a rest _ := by simp [tokParse]

/-! ## Plumbing -/

/-- **Adapt the source**: print from `w'` by first projecting to `w`. Parse (and the value the
law returns) are untouched. This is how a product node works: each sub-parser `comap`s the
projection it needs. -/
def comap (g : w' → w) (p : IsoParser α fst fol w v) : IsoParser α fst fol w' v where
  parse := p.parse
  print a' := p.print (g a')
  firstOk := p.firstOk
  ok a' rest h := p.ok (g a') rest h

/-- **Adapt the value**; the leftover (and its progress proof) pass through. -/
def map (f : v → v') (p : IsoParser α fst fol w v) : IsoParser α fst fol w v' where
  parse input := (p.parse input).map (fun br => (f br.1, br.2))
  print a := (f (p.print a).1, (p.print a).2)
  firstOk c rest hc := by rw [p.firstOk c rest hc]; rfl
  ok a rest h := by
    obtain ⟨r, hp, hv⟩ := map_val_eq_some (p.ok a rest h)
    show ((p.parse ((p.print a).2 ++ rest)).map _).map _ = _
    rw [hp]
    simp [hv]

/-! ## Sequencing — the indexed monadic bind -/

/-- The composite parse, named for clean motives. Progress composes by transitivity. -/
def bindParse (p : IsoParser α f₁ fo₁ w v) (k : v → IsoParser α f₂ fo₂ w v') :
    (input : List α) → Option (v' × { r : List α // r.length < input.length }) :=
  fun input =>
    match p.parse input with
    | none => none
    | some (b, r) =>
      match (k b).parse r.val with
      | none => none
      | some (c, r') => some (c, ⟨r'.val, Nat.lt_trans r'.property r.property⟩)

/-- **Monadic bind** — possible because `k`'s *type* pins its FIRST/FOLLOW independently of the
parsed value (the indexed-monad discipline). The seam `FIRST(k) ⊆ FOLLOW(p)` is its one
obligation: inside `p >>= k`, `p`'s continuation starts with whatever `k` prints, and
`head_first` turns that into a FOLLOW-admissible continuation for `p`'s law. -/
def bind (p : IsoParser α f₁ fo₁ w v) (k : v → IsoParser α f₂ fo₂ w v')
    (hseam : ∀ c, f₂ c → fo₁ c) : IsoParser α f₁ fo₂ w v' where
  parse := bindParse p k
  print a :=
    (((k (p.print a).1).print a).1, (p.print a).2 ++ ((k (p.print a).1).print a).2)
  firstOk c rest hc := by
    show bindParse p k (c :: rest) = none
    simp only [bindParse]
    rw [p.firstOk c rest hc]
  ok a rest hrest := by
    have h1 : HeadIn fo₁ (((k (p.print a).1).print a).2 ++ rest) :=
      fun c hc => hseam c ((k (p.print a).1).head_first a rest hrest c hc)
    obtain ⟨r1, hp1, hv1⟩ := map_val_eq_some (p.ok a _ h1)
    have hkrun : ((k (p.print a).1).parse r1.val).map (fun z => (z.1, z.2.val))
        = some (((k (p.print a).1).print a).1, rest) := by
      rw [hv1]; exact (k (p.print a).1).ok a rest hrest
    obtain ⟨r2, hp2, hv2⟩ := map_val_eq_some hkrun
    show (bindParse p k (((p.print a).2 ++ ((k (p.print a).1).print a).2) ++ rest)).map
          (fun z => (z.1, z.2.val))
        = some (((k (p.print a).1).print a).1, rest)
    rw [show ((p.print a).2 ++ ((k (p.print a).1).print a).2) ++ rest
          = (p.print a).2 ++ (((k (p.print a).1).print a).2 ++ rest) from List.append_assoc ..]
    simp only [bindParse]
    rw [hp1]
    dsimp only
    rw [hp2]
    simp [hv2]

/-! ## Choice — FIRST-disjoint alternation -/

/-- Try `p`, else `q`; named for clean motives. -/
def orElseParse (p : IsoParser α f₁ fol w v) (q : IsoParser α f₂ fol w' v') :
    (input : List α) → Option ((v ⊕ v') × { r : List α // r.length < input.length }) :=
  fun input =>
    match p.parse input with
    | some (b, r) => some (Sum.inl b, r)
    | none =>
      match q.parse input with
      | some (b', r) => some (Sum.inr b', r)
      | none => none

/-- **Alternation.** Source and value are sums; FIRST is the union; both branches share FOLLOW.
`hdisj` (`FIRST(q) ⊆ ¬FIRST(p)`) makes the biased choice deterministic: `q`'s printed output
starts with a `FIRST(q)` symbol, so `firstOk` makes `p` fail on it. Progress makes this the
*only* obligation (`print_ne_nil` covers the empty-output hazard). -/
def orElse (p : IsoParser α f₁ fol w v) (q : IsoParser α f₂ fol w' v')
    (hdisj : ∀ c, f₂ c → ¬ f₁ c) :
    IsoParser α (fun c => f₁ c ∨ f₂ c) fol (w ⊕ w') (v ⊕ v') where
  parse := orElseParse p q
  print
    | Sum.inl a  => (Sum.inl (p.print a).1, (p.print a).2)
    | Sum.inr a' => (Sum.inr (q.print a').1, (q.print a').2)
  firstOk c rest hc := by
    show orElseParse p q (c :: rest) = none
    simp only [orElseParse]
    rw [p.firstOk c rest (fun h => hc (Or.inl h)),
        q.firstOk c rest (fun h => hc (Or.inr h))]
  ok a rest hrest := by
    cases a with
    | inl a =>
      obtain ⟨r, hp, hv⟩ := map_val_eq_some (p.ok a rest hrest)
      show (orElseParse p q ((p.print a).2 ++ rest)).map (fun z => (z.1, z.2.val))
          = some (Sum.inl (p.print a).1, rest)
      simp only [orElseParse]
      rw [hp]
      simp [hv]
    | inr a' =>
      have hpnone : p.parse ((q.print a').2 ++ rest) = none := by
        cases hout : (q.print a').2 with
        | nil => exact absurd hout (q.print_ne_nil a')
        | cons c cs =>
          have hc2 : f₂ c := q.head_first a' rest hrest c (by rw [hout]; rfl)
          exact p.firstOk c (cs ++ rest) (hdisj c hc2)
      obtain ⟨r, hq, hv⟩ := map_val_eq_some (q.ok a' rest hrest)
      show (orElseParse p q ((q.print a').2 ++ rest)).map (fun z => (z.1, z.2.val))
          = some (Sum.inr (q.print a').1, rest)
      simp only [orElseParse]
      rw [hpnone, hq]
      simp [hv]

/-! ## Repetition — `many1` and `chainl` -/

/-- Parse one-or-more `p`, greedily. -/
def many1Parse (p : IsoParser α fst fol w v) : (input : List α) →
    Option (NEList v × { r : List α // r.length < input.length })
  | input =>
    match p.parse input with
    | none => none
    | some (b, r) =>
      match many1Parse p r.val with
      | none => some ((b, []), r)
      | some (nel, r2) => some ((b, nel.toList), ⟨r2.val, Nat.lt_trans r2.property r.property⟩)
termination_by input => input.length
decreasing_by exact r.property

/-- The printed values of a source list. -/
def many1PrintV (p : IsoParser α fst fol w v) : List w → List v
  | [] => []
  | a :: as => (p.print a).1 :: many1PrintV p as

/-- The concatenated outputs of a source list. -/
def many1PrintOut (p : IsoParser α fst fol w v) : List w → List α
  | [] => []
  | a :: as => (p.print a).2 ++ many1PrintOut p as

/-- **Round-trip for `many1`**, in printed form; by induction on the source list. `hrep`
("an element's own output may follow an element") is `FIRST ⊆ FOLLOW`. -/
theorem many1Parse_run (p : IsoParser α fst fol w v) (hrep : ∀ c, fst c → fol c) :
    ∀ (as : List w) (a : w) (rest : List α), HeadIn (fun c => fol c ∧ ¬ fst c) rest →
      (many1Parse p ((p.print a).2 ++ (many1PrintOut p as ++ rest))).map
          (fun z => (z.1, z.2.val))
        = some (((p.print a).1, many1PrintV p as), rest) := by
  intro as
  induction as with
  | nil =>
    intro a rest hrest
    simp only [many1PrintOut, many1PrintV, List.nil_append]
    have hfol : HeadIn fol rest := fun c hc => (hrest c hc).1
    obtain ⟨r, hp, hv⟩ := map_val_eq_some (p.ok a rest hfol)
    rw [many1Parse, hp]
    dsimp only
    have hstop : p.parse r.val = none := by
      rw [hv]
      cases rest with
      | nil => exact p.run_nil
      | cons c cs => exact p.firstOk c cs (hrest c rfl).2
    have hm : many1Parse p r.val = none := by rw [many1Parse, hstop]
    rw [hm]
    simp [hv]
  | cons a2 as' ih =>
    intro a rest hrest
    simp only [many1PrintOut, many1PrintV]
    have hcont : HeadIn fol ((p.print a2).2 ++ (many1PrintOut p as' ++ rest)) :=
      headIn_print_append p hrep a2 _
    obtain ⟨r, hp, hv⟩ := map_val_eq_some (p.ok a _ hcont)
    have hih' : (many1Parse p r.val).map (fun z => (z.1, z.2.val))
        = some (((p.print a2).1, many1PrintV p as'), rest) := by
      rw [hv]; exact ih a2 rest hrest
    obtain ⟨r2, hm2, hv2⟩ := map_val_eq_some hih'
    rw [show (p.print a).2 ++ (((p.print a2).2 ++ many1PrintOut p as') ++ rest)
          = (p.print a).2 ++ ((p.print a2).2 ++ (many1PrintOut p as' ++ rest)) from by
        rw [List.append_assoc]]
    rw [many1Parse, hp]
    dsimp only
    rw [hm2]
    simp [hv2, NEList.toList]

/-- **One-or-more `p`.** Source `NEList w`, value `NEList v` — aligned when `p` is. FOLLOW
computes: the continuation may not start another element. -/
def many1 (p : IsoParser α fst fol w v) (hrep : ∀ c, fst c → fol c) :
    IsoParser α fst (fun c => fol c ∧ ¬ fst c) (NEList w) (NEList v) where
  parse := many1Parse p
  print nel := (((p.print nel.1).1, many1PrintV p nel.2),
                (p.print nel.1).2 ++ many1PrintOut p nel.2)
  firstOk c rest hc := by
    show many1Parse p (c :: rest) = none
    rw [many1Parse, p.firstOk c rest hc]
  ok nel rest hrest := by
    obtain ⟨a, as⟩ := nel
    show (many1Parse p (((p.print a).2 ++ many1PrintOut p as) ++ rest)).map _ = _
    rw [List.append_assoc]
    exact many1Parse_run p hrep as a rest hrest

/-- A seed, then zero-or-more steps (reusing `many1Parse`); named for clean motives. -/
def chainlParse (pSeed : IsoParser α f₁ fol w v) (pStep : IsoParser α f₂ fol w' v') :
    (input : List α) → Option ((v × List v') × { r : List α // r.length < input.length }) :=
  fun input =>
    match pSeed.parse input with
    | none => none
    | some (b, r) =>
      match many1Parse pStep r.val with
      | none => some ((b, []), r)
      | some (nel, r2) => some ((b, nel.toList), ⟨r2.val, Nat.lt_trans r2.property r.property⟩)

/-- **A left-associative chain**: `seed (step)*`. Source `w × List w'`, value `v × List v'`;
seed and steps share FOLLOW, and `hseam` (`FIRST(step) ⊆ FOLLOW`) covers both the seed→step seam
and step repetition. -/
def chainl (pSeed : IsoParser α f₁ fol w v) (pStep : IsoParser α f₂ fol w' v')
    (hseam : ∀ c, f₂ c → fol c) :
    IsoParser α f₁ (fun c => fol c ∧ ¬ f₂ c) (w × List w') (v × List v') where
  parse := chainlParse pSeed pStep
  print aw := (((pSeed.print aw.1).1, many1PrintV pStep aw.2),
               (pSeed.print aw.1).2 ++ many1PrintOut pStep aw.2)
  firstOk c rest hc := by
    show chainlParse pSeed pStep (c :: rest) = none
    simp only [chainlParse]
    rw [pSeed.firstOk c rest hc]
  ok aw rest hrest := by
    obtain ⟨a, steps⟩ := aw
    cases steps with
    | nil =>
      have hfol : HeadIn fol rest := fun c hc => (hrest c hc).1
      obtain ⟨r, hp, hv⟩ := map_val_eq_some (pSeed.ok a rest hfol)
      show (chainlParse pSeed pStep (((pSeed.print a).2 ++ many1PrintOut pStep []) ++ rest)).map
            (fun z => (z.1, z.2.val))
          = some (((pSeed.print a).1, many1PrintV pStep []), rest)
      rw [show ((pSeed.print a).2 ++ many1PrintOut pStep []) ++ rest
            = (pSeed.print a).2 ++ rest from by simp [many1PrintOut]]
      simp only [many1PrintV, chainlParse]
      rw [hp]
      dsimp only
      have hstop : pStep.parse r.val = none := by
        rw [hv]
        cases rest with
        | nil => exact pStep.run_nil
        | cons c cs => exact pStep.firstOk c cs (hrest c rfl).2
      have hm : many1Parse pStep r.val = none := by rw [many1Parse, hstop]
      rw [hm]
      simp [hv]
    | cons s2 ss =>
      have hcont : HeadIn fol ((pStep.print s2).2 ++ (many1PrintOut pStep ss ++ rest)) :=
        headIn_print_append pStep hseam s2 _
      obtain ⟨r, hp, hv⟩ := map_val_eq_some (pSeed.ok a _ hcont)
      have hih' : (many1Parse pStep r.val).map (fun z => (z.1, z.2.val))
          = some (((pStep.print s2).1, many1PrintV pStep ss), rest) := by
        rw [hv]; exact many1Parse_run pStep hseam ss s2 rest hrest
      obtain ⟨r2, hm2, hv2⟩ := map_val_eq_some hih'
      show (chainlParse pSeed pStep
              (((pSeed.print a).2 ++ many1PrintOut pStep (s2 :: ss)) ++ rest)).map
            (fun z => (z.1, z.2.val)) = _
      simp only [many1PrintOut, many1PrintV]
      rw [show ((pSeed.print a).2 ++ ((pStep.print s2).2 ++ many1PrintOut pStep ss)) ++ rest
            = (pSeed.print a).2 ++ ((pStep.print s2).2 ++ (many1PrintOut pStep ss ++ rest)) from by
          simp [List.append_assoc]]
      simp only [chainlParse]
      rw [hp]
      dsimp only
      rw [hm2]
      simp [hv2, NEList.toList]

end LambdaLab.IsoParser
