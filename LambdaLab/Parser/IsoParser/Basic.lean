/-!
# `IsoParser` — a consuming biparser with FIRST/FOLLOW indices and the round-trip law

**⚠ Experimental redesign** (from `Playground/CRoundTripBiparser.lean`): the *split* source/value
model — the monadic-profunctor shape — replacing the previous fused value+annotation design.

An `IsoParser α fst fol w v` parses a `v` (with a strictly-shorter leftover — progress lives in
the type) and prints from a source `w`. The indices are **propositions**: they never touch
`parse`/`print`, so Prop costs nothing computationally.

* `fst` (**FIRST**): symbols the parser can start with. `firstOk` is the negative claim — outside
  FIRST, parse fails. It exists so `bind` can *derive* "whatever the continuation prints starts
  with its FIRST" (`head_first`), which feeds the seam.
* `fol` (**FOLLOW**): continuations the parser provably stops at. The law `ok` is guarded by it;
  at `rest = []` the guard is vacuous, so the terminal round-trip (`roundtrip`) is free.

The law is stated in **erased form** (through `.map (fun z => (z.1, z.2.val))`): a raw statement
would put the leftover under a dependent proof and break input rewrites (append-associativity in
`bind`); erased, the equation's type is input-independent and every rewrite is clean.

What the split model trades away (relative to the previous fused design): the law pins only the
printed *value* `(print w).1`, never connecting it to the source `w`; exactness in its indexed
form ("whatever parse consumed is a print of *the result's* annotation") is not stateable (parse
yields values, print consumes sources) — only the ∃-source form is, and `Exact` below states it,
as the witness the `IsoParser → LossyParser` converters consume; and there is no annotation
family, so only canonical-form languages are genuine isos. What it buys: `comap`, a real
(indexed) monadic `bind`, and `do`-style sequencing over product sources.

Free theorems from progress-in-the-type: `run_nil` (every parser fails on `[]`) and
`print_ne_nil` (printed output is nonempty) — so alternation needs only FIRST-disjointness.
-/

namespace LambdaLab.Parser.IsoParser

variable {α : Type} {fst fol : α → Prop} {w v : Type}

/-- The FOLLOW condition: `rest` is empty, or its head is admissible. Vacuous at `[]`. -/
def HeadIn (f : α → Prop) (rest : List α) : Prop :=
  ∀ c, rest.head? = some c → f c

@[simp] theorem HeadIn_nil (f : α → Prop) : HeadIn f ([] : List α) := by
  intro c h; simp at h

/-- Weaken a FOLLOW condition along `f ≤ g`. -/
theorem HeadIn.mono {f g : α → Prop} (h : ∀ c, f c → g c)
    {rest : List α} (hr : HeadIn f rest) : HeadIn g rest :=
  fun c hc => h c (hr c hc)

/-- A consuming biparser: parse a value with a strictly-shorter leftover, print from a source,
carrying FIRST-soundness and the round-trip law. -/
structure IsoParser (α : Type) (fst fol : α → Prop) (w v : Type) where
  /-- Parse a prefix into a value and a strictly shorter leftover. -/
  parse : (input : List α) → Option (v × { r : List α // r.length < input.length })
  /-- Print a source: the value it denotes, and its output. -/
  print : w → v × List α
  /-- FIRST is sound: outside it, the parse fails. -/
  firstOk : ∀ c rest, ¬ fst c → parse (c :: rest) = none
  /-- **The law**, in erased form: print, then parse with a FOLLOW-admissible continuation —
  recover the printed value, continuation untouched. -/
  ok : ∀ (a : w) (rest : List α), HeadIn fol rest →
    (parse ((print a).2 ++ rest)).map (fun z => (z.1, z.2.val)) = some ((print a).1, rest)

/-- The parse result with the progress proof erased. -/
def IsoParser.run (p : IsoParser α fst fol w v) (input : List α) : Option (v × List α) :=
  (p.parse input).map (fun z => (z.1, z.2.val))

/-- Recover the raw parse result (with its progress witness) from an erased equation. -/
theorem run_eq_some {p : IsoParser α fst fol w v} {input : List α} {b : v} {rest : List α}
    (h : p.run input = some (b, rest)) :
    ∃ r : { r : List α // r.length < input.length },
      p.parse input = some (b, r) ∧ r.val = rest := by
  unfold IsoParser.run at h
  cases hp : p.parse input with
  | none => rw [hp] at h; simp at h
  | some z =>
    obtain ⟨b', r⟩ := z
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨r, rfl, rfl⟩

/-- **Exactness** — the converse of `ok`: whatever the parser consumed is the print of some
source. A *predicate* at this level, proved per parser by an exactness induction
(`Mixfix/Sound.lean` for the mixfix stack); the `IsoParser → LossyParser` converters consume it
to discharge the lossy level's `exact` law. -/
def IsoParser.Exact (p : IsoParser α fst fol w v) : Prop :=
  ∀ (input : List α) (b : v) (rest : List α),
    p.run input = some (b, rest) → ∃ a : w, (p.print a).1 = b ∧ (p.print a).2 ++ rest = input

/-- `ok`, restated on `run`. -/
theorem IsoParser.run_print (p : IsoParser α fst fol w v) (a : w) (rest : List α)
    (h : HeadIn fol rest) : p.run ((p.print a).2 ++ rest) = some ((p.print a).1, rest) :=
  p.ok a rest h

/-- **Every parser fails on empty input** — free: a success would need a shorter-than-empty
leftover. -/
theorem IsoParser.run_nil (p : IsoParser α fst fol w v) : p.parse [] = none := by
  match hp : p.parse [] with
  | none => rfl
  | some (b, ⟨r, hr⟩) => exact absurd hr (by simp)

/-- **The terminal round-trip** — at end of input the FOLLOW guard is vacuous. -/
theorem IsoParser.roundtrip (p : IsoParser α fst fol w v) (a : w) :
    p.run (p.print a).2 = some ((p.print a).1, []) := by
  have h := p.ok a [] (HeadIn_nil _)
  -- rewrite `++ []` away while the statement is in erased form (input-independent motive)
  rw [List.append_nil] at h
  exact h

/-- **A printed output is never empty** — free: printing then parsing succeeds (`ok`), but every
parse of `[]` fails (`run_nil`). -/
theorem IsoParser.print_ne_nil (p : IsoParser α fst fol w v) (a : w) : (p.print a).2 ≠ [] := by
  intro h
  have hok := p.roundtrip a
  unfold IsoParser.run at hok
  rw [h, p.run_nil] at hok
  simp at hok

/-- A printed output (with admissible continuation) starts with a FIRST symbol — *derived* from
`ok` + `firstOk`, not assumed. This is what discharges `bind`'s internal seam. Classical: `fst`
need not be decidable. -/
theorem IsoParser.head_first (q : IsoParser α fst fol w v) (a : w) (rest : List α)
    (hrest : HeadIn fol rest) :
    ∀ c, ((q.print a).2 ++ rest).head? = some c → fst c := by
  intro c hc
  refine Classical.byContradiction fun hf => ?_
  cases hl : (q.print a).2 ++ rest with
  | nil => rw [hl] at hc; exact absurd hc (by simp)
  | cons x xs =>
    rw [hl] at hc
    have hx : x = c := by simpa using hc
    subst hx
    have hok := q.ok a rest hrest
    rw [hl, q.firstOk x xs hf] at hok
    simp at hok

/-- The printed values of equal outputs agree — the split model's residue of `print_injective`
(the *sources* need not agree; that is exactly the fusion this design gave up). -/
theorem IsoParser.print_val_eq (p : IsoParser α fst fol w v)
    {a a' : w} (h : (p.print a).2 = (p.print a').2) : (p.print a).1 = (p.print a').1 := by
  have h1 := p.roundtrip a
  rw [h, p.roundtrip a'] at h1
  exact (congrArg Prod.fst (Option.some.inj h1)).symm

end LambdaLab.Parser.IsoParser
