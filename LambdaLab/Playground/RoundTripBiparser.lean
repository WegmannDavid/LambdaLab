/-!
# Biparser with FIRST/FOLLOW indices and the round-trip law **in the structure**

The evolution of `Playground/Biparser.lean`: the law is a *field*, so every combinator must rebuild
it — and then every parser you can construct is correct by construction. The indices are
**propositions** (`Char → Prop`), not `Bool`: they never touch `parse`/`print` — they are pure
specification — so nothing computes with them and Prop costs nothing. What Prop changes:

* `firstOk`'s hypothesis is `¬ fst c` (was `fst c = false`);
* `head_first`'s case split on the index becomes **classical** (`Classical.byContradiction`) —
  a Prop need not be decidable;
* leaves state their FIRST as the actual proposition (`(· = c)`, not `decide (x = c)`), and the
  `seam` tactic still closes decidable atoms by `decide`.

The indices:

* `fst` (**FIRST**): tokens the parser can start with. `firstOk` is the *negative* claim — outside
  FIRST, parse fails. It exists so `bind` can *derive* "whatever the continuation prints starts
  with its FIRST" (`head_first`), which feeds the seam.
* `fol` (**FOLLOW**): continuations the parser provably stops at. The law `ok` is guarded by it;
  at `rest = []` the guard is vacuous, so the terminal round-trip (`roundtrip`) is free.

Cost: `bind` changes the indices (`f₁ fo₁ → f₁ fo₂`) and takes a seam proof
(`FIRST(k) ⊆ FOLLOW(p)`), so this is an **indexed** monad — Lean's `Monad`/`do` cannot apply.
The `gdo` macro replaces `do`, inserting `(by seam)` at every bind.
-/

/-- The FOLLOW condition: `rest` is empty, or its head is admissible. Vacuous at `[]`. -/
def HeadIn (f : Char → Prop) (rest : List Char) : Prop :=
  ∀ c, rest.head? = some c → f c

structure Biparser (fst fol : Char → Prop) (α β : Type) where
  parse : List Char → Option (β × List Char)
  print : α → β × List Char
  /-- FIRST is sound: outside it, the parse fails. -/
  firstOk : ∀ c rest, ¬ fst c → parse (c :: rest) = none
  /-- **The law.** Print, then parse with a FOLLOW-admissible continuation: recover the printed
  value, continuation untouched. -/
  ok : ∀ a rest, HeadIn fol rest →
    parse ((print a).2 ++ rest) = some ((print a).1, rest)

/-- **The payoff, terminally**: at end of input the FOLLOW guard is vacuous, so *every* `Biparser`
round-trips its printed output — no side conditions, no per-parser proof. -/
theorem Biparser.roundtrip (p : Biparser fst fol α β) (a : α) :
    p.parse (p.print a).2 = some ((p.print a).1, []) := by
  have h := p.ok a [] (fun c hc => absurd hc (by simp))
  simpa using h

/-- A printed output (with admissible continuation) always starts with a FIRST symbol — *derived*
from `ok` + `firstOk`, not assumed. This is what discharges `bind`'s internal seam. It holds even
when the printed output is empty: then the head comes from `rest`, and an empty-printing parser
must succeed on bare `rest`, so that head is in FIRST too. Classical: `fst` need not be decidable. -/
theorem Biparser.head_first (q : Biparser fst fol α β) (a : α) (rest : List Char)
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
    exact absurd hok.symm (Option.some_ne_none _)

/-- Adapt the source (parse ignores the source, and the law returns the printed value either way,
so the indices and law carry over untouched). -/
def Biparser.comap (g : α' → α) (p : Biparser fst fol α β) : Biparser fst fol α' β where
  parse := p.parse
  print a' := p.print (g a')
  firstOk := p.firstOk
  ok a' rest h := p.ok (g a') rest h

/-- Map the value. -/
def Biparser.map (f : β → γ) (p : Biparser fst fol α β) : Biparser fst fol α γ where
  parse input := (p.parse input).map (fun br => (f br.1, br.2))
  print a := (f (p.print a).1, (p.print a).2)
  firstOk c rest hc := by rw [p.firstOk c rest hc]; rfl
  ok a rest h := by
    show (p.parse ((p.print a).2 ++ rest)).map _ = _
    rw [p.ok a rest h]
    rfl

/-- **Bind, with the seam.** The indices change: result FIRST is `p`'s, result FOLLOW is `k`'s —
which is exactly why `Monad` can't host this. `hseam` (`FIRST(k) ⊆ FOLLOW(p)`) is the one
obligation: inside `p >>= k`, the continuation `p` actually faces starts with whatever `k` prints,
and `head_first` turns that into a FOLLOW-admissible continuation for `p`'s law. -/
def Biparser.bind (p : Biparser f₁ fo₁ α β) (k : β → Biparser f₂ fo₂ α γ)
    (hseam : ∀ c, f₂ c → fo₁ c) : Biparser f₁ fo₂ α γ where
  parse input :=
    match p.parse input with
    | none => none
    | some (b, rest) => (k b).parse rest
  print a :=
    (((k (p.print a).1).print a).1, (p.print a).2 ++ ((k (p.print a).1).print a).2)
  firstOk c rest hc := by
    show (match p.parse (c :: rest) with
          | none => none
          | some (b, rest) => (k b).parse rest) = none
    rw [p.firstOk c rest hc]
  ok a rest hrest := by
    have h1 : HeadIn fo₁ (((k (p.print a).1).print a).2 ++ rest) :=
      fun c hc => hseam c ((k (p.print a).1).head_first a rest hrest c hc)
    show (match p.parse ((p.print a).2 ++ ((k (p.print a).1).print a).2 ++ rest) with
          | none => none
          | some (b, rest) => (k b).parse rest) = _
    rw [List.append_assoc, p.ok a _ h1]
    exact (k (p.print a).1).ok a rest hrest

/-! ## `gdo` — do-notation for the indexed monad

Each bind's seam is threaded as `(by seam)`. The seams are the lexical facts that make the grammar
unambiguous; `seam` tries the common shapes (`trivial` for a `⊤` FOLLOW, `decide` for decidable
atoms like `¬('B'.isDigit)`). -/

macro "seam" : tactic => `(tactic| (
  intro c hc
  first
    | trivial
    | assumption
    | simp_all
    | decide))

syntax "gdo " ("let " ident " ← " term ";"?)+ "return " term : term

macro_rules
  | `(gdo $[let $xs ← $ps $[;]?]* return $e) => do
      let n := xs.size
      let mut acc ← `(Biparser.map (fun $(xs[n-1]!) => $e) $(ps[n-1]!))
      for i in [0:n-1] do
        let j := n - 2 - i
        acc ← `(Biparser.bind $(ps[j]!) (fun $(xs[j]!) => $acc) (by seam))
      return acc

/-! ## Leaves — each proves its own law once -/

/-- A fixed character. FIRST is the honest proposition `(· = c)`; a single character is
self-delimiting, so FOLLOW = ⊤. -/
def pChar (c : Char) : Biparser (· = c) (fun _ => True) α Unit where
  parse input :=
    match input with
    | [] => none
    | h :: t => if h = c then some ((), t) else none
  print _ := ((), [c])
  firstOk x rest hx := by simp [hx]
  ok a rest _ := by simp

abbrev Digit := {c : Char // c.isDigit}

/-- One digit. FIRST = `isDigit` (the coerced proposition); FOLLOW = ⊤. -/
def pDigit : Biparser (fun c => c.isDigit) (fun _ => True) Digit Digit where
  parse input :=
    match input with
    | [] => none
    | h :: t => if hd : h.isDigit then some (⟨h, hd⟩, t) else none
  print d := (d, [d.val])
  firstOk x rest hx := by simp [hx]
  ok d rest _ := by simp [d.property]

/-! ## The old examples — now correct by construction -/

def pAB : Biparser (· = 'A') (fun _ => True) Unit Unit := gdo
  let _a ← pChar 'A'
  let _b ← pChar 'B'
  return ()

#eval pAB.parse ['A', 'B', 'C'] -- some ((), ['C'])
#eval pAB.print () -- ((), ['A', 'B'])

def pADigitB : Biparser (· = 'A') (fun _ => True) Digit Digit := gdo
  let _a ← pChar 'A'
  let d ← pDigit
  let _b ← pChar 'B'
  return d

#eval pADigitB.parse ['A', '1', 'B', '2'] -- some (⟨'1', _⟩, ['2'])
#eval pADigitB.print ⟨'1', by decide⟩ -- (⟨'1', _⟩, ['A', '1', 'B'])

def pADigitBDigit :
    Biparser (· = 'A') (fun _ => True) (Digit × Digit) (Digit × Digit) := gdo
  let _a ← pChar 'A'
  let d1 ← Biparser.comap Prod.fst pDigit
  let _b ← pChar 'B'
  let d2 ← Biparser.comap Prod.snd pDigit
  let _c ← pChar 'C'
  return (d1, d2)

#eval pADigitBDigit.parse ['A', '5', 'B', '6', 'C', '3'] -- some ((⟨'5', _⟩, ⟨'6', _⟩), ['3'])
#eval pADigitBDigit.print (⟨'5', by decide⟩, ⟨'6', by decide⟩) -- ((…), ['A', '5', 'B', '6', 'C'])

/-! ## Alternation — `Biparser.lean`'s `<|>`, now with the law

The law-free playground's `HOrElse` accepts *any* two biparsers — including overlapping ones,
where the biased choice silently breaks the right branch's round-trip. Here alternation carries
two obligations, and they are exactly why the original example *happens* to behave:

* `hdisj` (`FIRST(q) ⊆ ¬FIRST(p)`): `q`'s printed output starts with a `FIRST(q)` symbol
  (`head_first`), so `firstOk` makes `p` *fail* on it — the choice is deterministic and the right
  branch round-trips. An overlapping alternative shows up as an unprovable `hdisj`.
* `hpnil` (`p.parse [] = none`): this structure has no progress guarantee (nothing forbids
  succeeding on `[]` or printing `[]`), so if `q` printed nothing before an empty continuation,
  `p` could steal the parse. `rfl` for any real parser; a progress-in-the-type design derives it.

This also can't be an `HOrElse` instance anymore — the instance would have to invent the proofs.
That loss *is* the feature. -/

def Biparser.orElse (p : Biparser f₁ fol α β) (q : Biparser f₂ fol α' β')
    (hdisj : ∀ c, f₂ c → ¬ f₁ c) (hpnil : p.parse [] = none) :
    Biparser (fun c => f₁ c ∨ f₂ c) fol (α ⊕ α') (β ⊕ β') where
  parse input :=
    match p.parse input with
    | some (b, rest) => some (Sum.inl b, rest)
    | none =>
      match q.parse input with
      | some (b', rest) => some (Sum.inr b', rest)
      | none => none
  print
    | Sum.inl a  => (Sum.inl (p.print a).1, (p.print a).2)
    | Sum.inr a' => (Sum.inr (q.print a').1, (q.print a').2)
  firstOk c rest hc := by
    show (match p.parse (c :: rest) with
          | some (b, r) => some (Sum.inl b, r)
          | none =>
            match q.parse (c :: rest) with
            | some (b', r) => some (Sum.inr b', r)
            | none => none) = none
    rw [p.firstOk c rest (fun h => hc (Or.inl h)),
        q.firstOk c rest (fun h => hc (Or.inr h))]
  ok a rest hrest := by
    cases a with
    | inl a =>
      show (match p.parse ((p.print a).2 ++ rest) with
            | some (b, r) => some (Sum.inl b, r)
            | none =>
              match q.parse ((p.print a).2 ++ rest) with
              | some (b', r) => some (Sum.inr b', r)
              | none => none) = some (Sum.inl (p.print a).1, rest)
      rw [p.ok a rest hrest]
    | inr a' =>
      have hpnone : p.parse ((q.print a').2 ++ rest) = none := by
        cases hX : (q.print a').2 ++ rest with
        | nil => exact hpnil
        | cons c xs =>
          have hc2 : f₂ c := q.head_first a' rest hrest c (by rw [hX]; rfl)
          exact p.firstOk c xs (hdisj c hc2)
      show (match p.parse ((q.print a').2 ++ rest) with
            | some (b, r) => some (Sum.inl b, r)
            | none =>
              match q.parse ((q.print a').2 ++ rest) with
              | some (b', r) => some (Sum.inr b', r)
              | none => none) = some (Sum.inr (q.print a').1, rest)
      rw [hpnone, q.ok a' rest hrest]

/-! ### The replicated example: `pADigit <|> pDigitB` -/

def pADigit : Biparser (· = 'A') (fun _ => True) Digit Digit := gdo
  let _a ← pChar 'A'
  let d ← pDigit
  return d

def pDigitB : Biparser (fun c => c.isDigit) (fun _ => True) Digit Digit := gdo
  let d ← pDigit
  let _b ← pChar 'B'
  return d

/-- The alternation. `hdisj`: a digit is not `'A'` (`decide`); `hpnil`: `rfl`. -/
def pAAOrDigitB :=
  Biparser.orElse pADigit pDigitB
    (by intro c h hc; subst hc; revert h; decide)
    rfl

#eval pAAOrDigitB.parse ['A', '1', 'C'] -- some (Sum.inl '1', ['C'])
#eval pAAOrDigitB.parse ['3', 'B', 'C'] -- some (Sum.inr '3', ['C'])
#eval pAAOrDigitB.print (Sum.inl ⟨'1', by decide⟩) -- (Sum.inl '1', ['A', '1'])
#eval pAAOrDigitB.print (Sum.inr ⟨'3', by decide⟩) -- (Sum.inr '3', ['3', 'B'])

/-- Both branches round-trip — free. -/
example (v : Digit ⊕ Digit) :
    pAAOrDigitB.parse (pAAOrDigitB.print v).2 = some ((pAAOrDigitB.print v).1, []) :=
  pAAOrDigitB.roundtrip v
