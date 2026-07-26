/-!
# The merge: `RoundTripBiparser` (indexed law) + `CBiparser` (consuming)

FIRST/FOLLOW indices and the bundled round-trip law, **with progress in the type**: the leftover
is strictly shorter. What the merge buys:

* `run_nil` (every parser fails on `[]`) and `print_ne_nil` (printed output is nonempty) are now
  **free theorems** — so `orElse` needs only FIRST-disjointness: the `hpnil` hypothesis of the
  non-consuming version is *gone*.
* Nothing else is lost: `bind`/`gdo`, `comap`, `map`, the leaves, and the free terminal
  `roundtrip` all carry over.

Two proof-engineering consequences of the subtype leftover (the main library's lessons):

* The law is stated in **erased form** — through `.map (fun z => (z.1, z.2.val))` — because a
  `some (value, ⟨rest, proof⟩)` statement would put `rest` under a dependent proof, and rewriting
  the input (e.g. by append-associativity in `bind`) would break the motive. Erased, the equation's
  type doesn't mention the input, and every rewrite is clean.
* Composite parsers get **named** parse functions (`bindParse`, `orElseParse`): rewriting the input
  of an applied function has a trivially type-correct motive; an inline `match` does not.

Remaining delta to the real `IsoParser`: fuse source and value (`α = β`, plus the annotation
family) so misalignment is unrepresentable.
-/

/-- The FOLLOW condition: `rest` is empty, or its head is admissible. Vacuous at `[]`. -/
def HeadIn (f : Char → Prop) (rest : List Char) : Prop :=
  ∀ c, rest.head? = some c → f c

structure Biparser (fst fol : Char → Prop) (α β : Type) where
  parse : (input : List Char) → Option (β × { r : List Char // r.length < input.length })
  print : α → β × List Char
  /-- FIRST is sound: outside it, the parse fails. -/
  firstOk : ∀ c rest, ¬ fst c → parse (c :: rest) = none
  /-- **The law**, in erased form (the subtype stays out of every proof). -/
  ok : ∀ a rest, HeadIn fol rest →
    (parse ((print a).2 ++ rest)).map (fun z => (z.1, z.2.val)) = some ((print a).1, rest)

/-- Recover the raw parse result (with its progress witness) from an erased equation. -/
theorem run_eq_some {p : Biparser fst fol α β} {input : List Char} {b : β} {rest : List Char}
    (h : (p.parse input).map (fun z => (z.1, z.2.val)) = some (b, rest)) :
    ∃ r : { r : List Char // r.length < input.length },
      p.parse input = some (b, r) ∧ r.val = rest := by
  cases hp : p.parse input with
  | none => rw [hp] at h; simp at h
  | some z =>
    obtain ⟨b', r⟩ := z
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨r, rfl, rfl⟩

/-- **Free now**: every consuming parser fails on `[]` (a success would need a shorter-than-empty
leftover). In the non-consuming version this was `orElse`'s assumed `hpnil`. -/
theorem Biparser.run_nil (p : Biparser fst fol α β) : p.parse [] = none := by
  match hp : p.parse [] with
  | none => rfl
  | some (b, ⟨r, hr⟩) => exact absurd hr (by simp)

/-- **The payoff, terminally**: at end of input the FOLLOW guard is vacuous. -/
theorem Biparser.roundtrip (p : Biparser fst fol α β) (a : α) :
    (p.parse (p.print a).2).map (fun z => (z.1, z.2.val)) = some ((p.print a).1, []) := by
  have h := p.ok a [] (fun c hc => absurd hc (by simp))
  -- Rewrite `++ []` away *first*, while the statement is still in erased form (input-independent
  -- type, clean motive). A `simpa` would introduce a dependent ∃-binder before getting there.
  rwa [List.append_nil] at h

/-- **Free now**: a printed output is never empty — printing then parsing succeeds (`ok`), but
every parse of `[]` fails (`run_nil`). -/
theorem Biparser.print_ne_nil (p : Biparser fst fol α β) (a : α) : (p.print a).2 ≠ [] := by
  intro h
  have hok := p.roundtrip a
  rw [h, p.run_nil] at hok
  simp at hok

/-- A printed output (with admissible continuation) starts with a FIRST symbol — derived, as
before; with `print_ne_nil` the head now always comes from the printed output. -/
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
    simp at hok

/-- Adapt the source — untouched by consuming. -/
def Biparser.comap (g : α' → α) (p : Biparser fst fol α β) : Biparser fst fol α' β where
  parse := p.parse
  print a' := p.print (g a')
  firstOk := p.firstOk
  ok a' rest h := p.ok (g a') rest h

/-- Map the value; the leftover (and its progress proof) pass through. -/
def Biparser.map (f : β → γ) (p : Biparser fst fol α β) : Biparser fst fol α γ where
  parse input := (p.parse input).map (fun br => (f br.1, br.2))
  print a := (f (p.print a).1, (p.print a).2)
  firstOk c rest hc := by rw [p.firstOk c rest hc]; rfl
  ok a rest h := by
    obtain ⟨r, hp, hv⟩ := run_eq_some (p.ok a rest h)
    show ((p.parse ((p.print a).2 ++ rest)).map _).map _ = _
    rw [hp]
    simp [hv]

/-- The composite parse, **named** so that rewriting its input has a clean motive. Progress
composes by transitivity. -/
def bindParse (p : Biparser f₁ fo₁ α β) (k : β → Biparser f₂ fo₂ α γ) :
    (input : List Char) → Option (γ × { r : List Char // r.length < input.length }) :=
  fun input =>
    match p.parse input with
    | none => none
    | some (b, r) =>
      match (k b).parse r.val with
      | none => none
      | some (c, r') => some (c, ⟨r'.val, Nat.lt_trans r'.property r.property⟩)

/-- Bind, with the seam — unchanged from the non-consuming version, except the law proof works in
erased form: state `k`'s law *at `r₁.val`* (transported at the erased level, where nothing is
dependent), then compute. -/
def Biparser.bind (p : Biparser f₁ fo₁ α β) (k : β → Biparser f₂ fo₂ α γ)
    (hseam : ∀ c, f₂ c → fo₁ c) : Biparser f₁ fo₂ α γ where
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
    obtain ⟨r1, hp1, hv1⟩ := run_eq_some (p.ok a _ h1)
    have hkrun : ((k (p.print a).1).parse r1.val).map (fun z => (z.1, z.2.val))
        = some (((k (p.print a).1).print a).1, rest) := by
      rw [hv1]; exact (k (p.print a).1).ok a rest hrest
    obtain ⟨r2, hp2, hv2⟩ := run_eq_some hkrun
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

/-! ## `gdo` — unchanged -/

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

/-! ## Leaves -/

def pChar (c : Char) : Biparser (· = c) (fun _ => True) α Unit where
  parse input :=
    match input with
    | [] => none
    | h :: t => if h = c then some ((), ⟨t, by simp⟩) else none
  print _ := ((), [c])
  firstOk x rest hx := by simp [hx]
  ok a rest _ := by simp

abbrev Digit := {c : Char // c.isDigit}

def pDigit : Biparser (fun c => c.isDigit) (fun _ => True) Digit Digit where
  parse input :=
    match input with
    | [] => none
    | h :: t => if hd : h.isDigit then some (⟨h, hd⟩, ⟨t, by simp⟩) else none
  print d := (d, [d.val])
  firstOk x rest hx := by simp [hx]
  ok d rest _ := by simp [d.property]

/-! ## The examples -/

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

/-! ## Alternation — `hpnil` is GONE

The non-consuming version needed `hpnil : p.parse [] = none` because `q` might print nothing
before an empty continuation. Now `print_ne_nil` guarantees `q`'s output has a head, so the only
obligation left is the one alternation deserves: FIRST-disjointness. -/

def orElseParse (p : Biparser f₁ fol α β) (q : Biparser f₂ fol α' β') :
    (input : List Char) → Option ((β ⊕ β') × { r : List Char // r.length < input.length }) :=
  fun input =>
    match p.parse input with
    | some (b, r) => some (Sum.inl b, r)
    | none =>
      match q.parse input with
      | some (b', r) => some (Sum.inr b', r)
      | none => none

def Biparser.orElse (p : Biparser f₁ fol α β) (q : Biparser f₂ fol α' β')
    (hdisj : ∀ c, f₂ c → ¬ f₁ c) :
    Biparser (fun c => f₁ c ∨ f₂ c) fol (α ⊕ α') (β ⊕ β') where
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
      obtain ⟨r, hp, hv⟩ := run_eq_some (p.ok a rest hrest)
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
      obtain ⟨r, hq, hv⟩ := run_eq_some (q.ok a' rest hrest)
      show (orElseParse p q ((q.print a').2 ++ rest)).map (fun z => (z.1, z.2.val))
          = some (Sum.inr (q.print a').1, rest)
      simp only [orElseParse]
      rw [hpnone, hq]
      simp [hv]

/-! ### The replicated example -/

def pADigit : Biparser (· = 'A') (fun _ => True) Digit Digit := gdo
  let _a ← pChar 'A'
  let d ← pDigit
  return d

def pDigitB : Biparser (fun c => c.isDigit) (fun _ => True) Digit Digit := gdo
  let d ← pDigit
  let _b ← pChar 'B'
  return d

/-- Only `hdisj` left — the `rfl` that used to discharge `hpnil` is not even a parameter. -/
def pAAOrDigitB :=
  Biparser.orElse pADigit pDigitB
    (by intro c h hc; subst hc; revert h; decide)

#eval pAAOrDigitB.parse ['A', '1', 'C'] -- some (Sum.inl '1', ['C'])
#eval pAAOrDigitB.parse ['3', 'B', 'C'] -- some (Sum.inr '3', ['C'])
#eval pAAOrDigitB.parse [] -- none  (free: `run_nil`)
#eval pAAOrDigitB.print (Sum.inl ⟨'1', by decide⟩) -- (Sum.inl '1', ['A', '1'])
#eval pAAOrDigitB.print (Sum.inr ⟨'3', by decide⟩) -- (Sum.inr '3', ['3', 'B'])

/-- Both branches round-trip — free. -/
example (v : Digit ⊕ Digit) :
    (pAAOrDigitB.parse (pAAOrDigitB.print v).2).map (fun z => (z.1, z.2.val))
      = some ((pAAOrDigitB.print v).1, []) :=
  pAAOrDigitB.roundtrip v

/-! ## `fix` — recursion **with the law**

The recursor cannot be a law-carrying `Biparser` (its law would only hold on shorter inputs;
bundling a partial law leaks a `sorry` — the lesson from `CParser`/`CBiparser`, where `fix` was
possible only *because* those are law-free). The honest design:

* the body is a **proof-free parse transformer** (`FixBody`), with the shortness guard inside the
  recursor — so ill-founded calls fail rather than loop, and no partial law is ever bundled;
* `print` is supplied as a plain **total function** — its recursion is the user's own (structural
  on the source), so unlike `CBiparser.fix` there is no `μ` and no junk fallback;
* the user proves **one step-law** (`hok`): *if the recursor satisfies the round-trip on strictly
  shorter print-inputs, the body satisfies it* — and `fix` runs the strong induction once,
  generically.

So the induction that `RoundTripBiparser`'s `pParens` had to do by hand is paid once, here; each
grammar pays only its one-layer step. This is the library's `fix2` (`IsoParser/Fix.lean`), minus
the exactness half (this structure's law is one-directional). -/

/-- A recursion body: one grammar layer, with a proof-free recursor (guard internalized). -/
abbrev FixBody (β : Type) :=
  (input : List Char) →
    ((input' : List Char) → Option (β × { r : List Char // r.length < input'.length })) →
    Option (β × { r : List Char // r.length < input.length })

-- `h` reads as unused: it is consumed only in `decreasing_by`.
set_option linter.unusedVariables false in
def fixParse (body : FixBody β) :
    (input : List Char) → Option (β × { r : List Char // r.length < input.length })
  | input => body input (fun input' =>
      if h : input'.length < input.length then fixParse body input' else none)
termination_by input => input.length
decreasing_by exact h

/-- **The induction, paid once**: the step-law `hok` propagates the round-trip through the
fixpoint, by strong induction on the input length. -/
theorem fixParse_run (body : FixBody β) (print : α → β × List Char)
    (hok : ∀ (a : α) (rest : List Char)
      (rec : (input' : List Char) → Option (β × { r : List Char // r.length < input'.length })),
      HeadIn fol rest →
      (∀ (a' : α) (rest' : List Char),
          ((print a').2 ++ rest').length < ((print a).2 ++ rest).length → HeadIn fol rest' →
          (rec ((print a').2 ++ rest')).map (fun z => (z.1, z.2.val)) = some ((print a').1, rest')) →
      (body ((print a).2 ++ rest) rec).map (fun z => (z.1, z.2.val)) = some ((print a).1, rest)) :
    ∀ (n : Nat) (a : α) (rest : List Char), ((print a).2 ++ rest).length = n → HeadIn fol rest →
      (fixParse body ((print a).2 ++ rest)).map (fun z => (z.1, z.2.val))
        = some ((print a).1, rest) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a rest hn hr
    rw [fixParse]
    apply hok a rest _ hr
    intro a' rest' hlt hr'
    simp only [dif_pos hlt]
    exact ih ((print a').2 ++ rest').length (hn ▸ hlt) a' rest' rfl hr'

/-- **The law-carrying fixpoint.** -/
def Biparser.fix (body : FixBody β) (print : α → β × List Char)
    (hfirst : ∀ (c : Char) (rest : List Char) rec, ¬ fst c → body (c :: rest) rec = none)
    (hok : ∀ (a : α) (rest : List Char)
      (rec : (input' : List Char) → Option (β × { r : List Char // r.length < input'.length })),
      HeadIn fol rest →
      (∀ (a' : α) (rest' : List Char),
          ((print a').2 ++ rest').length < ((print a).2 ++ rest).length → HeadIn fol rest' →
          (rec ((print a').2 ++ rest')).map (fun z => (z.1, z.2.val)) = some ((print a').1, rest')) →
      (body ((print a).2 ++ rest) rec).map (fun z => (z.1, z.2.val)) = some ((print a).1, rest)) :
    Biparser fst fol α β where
  parse := fixParse body
  print := print
  firstOk c rest hc := by rw [fixParse, hfirst c rest _ hc]
  ok a rest hr := fixParse_run body print hok ((print a).2 ++ rest).length a rest rfl hr

/-! ### The demo: `P ::= 'a' | '(' P ')'`, through `fix`, law included -/

/-- All the elements are equal, so a trailing copy commutes to the front. -/
theorem replicate_cons_comm (n : Nat) (a : α) (l : List α) :
    List.replicate n a ++ (a :: l) = a :: (List.replicate n a ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- The canonical string at depth `n` — the print side, **structurally** recursive on the source
(this is why `fix` needs no print-side measure). -/
def wrap (n : Nat) : List Char :=
  List.replicate n '(' ++ ('a' :: List.replicate n ')')

/-- Peeling one nesting level, pre-associated into `print ++ continuation` shape. -/
theorem wrap_succ (n : Nat) (rest : List Char) :
    wrap (n + 1) ++ rest = '(' :: (wrap n ++ (')' :: rest)) := by
  simp [wrap, List.replicate_succ, List.append_assoc, replicate_cons_comm]

/-- One grammar layer, proof-free recursor. -/
def parensBody : FixBody Nat := fun input rec =>
  match input with
  | [] => none
  | c :: rest =>
    if c = 'a' then some (0, ⟨rest, by simp⟩)
    else if c = '(' then
      match rec rest with
      | some (n, r) =>
        match hr : r.val with
        | ')' :: r2 => some (n + 1, ⟨r2, by
            have h0 := r.property; rw [hr] at h0
            simp only [List.length_cons] at h0 ⊢; omega⟩)
        | _ => none
      | none => none
    else none

/-- **Nested parens, with the round-trip law** — the step-law is one layer of the induction that
`RoundTripBiparser`'s standalone `pParens` proof did wholesale. -/
def pParens : Biparser (fun c => c = 'a' ∨ c = '(') (fun _ => True) Nat Nat :=
  Biparser.fix parensBody (fun n => (n, wrap n))
    (hfirst := by
      intro c rest rec hc
      have h1 : ¬ c = 'a' := fun h => hc (Or.inl h)
      have h2 : ¬ c = '(' := fun h => hc (Or.inr h)
      simp only [parensBody]; rw [if_neg h1, if_neg h2])
    (hok := by
      intro a rest rec _ hrec
      cases a with
      | zero =>
        show (parensBody ('a' :: rest) rec).map (fun z => (z.1, z.2.val)) = some (0, rest)
        simp [parensBody]
      | succ m =>
        show (parensBody (wrap (m + 1) ++ rest) rec).map (fun z => (z.1, z.2.val))
          = some (m + 1, rest)
        rw [wrap_succ]
        simp only [parensBody]
        rw [if_neg (by decide)]; simp only [if_true]
        have hq : (rec (wrap m ++ (')' :: rest))).map (fun z => (z.1, z.2.val))
            = some (m, ')' :: rest) :=
          hrec m (')' :: rest)
            (by simp only [wrap, List.length_append, List.length_cons,
                  List.length_replicate]; omega)
            (by intro c _; trivial)
        rcases hrc : rec (wrap m ++ (')' :: rest)) with _ | ⟨n', r0⟩
        · rw [hrc] at hq; simp at hq
        · rw [hrc] at hq
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
          obtain ⟨rfl, hrv⟩ := hq
          obtain ⟨r0v, r0lt⟩ := r0
          subst hrv
          rfl)

#eval pParens.parse "a".toList      -- some (0, [])
#eval pParens.parse "((a))".toList  -- some (2, [])
#eval pParens.parse "((a)".toList   -- none
#eval pParens.print 3               -- (3, ['(', '(', '(', 'a', ')', ')', ')'])

/-- The round-trip — a **theorem** now (compare `CBiparser`'s `pParens`, where the same green
`#eval` was observation only). -/
example (n : Nat) :
    (pParens.parse (pParens.print n).2).map (fun z => (z.1, z.2.val))
      = some ((pParens.print n).1, []) :=
  pParens.roundtrip n

/-- And the fix-built parser composes with `gdo` like any other law-carrying piece. -/
def pBracketParens : Biparser (· = '[') (fun _ => True) Nat Nat := gdo
  let _o ← pChar '['
  let n ← pParens
  let _c ← pChar ']'
  return n

#eval pBracketParens.parse "[((a))]".toList -- some (2, [])

example (n : Nat) :
    (pBracketParens.parse (pBracketParens.print n).2).map (fun z => (z.1, z.2.val))
      = some ((pBracketParens.print n).1, []) :=
  pBracketParens.roundtrip n
