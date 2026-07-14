import LambdaLab.Playground.RoundTripBiparser

/-!
# `Bip` — the round-trip law in the structure

`RoundTripBiparser.lean` proves the law, but pays for it the way the *original* parser paid
for termination: a predicate (`RoundTrips`) beside the code, a parameter (`F`) threaded
through every lemma, and a hand-written assembly proof per grammar. That is exactly the
`Progresses`/`NonGrowing` anti-pattern that progress-in-the-type eliminated.

So: apply the same medicine a fourth time. **Bundle the law into the structure and let the
combinators compute the FOLLOW.**

Two facts make it work, and both are gifts from the existing design:

* `first (p >>= k) = first p` — because every `CBiparser` provably consumes ≥1 character, the
  first character of a sequence is always its head's. So FIRST is trivially compositional.
* `p.run [] = none` for **every** `CBiparser` — provably, because the leftover must be a
  *strict* suffix of `[]` and no list is shorter than `[]`. This is what discharges the
  top-level FOLLOW *for free*, killing the `*_run_nil` lemmas.

The payoff is `Bip.roundtrip`: **every** `Bip` round-trips terminally, with no side-condition
and no per-grammar proof. Building the grammar out of combinators *is* the proof. The only
obligations left are the seams — and those are the genuine content ("this grammar is
unambiguous"), now one-line lexical facts demanded at the use site.
-/

/-- A FOLLOW condition, as a character class: only the *first* character of the continuation
ever matters (every `F` in `RoundTripBiparser` turned out to be of this shape). Vacuously
true at `[]` — which is precisely why end-of-input needs no proof. -/
def HeadIn (f : Char → Bool) (rest : List Char) : Prop :=
  ∀ c, rest.head? = some c → f c = true

@[simp] theorem HeadIn_nil (f : Char → Bool) : HeadIn f [] := by
  intro c hc; simp at hc

/-- `RoundTrips` is antitone in `F`: a *stronger* FOLLOW admits fewer continuations. -/
theorem RoundTrips_mono {p : CBiparser w v} {F F' : List Char → Prop}
    (h : ∀ rest, F' rest → F rest) (hp : RoundTrips p F) : RoundTrips p F' :=
  fun s rest hF' => hp s rest (h rest hF')

/-- **Every `CBiparser` fails on empty input** — and this is a *theorem*, not an assumption:
its leftover must satisfy `r.length < [].length = 0`, which nothing does. Progress-in-the-type
paying for the round-trip layer. -/
theorem run_nil (p : CBiparser w v) : p.run [] = none := by
  simp only [CBiparser.run]
  rcases h : p.parse [] with _ | ⟨a, r, hr⟩
  · rfl
  · exact absurd hr (by simp)

/-- A biparser carrying its own round-trip law, plus the character classes needed to compute
seams. `first`/`follow` are computed by the combinators; `ok` rides along and is never
threaded through a proof. -/
structure Bip (w v : Type) where
  bp      : CBiparser w v
  first   : Char → Bool
  follow  : Char → Bool
  /-- FIRST is sound: outside it, the parse fails. -/
  firstOk : ∀ (c : Char) (rest : List Char), first c = false → bp.run (c :: rest) = none
  /-- The law, bundled. -/
  ok      : RoundTrips bp (HeadIn follow)

/-- Nothing outside FIRST parses — *including* the empty input, by `run_nil`. -/
theorem Bip.noParse (p : Bip w v) (rest : List Char)
    (h : ∀ c, rest.head? = some c → p.first c = false) : p.bp.run rest = none := by
  cases rest with
  | nil => exact run_nil _
  | cons c cs => exact p.firstOk c cs (h c rfl)

/-- **The payoff.** Every `Bip` round-trips terminally: print any source, parse it back, get
the value with nothing left over. No side-conditions, no per-grammar proof — `HeadIn f []` is
vacuous, so the FOLLOW is discharged at end-of-input. -/
theorem Bip.roundtrip (p : Bip w v) (s : w) :
    p.bp.run (p.bp.print s).2 = some ((p.bp.print s).1, []) := by
  have h := p.ok s [] (HeadIn_nil _)
  simpa using h

/-- A printed output always starts with a character in FIRST — derived from `ok` + `firstOk`,
not assumed. This is what lets `bSeq` discharge its seam. -/
theorem Bip.head_first (q : Bip w v) (s : w) (rest : List Char)
    (hrest : HeadIn q.follow rest) (c : Char)
    (hc : ((q.bp.print s).2 ++ rest).head? = some c) : q.first c = true := by
  cases hfc : q.first c with
  | true => rfl
  | false =>
      exfalso
      have hnone : q.bp.run ((q.bp.print s).2 ++ rest) = none := by
        apply Bip.noParse
        intro c' hc'
        rw [hc] at hc'
        exact (Option.some.inj hc') ▸ hfc
      rw [q.ok s rest hrest] at hnone
      exact absurd hnone (by simp)

/-! ## Leaves — each computes its own `first`/`follow` -/

/-- A fixed char: consumes exactly one, so **self-delimiting** (`follow = ⊤`). -/
def bChar (c : Char) : Bip w Char where
  bp := pChar1 c
  first := (· == c)
  follow := fun _ => true
  firstOk := by
    intro c' rest h
    have hne : ¬ (c' = c) := by simpa using h
    simp [CBiparser.run, pChar1, hne]
  ok := RoundTrips_mono (fun _ _ => trivial) (RoundTrips_pChar1 c)

/-- A digit. `first` is *defined* as "`ofChar?` succeeds", which makes `firstOk` immediate. -/
def bDigit : Bip Digit Digit where
  bp := digit1
  first := fun c => (Digit.ofChar? c).isSome
  follow := fun _ => true
  firstOk := by
    intro c rest h
    have hnone : Digit.ofChar? c = none := by
      cases hc : Digit.ofChar? c with
      | none => rfl
      | some d => rw [hc] at h; simp at h
    simp [CBiparser.run, digit1, hnone]
  ok := RoundTrips_mono (fun _ _ => trivial) RoundTrips_digit1

/-- Whitespace is **greedy**, so it is the one leaf with a nontrivial FOLLOW. -/
def bWs : Bip w Unit where
  bp := ws1
  first := Char.isWhitespace
  follow := fun c => !c.isWhitespace
  firstOk := by
    intro c rest h
    simp [CBiparser.run, ws1, h]
  ok := RoundTrips_mono (fun _ hr c hc => by simpa using hr c hc) RoundTrips_ws1

/-! ## Combinators — the law is rebuilt, never re-proved -/

def bMap (f : v → v') (p : Bip w v) : Bip w v' where
  bp := f <$> p.bp
  first := p.first
  follow := p.follow
  firstOk := by
    intro c rest h
    simp [map_run, p.firstOk c rest h]
  ok := RoundTrips_map f p.bp _ p.ok

/-- Sequencing. Its **one** obligation is the seam: whatever `q` can start with must be
something `p` is allowed to be followed by. That is the grammar's unambiguity, and it is the
only thing the user ever supplies. -/
def bSeq (p : Bip w v) (q : Bip w v')
    (hseam : ∀ c, q.first c = true → p.follow c = true) : Bip w (v × v') where
  bp := p.bp >>= fun a => (fun b => (a, b)) <$> q.bp
  first := p.first
  follow := q.follow
  firstOk := by
    intro c rest h
    simp [bind_run, p.firstOk c rest h]
  ok := by
    refine RoundTrips_bind p.bp _ (HeadIn q.follow) (HeadIn p.follow) p.ok
      (fun a => RoundTrips_map _ _ _ q.ok) ?_
    intro s rest hrest c hc
    simp only [map_print] at hc
    exact hseam c (q.head_first s rest hrest c hc)

/-- One-or-more. FOLLOW gains the seam: the continuation may not start *another element*
(`!p.first`). The `hrep` obligation says an element's own output may follow an element —
i.e. elements are repeatable — which is trivial whenever `p` is self-delimiting. -/
def bMany1 (p : Bip w v)
    (hrep : ∀ (s : w) (c : Char), ((p.bp.print s).2).head? = some c → p.follow c = true) :
    Bip (NEList w) (List v) where
  bp := many1NE p.bp
  first := p.first
  follow := fun c => p.follow c && !p.first c
  firstOk := by
    intro c rest h
    rw [many1NE_run_eq, p.firstOk c rest h]
  ok := by
    have hclosed : ∀ (s : w) (r : List Char),
        HeadIn p.follow r → HeadIn p.follow ((p.bp.print s).2 ++ r) := by
      intro s r hr c hc
      cases hout : (p.bp.print s).2 with
      | nil => rw [hout] at hc; simp at hc; exact hr c hc
      | cons c0 cs =>
          rw [hout] at hc; simp at hc
          exact hc ▸ hrep s c0 (by rw [hout]; rfl)
    refine RoundTrips_mono ?_ (RoundTrips_many1NE p.bp (HeadIn p.follow) p.ok hclosed)
    intro rest hr
    refine ⟨fun c hc => ?_, ?_⟩
    · have := hr c hc; simpa using (Bool.and_eq_true .. |>.mp this).1
    · apply Bip.noParse
      intro c hc
      have := hr c hc
      simpa using (Bool.and_eq_true .. |>.mp this).2

/-! ## The grammar — and the round-trip falls out with no assembly proof

The whole development below is *definitions plus three lexical facts*. There is no
`RoundTrips_*` proof anywhere: the law was rebuilt by the combinators. -/

/-- Whitespace is never a digit. (`Char.isWhitespace` is a three-way test, so this is a
case split, not an appeal to a million-element `decide`.) -/
theorem ws_not_digit (c : Char) (h : c.isWhitespace = true) : Digit.ofChar? c = none := by
  simp only [Char.isWhitespace] at h
  simp only [Bool.or_eq_true, decide_eq_true_iff] at h
  rcases h with ((rfl | rfl) | rfl) | rfl <;> rfl

/-- A non-empty digit run. -/
def bDigits : Bip (Digit × List Digit) (List Digit) :=
  bMany1 bDigit (by intro _ _ _; rfl)          -- `bDigit.follow = ⊤`

/-- One element: digits, ≥1 whitespace, `;`. The two `bSeq` seams are the grammar's entire
unambiguity argument. -/
def bElem : Bip (Digit × List Digit) (List Digit) :=
  bMap (fun ((l, _), _) => l) <|
    bSeq
      (bSeq bDigits bWs
        -- seam: whitespace may follow a digit run, because whitespace is not a digit
        (by intro c hc; simp [bDigits, bMany1, bDigit, ws_not_digit c hc]))
      (bChar ';')
      -- seam: `;` may follow whitespace, because `;` is not whitespace
      (by intro c hc
          simp only [bChar] at hc
          have hcc : c = ';' := by simpa using hc
          subst hcc
          simp [bSeq, bWs])

/-- The whole grammar. -/
def bLists : Bip ((Digit × List Digit) × List (Digit × List Digit)) (List (List Digit)) :=
  bMany1 bElem (by intro _ _ _; rfl)           -- `bElem.follow = ⊤` (it ends in `;`)

/-- **The end-to-end round-trip — one line.** Compare `roundtrip_pDigitListsB`, which needed
`RoundTrips_pElem`, `RoundTrips_pDigitListsB`, and three `*_run_nil` lemmas to assemble. -/
theorem bLists_roundtrip (s : (Digit × List Digit) × List (Digit × List Digit)) :
    bLists.bp.run (bLists.bp.print s).2 = some ((bLists.bp.print s).1, []) :=
  bLists.roundtrip s

#eval (bLists.bp.print ((.d1, [.d2]), [(.d3, [])])).2
#eval bLists.bp.run "12 ;3 ;".toList
