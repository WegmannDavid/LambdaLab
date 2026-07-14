import LambdaLab.Playground.Biparser
import LambdaLab.NEList

/-!
# A round-trip law for `CBiparser`

The naive law — "printing any source and re-parsing recovers it" — is **false**, for two
independent reasons:

1. **Invalid sources.** `digit1`'s source *used to be* `Char`, but only *digits* round-trip:
   `print 'x'` emitted `"x"`, which the parser rejects. The source type was wider than the
   printable set. (Now fixed at the root — see below.)
2. **The greedy seam.** `many1` is greedy, so `parse (print xs ++ print ys)` reads
   `xs ++ ys` as one longer list. Appending another valid element breaks it.

This file fences off both, with one design decision per failure:

* **(1) → restrict the source *type*.** `digit1`'s source is an *inductive* `Digit`, so `'x'`
  is not merely excluded but **unrepresentable**. No well-formedness predicate is threaded
  through any proof — the invariant is in the type. The same medicine cures the same disease
  one level up: `many1`'s `List w` source is too wide (it never *parses* an empty list), so
  `many1NE` sources from `w × List w` — non-empty by construction. That is what makes the
  seam lemma provable at all.
* **(2) → a `FOLLOW` parameter `F`.** Unavoidable for greedy repetition. It is a
  *parameter*, so one law serves both self-delimiting biparsers (`F = ⊤`) and greedy ones.

The law itself is the paper's **weak backward round-tripping**: it compares against the
printer's *own output value* `(p.print s).1`, which is exactly what makes `RoundTrips_bind`
a rewrite instead of a case-split — i.e. what makes the law **compositional**. Each
combinator's lemma is proved *once*; every biparser built from them inherits its law, so
adding a biparser is a local proof and never a global edit.
-/

/-- The parse result with the progress proof erased. Stating the law against `run` (not
`parse`) keeps `{r // r.length < _}` out of every proof — proof irrelevance means the
subtype adds nothing to the law, only noise. -/
def CBiparser.run (p : CBiparser w v) (input : List Char) : Option (v × List Char) :=
  (p.parse input).map (fun (a, r) => (a, r.val))


/-- **The law.** `p` round-trips with respect to a continuation predicate `F` ("what may
legally follow") when: printing any source, appending any `F`-admissible continuation, and
re-parsing recovers the printed value and hands the continuation back untouched.

`F` is the FOLLOW condition. Self-delimiting biparsers take `F = fun _ => True`; greedy ones
(`ws1`, `many1`) need an `F` that forbids the continuation from extending their parse. -/
def RoundTrips (p : CBiparser w v) (F : List Char → Prop) : Prop :=
  ∀ (s : w) (rest : List Char), F rest →
    p.run ((p.print s).2 ++ rest) = some ((p.print s).1, rest)

/-! ## Leaves -/

/-- A fixed char consumes exactly one char, so it is **self-delimiting**: `F = ⊤`. -/
theorem RoundTrips_pChar1 (c : Char) : RoundTrips (pChar1 c : CBiparser w Char) (fun _ => True) := by
  intro _ rest _
  simp [CBiparser.run, pChar1]

/-! `Digit` and `digit1` now live in `Biparser.lean` — the source restriction was pushed down
into the base development, so the too-wide `Char` source no longer exists anywhere. -/

/-- The char-level round-trip: 10 cases, all `rfl`. This is the *only* place digit-validity is
ever discussed; everything downstream inherits it from the `Digit` type. -/
theorem Digit.ofChar?_toChar (d : Digit) : Digit.ofChar? d.toChar = some d := by
  cases d <;> rfl

/-- One char consumed ⇒ self-delimiting ⇒ `F = ⊤`. Because the source is `Digit`, the bad
source `'x'` is unrepresentable and the law needs no side-condition. -/
theorem RoundTrips_digit1 : RoundTrips digit1 (fun _ => True) := by
  intro d rest _
  simp [CBiparser.run, digit1, Digit.ofChar?_toChar]

/-- `dropWhile` is the identity when the list doesn't start with a `p`-char. -/
theorem dropWhile_eq_self {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ c, l.head? = some c → p c = false) : l.dropWhile p = l := by
  cases l with
  | nil => simp
  | cons hd tl => simp [List.dropWhile, h hd (by simp)]

/-- The FOLLOW condition for whitespace: the continuation must not begin with whitespace,
else `ws1`'s greedy `dropWhile` eats into it. -/
def NoLeadWs (rest : List Char) : Prop :=
  ∀ c, rest.head? = some c → c.isWhitespace = false

/-- `ws1` is **greedy**, so it is the first leaf needing a real `F`. -/
theorem RoundTrips_ws1 : RoundTrips (ws1 : CBiparser w Unit) NoLeadWs := by
  intro _ rest hF
  simp only [CBiparser.run, ws1, List.singleton_append]
  rw [if_pos (by decide : (' ' : Char).isWhitespace = true)]
  simp [dropWhile_eq_self Char.isWhitespace rest hF]

/-! ## Compositional core — proved once, inherited by every biparser built from them.

Each combinator gets the *same* two-lemma treatment: a `_print` equation (how printing
decomposes) and a `_run` equation (how parsing decomposes, **at the erased level** — no
subtypes). Every `RoundTrips_*` proof below is then a plain rewrite chain against those.
Keeping this uniform is what keeps the proofs short: the moment one combinator reaches back
into `parse` and its `{r // r.length < _}`, its proof balloons. -/

theorem map_print (f : v → v') (p : CBiparser w v) (s : w) :
    (f <$> p).print s = (f (p.print s).1, (p.print s).2) := rfl

theorem map_run (f : v → v') (p : CBiparser w v) (input : List Char) :
    (f <$> p).run input = (p.run input).map (fun (a, r) => (f a, r)) := by
  simp only [CBiparser.run, Functor.map]
  cases p.parse input <;> rfl

theorem RoundTrips_map (f : v → v') (p : CBiparser w v) (F : List Char → Prop)
    (hp : RoundTrips p F) : RoundTrips (f <$> p) F := by
  intro s rest hF
  simp [map_print, map_run, hp s rest hF]

theorem bind_print (p : CBiparser w v) (k : v → CBiparser w v') (s : w) :
    (p >>= k).print s =
      (((k (p.print s).1).print s).1, (p.print s).2 ++ ((k (p.print s).1).print s).2) := by
  simp only [Bind.bind]

theorem bind_run (p : CBiparser w v) (k : v → CBiparser w v') (input : List Char) :
    (p >>= k).run input =
      match p.run input with
      | none => none
      | some (a, r) => (k a).run r := by
  simp only [CBiparser.run, Bind.bind]
  rcases hp : p.parse input with _ | ⟨a, r, hr⟩
  · simp
  · rcases hk : (k a).parse r with _ | ⟨b, r', hr'⟩ <;> simp [hk]

/-- **The compositional heart.** `p >>= k` round-trips at `F` provided
* `p` round-trips at `Fp`,
* every `k a` round-trips at `F`, and
* `Fp` holds of *`k`'s output followed by an `F`-continuation* — i.e. `k`'s printed output
  is an admissible FOLLOW for `p`. This is where the seam is discharged, once. -/
theorem RoundTrips_bind (p : CBiparser w v) (k : v → CBiparser w v')
    (F Fp : List Char → Prop)
    (hp : RoundTrips p Fp)
    (hk : ∀ a, RoundTrips (k a) F)
    (hseam : ∀ (s : w) (rest : List Char), F rest →
        Fp (((k (p.print s).1).print s).2 ++ rest)) :
    RoundTrips (p >>= k) F := by
  intro s rest hF
  have h1 := hp s (((k (p.print s).1).print s).2 ++ rest) (hseam s rest hF)
  have h2 := hk (p.print s).1 s rest hF
  rw [bind_print, bind_run, List.append_assoc, h1]
  exact h2

/-! ## The greedy repetition seam — and the non-empty-source fix

`many1`'s source `List w` is **too wide**: `many1` never *parses* an empty list, so `us = []`
falsifies any round-trip law. That is failure mode (1) again, one level up, and it takes the
same medicine — restrict the source type. `many1NE` sources from `w × List w`: a head plus a
tail, i.e. a non-empty list *by construction*. With that, the seam lemma goes through. -/

def many1NE (p : CBiparser w α) : CBiparser (NEList w) (List α) where
  parse := many1Parse p
  print := fun (u, us) => many1Print p (u :: us)

/-! How `many1`'s printer decomposes. All three are `rfl`. They are deliberately NOT `@[simp]`:
simp would decompose `many1Print p (u' :: us')` recursively, but that folded term is exactly
what the induction hypothesis below is stated about, so `ih` would stop matching. -/

theorem many1Print_nil (p : CBiparser w α) : many1Print p [] = ([], []) := rfl

theorem many1Print_cons_fst (p : CBiparser w α) (v : w) (vs : List w) :
    (many1Print p (v :: vs)).1 = (p.print v).1 :: (many1Print p vs).1 := rfl

theorem many1Print_cons_snd (p : CBiparser w α) (v : w) (vs : List w) :
    (many1Print p (v :: vs)).2 = (p.print v).2 ++ (many1Print p vs).2 := rfl

theorem many1Parse_eq (p : CBiparser w α) (input : List Char) :
    many1Parse p input =
      match p.parse input with
      | none => none
      | some (a, ⟨r, hr⟩) =>
          match many1Parse p r with
          | none => some ([a], ⟨r, hr⟩)
          | some (as, ⟨r', hr'⟩) => some (a :: as, ⟨r', Nat.lt_trans hr' hr⟩) := by
  conv => lhs; rw [many1Parse]
  rfl

/-- The recursion restated at the **erased** (`run`) level — no subtypes, so the round-trip
proof below is a plain rewrite chain rather than dependent-pair juggling. -/
theorem many1NE_run_eq (p : CBiparser w α) (input : List Char) :
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

/-- `F` survives having a whole *run* of printed elements prepended — so the element law is
applicable at every intermediate continuation. -/
theorem F_closed_run (p : CBiparser w α) (F : List Char → Prop)
    (hclosed : ∀ (s : w) (r : List Char), F r → F ((p.print s).2 ++ r)) :
    ∀ (vs : List w) (rest : List Char), F rest → F ((many1Print p vs).2 ++ rest) := by
  intro vs
  induction vs with
  | nil => intro rest hF; rw [many1Print_nil]; simpa using hF
  | cons v vs' ih =>
      intro rest hF
      have h2 := hclosed v _ (ih rest hF)
      rwa [many1Print_cons_snd, List.append_assoc]

/-- **The seam lemma** — no longer a `sorry`. `many1NE p` round-trips at a FOLLOW that
(a) is admissible for the element, and (b) forbids the continuation from starting *another
element* (`p.run rest = none`) — otherwise greedy repetition reads one more. -/
theorem RoundTrips_many1NE (p : CBiparser w α) (F : List Char → Prop)
    (hp : RoundTrips p F)
    (hclosed : ∀ (s : w) (r : List Char), F r → F ((p.print s).2 ++ r)) :
    RoundTrips (many1NE p) (fun rest => F rest ∧ p.run rest = none) := by
  rintro ⟨u, us⟩ rest ⟨hF, hnone⟩
  have hnone' : (many1NE p).run rest = none := by rw [many1NE_run_eq, hnone]
  show (many1NE p).run ((many1Print p (u :: us)).2 ++ rest)
      = some ((many1Print p (u :: us)).1, rest)
  -- Each `rw` fires exactly once, by design: `many1NE_run_eq` is a *recursion* equation (as a
  -- `simp` lemma it loops), and the `many1Print` equations must not decompose the folded term
  -- `ih` is about. So this is a rewrite chain by necessity, not by taste.
  induction us generalizing u with
  | nil =>
      rw [many1Print_cons_snd, many1Print_cons_fst, many1Print_nil]
      simp only [List.append_nil]
      rw [many1NE_run_eq, hp u rest hF]
      dsimp only
      rw [hnone']
  | cons u' us' ih =>
      rw [many1Print_cons_snd, many1Print_cons_fst, List.append_assoc, many1NE_run_eq,
          hp u _ (F_closed_run p F hclosed (u' :: us') rest hF)]
      dsimp only
      rw [ih u']

/-! ## The example: digit lists separated by `;`, on a domain the law survives on -/

/-- A non-empty digit run. Elements are self-delimiting, so the only FOLLOW is the seam:
*the continuation must not start with a digit*. -/
def pDigitRun : CBiparser (Digit × List Digit) (List Digit) := many1NE digit1

theorem RoundTrips_pDigitRun :
    RoundTrips pDigitRun (fun rest => True ∧ digit1.run rest = none) :=
  RoundTrips_many1NE digit1 (fun _ => True) RoundTrips_digit1 (by intros; trivial)

/-- One element: a digit run, ≥1 whitespace, then `;`. -/
def pElem : CBiparser (Digit × List Digit) (List Digit) := do1
  let l  ← pDigitRun
  let _w ← ws1
  let _s ← pChar1 ';'
  return l

/-- The whole grammar: a non-empty list of elements. -/
def pDigitListsB :
    CBiparser ((Digit × List Digit) × List (Digit × List Digit)) (List (List Digit)) :=
  many1NE pElem

/-! ## End-to-end: the whole grammar round-trips

Every combinator lemma above now gets instantiated. The only real work is discharging the
`hseam` side-conditions — and each one turns out to be a single *lexical* fact:

* `';'` is not whitespace  ⇒ `ws1`'s FOLLOW holds when a `;` follows it.
* `' '` is not a digit     ⇒ the digit run's FOLLOW holds when whitespace follows it.

Those two facts are the entirety of this grammar's FIRST/FOLLOW bookkeeping, and they are
exactly why the delimiters make it unambiguous. Note the payoff: `pElem` ends up
**self-delimiting** (`F = ⊤`), because it terminates in a `;`. -/

/-! The leaves' printers, and the two FOLLOW facts, named. Each seam below is then *literally*
a lexical statement — no biparser internals leak into the proof. -/

theorem pChar1_print (c : Char) (s : w) : (pChar1 c : CBiparser w Char).print s = (c, [c]) := rfl

theorem ws1_print (s : w) : (ws1 : CBiparser w Unit).print s = ((), [' ']) := rfl

theorem NoLeadWs_cons {c : Char} (h : c.isWhitespace = false) (rest : List Char) :
    NoLeadWs (c :: rest) := by
  intro c' hc'
  simp only [List.head?_cons, Option.some.injEq] at hc'
  subst hc'; exact h

theorem digit1_run_cons_none {c : Char} (h : Digit.ofChar? c = none) (rest : List Char) :
    digit1.run (c :: rest) = none := by
  simp [CBiparser.run, digit1, h]

/-- The whole grammar's unambiguity rests on exactly these two facts. -/
theorem semi_not_ws : (';' : Char).isWhitespace = false := by decide
theorem space_not_digit : Digit.ofChar? ' ' = none := rfl

theorem RoundTrips_pElem : RoundTrips pElem (fun _ => True) := by
  unfold pElem
  refine RoundTrips_bind _ _ _ (fun rest => True ∧ digit1.run rest = none)
    RoundTrips_pDigitRun ?_ ?_
  · intro l
    refine RoundTrips_bind _ _ _ NoLeadWs RoundTrips_ws1 ?_ ?_
    · intro _w; exact RoundTrips_map _ _ _ (RoundTrips_pChar1 ';')
    · -- seam: `ws1` stops before the `;`, because a `;` is not whitespace
      intro s rest _
      simpa [map_print, pChar1_print] using NoLeadWs_cons semi_not_ws rest
  · -- seam: the digit run stops before the space, because a space is not a digit
    intro s rest _
    refine ⟨trivial, ?_⟩
    simpa [bind_print, ws1_print, map_print, pChar1_print] using
      digit1_run_cons_none space_not_digit (';' :: rest)

theorem RoundTrips_pDigitListsB :
    RoundTrips pDigitListsB (fun rest => True ∧ pElem.run rest = none) := by
  unfold pDigitListsB
  exact RoundTrips_many1NE pElem (fun _ => True) RoundTrips_pElem (by intros; trivial)

/-! The top-level FOLLOW is discharged at end-of-input: no element parses from `[]`. -/

theorem digit1_run_nil : digit1.run [] = none := rfl

theorem pDigitRun_run_nil : pDigitRun.run [] = none := by
  unfold pDigitRun; rw [many1NE_run_eq, digit1_run_nil]

theorem pElem_run_nil : pElem.run [] = none := by
  unfold pElem; rw [bind_run, pDigitRun_run_nil]

/-- **The end-to-end round-trip.** For *every* source, printing it and parsing the result back
recovers exactly the printed value, with nothing left over — and with **no side-conditions**.
The source type admits only well-formed sources (inductive `Digit`, non-empty `many1NE`), and
the top-level greedy FOLLOW is discharged by `pElem_run_nil`. -/
theorem roundtrip_pDigitListsB (s : (Digit × List Digit) × List (Digit × List Digit)) :
    pDigitListsB.run (pDigitListsB.print s).2 = some ((pDigitListsB.print s).1, []) := by
  have h := RoundTrips_pDigitListsB s [] ⟨trivial, pElem_run_nil⟩
  simpa using h
