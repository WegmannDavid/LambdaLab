import LambdaLab.Biparser.Basic

/-!
# Biparser combinators

The leaves and combinators for `Biparser` (see `Basic.lean` for the core types
and the round-trip law). Everything is polymorphic in the alphabet `α`. Each
combinator comes with a **preservation lemma** (`RoundTrips_*`), proved once, and
a proof-carrying smart constructor on `LawfulBiparser` that threads the proof.

## What notation is available

There is no lawful `pure`, so no `Monad`/`do`-with-`return`. But:

* `Bind` **is** definable — `bind` composes the two leftovers with `trans`, just
  like `seq`. So `do`-blocks work *as long as they end in an actual parser* (no
  final `pure`/`return` to inject a value).
* `Functor` (`<$>`) and `Seq` (`<*>`) are definable — they only consume, never
  inject — so the Applicative-minus-`Pure` style
  `(·, ·, ·) <$> pa <*> pb <*> pc` builds values with no `pure` at all. This is
  the idiomatic combinator style, and it threads through `LawfulBiparser` too.

## Leaves

* `tok c` — a fixed literal element (needs `DecidableEq α`); value is `c`.
* `anyTok` — any single element; prints whatever its source carries.
* `sat p` — any element satisfying `p`; source is the subtype `{a // p a}`. This
  is the variable-token leaf the mixfix layer reads identifiers through.
-/

namespace LambdaLab.Biparser

/-! ## Proof plumbing -/

/-- Rewriting a `parse` result along an equality of the input, transporting the
leftover with `RightSublist.cast`. Reconciles a combinator's law (stated at
`c ++ rest`) with a caller that feeds it the leftover `s.list`. -/
theorem parse_congr {α w v : Type} {bp : Biparser α w v} {l l' : List α}
    (h : l = l') {x : v} {s : RightSublist l} :
    bp.parse l = some (x, s) → bp.parse l' = some (x, s.cast h) := by
  subst h; exact id

/-! ## Leaf: `tok` (fixed literal) -/

/-- The single-element literal leaf. Parsing consumes exactly the matched head (so
the leftover is a genuine `RightSublist`); printing emits `[c]`. -/
def tok {α : Type} [DecidableEq α] (c : α) : Biparser α Unit α where
  parse input := match input with
    | [] => none
    | c' :: rest => if c = c' then some (c, RightSublist.cons c' rest) else none
  print _ := (c, [c])

/-- The `tok` leaf round-trips: it prints `[c]` and parse peels exactly that off. -/
theorem RoundTrips_tok {α : Type} [DecidableEq α] (c : α) : RoundTrips (tok c) := by
  intro _ rest
  refine ⟨RightSublist.cons c rest, rfl, ?_⟩
  simp [tok]

/-! ## Leaf: `anyTok` (any element) -/

/-- `tok c` prints a *fixed* literal; `anyTok` prints whatever element its source
carries (`print src = (src, [src])`) and parses any single element. -/
def anyTok {α : Type} : Biparser α α α where
  parse input := match input with
    | []        => none
    | c :: rest => some (c, RightSublist.cons c rest)
  print src := (src, [src])

theorem RoundTrips_anyTok {α : Type} : RoundTrips (anyTok (α := α)) :=
  fun src rest => ⟨RightSublist.cons src rest, rfl, rfl⟩

/-! ## Leaf: `sat` (any element satisfying `p`) -/

/-- Any element satisfying `p`. The source is the subtype `{a // p a = true}`, so
`print` always emits a genuine `p`-element and `parse`'s guard succeeds on it —
that is what makes the round-trip hold. The variable-token leaf. -/
def sat {α : Type} (p : α → Bool) : Biparser α {a : α // p a = true} α where
  parse input := match input with
    | []        => none
    | c :: rest => if p c then some (c, RightSublist.cons c rest) else none
  print src := (src.1, [src.1])

theorem RoundTrips_sat {α : Type} (p : α → Bool) : RoundTrips (sat p) := by
  intro src rest
  refine ⟨RightSublist.cons src.1 rest, rfl, ?_⟩
  simp [sat, src.2]

/-! ## Combinator: `map` (functor) -/

/-- Reshape the output value. Only needs `f : a → b` (never `f⁻¹`): the printer is
driven by the *source*, so it produces the underlying value and maps it forward. -/
def map {α w a b : Type} (f : a → b) (bw : Biparser α w a) : Biparser α w b where
  parse input := (bw.parse input).map fun r => (f r.1, r.2)
  print src := let (v, s) := bw.print src; (f v, s)

theorem RoundTrips_map {α w a b : Type} (f : a → b) (bw : Biparser α w a)
    (h : RoundTrips bw) : RoundTrips (map f bw) := by
  intro src rest
  obtain ⟨s, hL, hP⟩ := h src rest
  refine ⟨s, hL, ?_⟩
  show ((bw.parse ((bw.print src).2 ++ rest)).map fun r => (f r.1, r.2))
        = some (f (bw.print src).1, s)
  rw [hP]
  rfl

/-! ## Combinator: `seq` (pairing) -/

/-- Sequential composition: run `bw1`, then `bw2` on its leftover, pairing the
values and composing the two progress witnesses via `RightSublist.trans`. No
`pure` needed — the result is the *product* `a × b`, built from two consumers. -/
def seq {α w a b : Type} (bw1 : Biparser α w a) (bw2 : Biparser α w b) :
    Biparser α w (a × b) where
  parse input :=
    (bw1.parse input).bind fun r1 =>
      (bw2.parse r1.2.list).map fun r2 => ((r1.1, r2.1), r1.2.trans r2.2)
  print src :=
    (((bw1.print src).1, (bw2.print src).1), (bw1.print src).2 ++ (bw2.print src).2)

/-- `seq` preserves round-tripping: threads `bw1`'s guarantee at the suffix
`c2 ++ rest`, then `bw2`'s at `rest`, and composes the leftovers with `trans`. -/
theorem RoundTrips_seq {α w a b : Type} (bw1 : Biparser α w a) (bw2 : Biparser α w b)
    (h1 : RoundTrips bw1) (h2 : RoundTrips bw2) : RoundTrips (seq bw1 bw2) := by
  intro src rest
  -- Expose `seq`'s printed string as `c1 ++ c2` so the reassociation can see the
  -- `(_ ++ _) ++ _` pattern through `.print`.
  show ∃ s : RightSublist (((bw1.print src).2 ++ (bw2.print src).2) ++ rest),
      s.list = rest ∧
        (seq bw1 bw2).parse (((bw1.print src).2 ++ (bw2.print src).2) ++ rest)
          = some (((bw1.print src).1, (bw2.print src).1), s)
  -- `seq` prints left-assoc `(c1 ++ c2) ++ rest`; the recursion peels `c1` leaving
  -- `c1 ++ (c2 ++ rest)`. Reassociate the whole goal so the indices line up.
  rw [List.append_assoc]
  obtain ⟨s1, hs1L, hs1P⟩ := h1 src ((bw2.print src).2 ++ rest)
  obtain ⟨s2, hs2L, hs2P⟩ := h2 src rest
  have hs2P' : bw2.parse s1.list = some ((bw2.print src).1, s2.cast hs1L.symm) :=
    parse_congr hs1L.symm hs2P
  refine ⟨s1.trans (s2.cast hs1L.symm), by simp [hs2L], ?_⟩
  show ((bw1.parse _).bind fun r1 =>
        (bw2.parse r1.2.list).map fun r2 => ((r1.1, r2.1), r1.2.trans r2.2)) = _
  rw [hs1P]
  show ((bw2.parse s1.list).map fun r2 =>
        (((bw1.print src).1, r2.1), s1.trans r2.2)) = _
  rw [hs2P']
  rfl

/-! ## Combinator: `seqAp` (applicative apply) -/

/-- Applicative application, `f (a → b) → f a → f b` — the shape `<*>` wants.
Defined as `map` over `seq`, so its round-trip proof reuses both lemmas. -/
def seqAp {α w a b : Type} (bf : Biparser α w (a → b)) (bw : Biparser α w a) :
    Biparser α w b :=
  map (fun p => p.1 p.2) (seq bf bw)

theorem RoundTrips_seqAp {α w a b : Type} (bf : Biparser α w (a → b)) (bw : Biparser α w a)
    (hf : RoundTrips bf) (hw : RoundTrips bw) : RoundTrips (seqAp bf bw) :=
  RoundTrips_map _ _ (RoundTrips_seq bf bw hf hw)

/-! ## Combinator: `comap` (profunctor source-map)

The one combinator that unlocks *structured* biparsers. `map` reshapes the
*output* (`v`); `comap` reshapes the *source* (`w`) contravariantly — so two
`seq` branches can print two different parts of a shared source (`comap .1` and
`comap .2`). Without it, both branches would print from the identical source and
only literal (source-free) content could be built.

`comap` touches only `print`, never `parse`, so its round-trip law is immediate. -/

def comap {α w w' v : Type} (g : w' → w) (bp : Biparser α w v) : Biparser α w' v where
  parse := bp.parse
  print src := bp.print (g src)

theorem RoundTrips_comap {α w w' v : Type} (g : w' → w) (bp : Biparser α w v)
    (h : RoundTrips bp) : RoundTrips (comap g bp) := fun src rest => h (g src) rest

/-! ## Combinator: `alt` (choice / coproduct)

`alt` is the coproduct: the source `w₁ ⊕ w₂` selects which branch `print` uses,
and `parse` is **ordered choice** — try `bp₁`, fall back to `bp₂`.

The round-trip law is where mixfix ambiguity bites. The left branch is free
(tried first, so its own round-trip closes it). The right branch needs a
**disjointness** side-condition: `bp₁` must *reject* everything `bp₂` prints —
otherwise `parse` would take `bp₁`'s reading of a `bp₂`-string. This is exactly
the "distinct leading tokens" obligation; it cannot be avoided, because `parse`
sees only the input, never the source that chose the branch.

Predicate-style dispatch is derivable: `comap (fun s => if p s then .inl s else
.inr s) (alt bp₁ bp₂)`. -/

def alt {α w₁ w₂ v : Type} (bp₁ : Biparser α w₁ v) (bp₂ : Biparser α w₂ v) :
    Biparser α (w₁ ⊕ w₂) v where
  parse input :=
    match bp₁.parse input with
    | some r => some r
    | none   => bp₂.parse input
  print
    | .inl x => bp₁.print x
    | .inr y => bp₂.print y

theorem RoundTrips_alt {α w₁ w₂ v : Type} (bp₁ : Biparser α w₁ v) (bp₂ : Biparser α w₂ v)
    (h₁ : RoundTrips bp₁) (h₂ : RoundTrips bp₂)
    (hdisj : ∀ (y : w₂) (rest : List α), bp₁.parse ((bp₂.print y).2 ++ rest) = none) :
    RoundTrips (alt bp₁ bp₂) := by
  intro src rest
  cases src with
  | inl x =>
    obtain ⟨s, hL, hP⟩ := h₁ x rest
    refine ⟨s, hL, ?_⟩
    simp only [alt]
    rw [hP]
  | inr y =>
    obtain ⟨s, hL, hP⟩ := h₂ y rest
    refine ⟨s, hL, ?_⟩
    simp only [alt]
    rw [hdisj y rest]
    exact hP

/-! ## Typeclass instances (bare biparser)

`Bind` gives `do` (for blocks ending in a parser); `Functor`/`Seq` give `<$>`/`<*>`.
No `Pure`/`Monad` — see the file header. -/

instance {α w : Type} : Functor (Biparser α w) where
  map := map

instance {α w : Type} : Seq (Biparser α w) where
  seq bf bw := seqAp bf (bw ())

instance {α w : Type} : Bind (Biparser α w) where
  bind bw f := {
    parse := fun input => (bw.parse input).bind fun r1 =>
      ((f r1.1).parse r1.2.list).map fun r2 => (r2.1, r1.2.trans r2.2)
    print := fun src =>
      let (a, s) := bw.print src
      let (b, s') := (f a).print src
      (b, s ++ s') }

/-! ## Proof-carrying smart constructors (`LawfulBiparser`)

Each mirrors a combinator and assembles the round-trip proof from the parts, so
callers never re-prove it. `Functor`/`Seq` instances make `<$>`/`<*>` proof-carrying. -/

def ltok {α : Type} [DecidableEq α] (c : α) : LawfulBiparser α Unit α :=
  ⟨tok c, RoundTrips_tok c⟩

def lanyTok {α : Type} : LawfulBiparser α α α := ⟨anyTok, RoundTrips_anyTok⟩

def lsat {α : Type} (p : α → Bool) : LawfulBiparser α {a : α // p a = true} α :=
  ⟨sat p, RoundTrips_sat p⟩

def lmap {α w a b : Type} (f : a → b) (x : LawfulBiparser α w a) : LawfulBiparser α w b :=
  ⟨map f x.toBiparser, RoundTrips_map f x.toBiparser x.ok⟩

def lseq {α w a b : Type} (x : LawfulBiparser α w a) (y : LawfulBiparser α w b) :
    LawfulBiparser α w (a × b) :=
  ⟨seq x.toBiparser y.toBiparser, RoundTrips_seq _ _ x.ok y.ok⟩

def lcomap {α w w' v : Type} (g : w' → w) (x : LawfulBiparser α w v) : LawfulBiparser α w' v :=
  ⟨comap g x.toBiparser, RoundTrips_comap g x.toBiparser x.ok⟩

/-- Proof-carrying choice. Unlike the other smart constructors this takes an extra
argument — the **disjointness** proof (`x` rejects everything `y` prints) — because
that obligation is genuine, not derivable from the two pieces. -/
def lalt {α w₁ w₂ v : Type} (x : LawfulBiparser α w₁ v) (y : LawfulBiparser α w₂ v)
    (hdisj : ∀ (b : w₂) (rest : List α), x.parse ((y.print b).2 ++ rest) = none) :
    LawfulBiparser α (w₁ ⊕ w₂) v :=
  ⟨alt x.toBiparser y.toBiparser, RoundTrips_alt _ _ x.ok y.ok hdisj⟩

instance {α w : Type} : Functor (LawfulBiparser α w) where
  map f x := ⟨map f x.toBiparser, RoundTrips_map f x.toBiparser x.ok⟩

instance {α w : Type} : Seq (LawfulBiparser α w) where
  seq x y := ⟨seqAp x.toBiparser (y ()).toBiparser, RoundTrips_seqAp _ _ x.ok (y ()).ok⟩

/-! ## Demonstration (over `α = Char`) -/

/-- Explicit pairing via `lseq`. `×` is right-associative, so this is `Char³`. -/
def abc : LawfulBiparser Char Unit (Char × Char × Char) :=
  lseq (ltok 'a') (lseq (ltok 'b') (ltok 'c'))

/-- Same grammar, applicative style — proof threaded through `<$>`/`<*>`. -/
def abcAp : LawfulBiparser Char Unit (Char × Char × Char) :=
  (fun a b c => (a, b, c)) <$> ltok 'a' <*> ltok 'b' <*> ltok 'c'

/-- `do` works too — but only because this block ends in a parser (`tok 'b'`),
never a `pure`. -/
def ab : Biparser Char Unit Char := do
  let _a ← tok 'a'
  tok 'b'

/-- **Structured data, print for free.** A biparser whose value *is* a pair of
characters, read from a source pair via `comap`. Nobody wrote a printer: `print`
is assembled by the combinators — `print (a, b) = ((a, b), [a, b])` — and the
round-trip proof is threaded the same way. This is the whole idea, in miniature:
build the tree out of combinators and both directions + the law come out free. -/
def pair : LawfulBiparser Char (Char × Char) (Char × Char) :=
  (fun a b => (a, b)) <$> lcomap Prod.fst lanyTok <*> lcomap Prod.snd lanyTok

/-- Choice: parse `'a'` or `'b'`. The disjointness obligation (`tok 'a'` rejects
what `tok 'b'` prints) is discharged by `'a' ≠ 'b'`. `print` dispatches on the
`Sum` source; `parse` is ordered choice. -/
def aOrB : LawfulBiparser Char (Unit ⊕ Unit) Char :=
  lalt (ltok 'a') (ltok 'b') (by intro _ rest; simp [ltok, tok])

/-- `sat` in action: any digit. `print` re-emits the digit from its (subtype)
source; `parse` accepts a head only when it satisfies the predicate. This is the
variable-token mechanism, shown at the char level. -/
def digit : LawfulBiparser Char {c : Char // Char.isDigit c = true} Char :=
  lsat Char.isDigit

-- All proof-carrying, for free:
#check (abc.ok   : RoundTrips abc.toBiparser)
#check (digit.ok : RoundTrips digit.toBiparser)
#check (abcAp.ok : RoundTrips abcAp.toBiparser)
#check (pair.ok  : RoundTrips pair.toBiparser)
#check (aOrB.ok  : RoundTrips aOrB.toBiparser)

#eval (abc.parse   "abcd".toList).map (fun r => (r.1, r.2.list))  -- some (('a','b','c'), ['d'])
#eval (abcAp.parse "abcd".toList).map (fun r => (r.1, r.2.list))  -- some (('a','b','c'), ['d'])
#eval (ab.parse    "abc".toList ).map (fun r => (r.1, r.2.list))  -- some ('b', ['c'])
#eval (pair.parse  "xyz".toList ).map (fun r => (r.1, r.2.list))  -- some (('x','y'), ['z'])
#eval pair.print ('x', 'y')                                       -- (('x','y'), ['x','y'])
#eval (aOrB.parse  "a".toList  ).map (fun r => (r.1, r.2.list))   -- some ('a', [])
#eval (aOrB.parse  "b".toList  ).map (fun r => (r.1, r.2.list))   -- some ('b', [])
#eval (aOrB.print (.inl ()), aOrB.print (.inr ()))                -- (('a',['a']), ('b',['b']))
#eval (digit.parse "7x".toList).map (fun r => (r.1, r.2.list))    -- some ('7', ['x'])

end LambdaLab.Biparser
