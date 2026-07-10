import LambdaLab.Biparser.Basic

/-!
# Biparser combinators

The leaves and combinators for `Biparser` (see `Basic.lean` for the core types
and the round-trip law). Each combinator comes with a **preservation lemma**
(`RoundTrips_*`), proved once, and a proof-carrying smart constructor on
`LawfulBiparser` that threads the proof.

## What notation is available

There is no lawful `pure`, so no `Monad`/`do`-with-`return`. But:

* `Bind` **is** definable — `bind` composes the two leftovers with `trans`, just
  like `seq`. So `do`-blocks work *as long as they end in an actual parser* (no
  final `pure`/`return` to inject a value).
* `Functor` (`<$>`) and `Seq` (`<*>`) are definable — they only consume, never
  inject — so the Applicative-minus-`Pure` style
  `(·, ·, ·) <$> pa <*> pb <*> pc` builds values with no `pure` at all. This is
  the idiomatic combinator style, and it threads through `LawfulBiparser` too.
-/

namespace LambdaLab.Biparser

/-! ## Proof plumbing -/

/-- Rewriting a `parse` result along an equality of the input, transporting the
leftover with `RightSublist.cast`. Reconciles a combinator's law (stated at
`c ++ rest`) with a caller that feeds it the leftover `s.list`. -/
theorem parse_congr {w v : Type} {bp : Biparser w v} {l l' : List Char}
    (h : l = l') {x : v} {s : RightSublist l} :
    bp.parse l = some (x, s) → bp.parse l' = some (x, s.cast h) := by
  subst h; exact id

/-! ## Leaf: `char` -/

/-- The single-character leaf. Parsing consumes exactly the matched head (so the
leftover is a genuine `RightSublist`); printing emits `[c]`. -/
def char (c : Char) : Biparser Unit Char where
  parse input := match input with
    | [] => none
    | c' :: rest => if c = c' then some (c, RightSublist.cons c' rest) else none
  print _ := (c, [c])

/-- The `char` leaf round-trips: it prints `[c]` and parse peels exactly that off. -/
theorem RoundTrips_char (c : Char) : RoundTrips (char c) := by
  intro _ rest
  refine ⟨RightSublist.cons c rest, rfl, ?_⟩
  simp [char]

/-! ## Combinator: `map` (functor) -/

/-- Reshape the output value. Only needs `f : a → b` (never `f⁻¹`): the printer is
driven by the *source*, so it produces the underlying value and maps it forward. -/
def map {w a b : Type} (f : a → b) (bw : Biparser w a) : Biparser w b where
  parse input := (bw.parse input).map fun r => (f r.1, r.2)
  print src := let (v, s) := bw.print src; (f v, s)

theorem RoundTrips_map {w a b : Type} (f : a → b) (bw : Biparser w a)
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
def seq {w a b : Type} (bw1 : Biparser w a) (bw2 : Biparser w b) : Biparser w (a × b) where
  parse input :=
    (bw1.parse input).bind fun r1 =>
      (bw2.parse r1.2.list).map fun r2 => ((r1.1, r2.1), r1.2.trans r2.2)
  print src :=
    (((bw1.print src).1, (bw2.print src).1), (bw1.print src).2 ++ (bw2.print src).2)

/-- `seq` preserves round-tripping: threads `bw1`'s guarantee at the suffix
`c2 ++ rest`, then `bw2`'s at `rest`, and composes the leftovers with `trans`. -/
theorem RoundTrips_seq {w a b : Type} (bw1 : Biparser w a) (bw2 : Biparser w b)
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
def seqAp {w a b : Type} (bf : Biparser w (a → b)) (bw : Biparser w a) : Biparser w b :=
  map (fun p => p.1 p.2) (seq bf bw)

theorem RoundTrips_seqAp {w a b : Type} (bf : Biparser w (a → b)) (bw : Biparser w a)
    (hf : RoundTrips bf) (hw : RoundTrips bw) : RoundTrips (seqAp bf bw) :=
  RoundTrips_map _ _ (RoundTrips_seq bf bw hf hw)

/-! ## Typeclass instances (bare biparser)

`Bind` gives `do` (for blocks ending in a parser); `Functor`/`Seq` give `<$>`/`<*>`.
No `Pure`/`Monad` — see the file header. -/

instance : Functor (Biparser w) where
  map := map

instance : Seq (Biparser w) where
  seq bf bw := seqAp bf (bw ())

instance : Bind (Biparser w) where
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

def lchar (c : Char) : LawfulBiparser Unit Char := ⟨char c, RoundTrips_char c⟩

def lmap {w a b : Type} (f : a → b) (x : LawfulBiparser w a) : LawfulBiparser w b :=
  ⟨map f x.toBiparser, RoundTrips_map f x.toBiparser x.ok⟩

def lseq {w a b : Type} (x : LawfulBiparser w a) (y : LawfulBiparser w b) :
    LawfulBiparser w (a × b) :=
  ⟨seq x.toBiparser y.toBiparser, RoundTrips_seq _ _ x.ok y.ok⟩

instance : Functor (LawfulBiparser w) where
  map f x := ⟨map f x.toBiparser, RoundTrips_map f x.toBiparser x.ok⟩

instance : Seq (LawfulBiparser w) where
  seq x y := ⟨seqAp x.toBiparser (y ()).toBiparser, RoundTrips_seqAp _ _ x.ok (y ()).ok⟩

/-! ## Demonstration -/

/-- Explicit pairing via `lseq`. `×` is right-associative, so this is `Char³`. -/
def abc : LawfulBiparser Unit (Char × Char × Char) :=
  lseq (lchar 'a') (lseq (lchar 'b') (lchar 'c'))

/-- Same grammar, applicative style — proof threaded through `<$>`/`<*>`. -/
def abcAp : LawfulBiparser Unit (Char × Char × Char) :=
  (fun a b c => (a, b, c)) <$> lchar 'a' <*> lchar 'b' <*> lchar 'c'

/-- `do` works too — but only because this block ends in a parser (`char 'b'`),
never a `pure`. -/
def ab : Biparser Unit Char := do
  let _a ← char 'a'
  char 'b'

-- Both grammars are proof-carrying, for free:
#check (abc.ok   : RoundTrips abc.toBiparser)
#check (abcAp.ok : RoundTrips abcAp.toBiparser)

#eval (abc.parse   "abcd".toList).map (fun r => (r.1, r.2.list))  -- some (('a','b','c'), ['d'])
#eval (abcAp.parse "abcd".toList).map (fun r => (r.1, r.2.list))  -- some (('a','b','c'), ['d'])
#eval (ab.parse    "abc".toList ).map (fun r => (r.1, r.2.list))  -- some ('b', ['c'])

end LambdaLab.Biparser
