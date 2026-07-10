import LambdaLab.Biparser.RightSublist

/-!
# A monadic-profunctor biparser that returns proper right sublists

This is the `Playground/LawfulBiparser.lean` construction re-homed here, with the
parser's leftover strengthened from a bare `List Char` to a `RightSublist input`
— a *proof of progress* carried in the return type (`length_lt`, and the leftover
is a genuine tail of the input).

## The `pure` wall

That strengthening costs us the `Monad`. `pure a` must consume nothing, i.e.
return the input unchanged as the leftover; but a `RightSublist` demands a
non-empty dropped prefix, so no such leftover exists. Hence **there is no lawful
`pure`, no `Monad`, and no `do`-notation** here.

We compose with `seq` instead: every leaf (`char`) consumes ≥1 token, so a
sequence never needs `pure`. This is the combinator (not monad) shape the rest of
the library uses. The proof-carrying idea survives intact: `RoundTrips` is an
external law, the preservation lemmas (`RoundTrips_char`, `RoundTrips_seq`) are
proved once, and `LawfulBiparser` threads the proof through the `lchar`/`lseq`
smart constructors.
-/

namespace LambdaLab.Biparser

/-- A biparser over the alphabet `Char`: parses into `v` (returning a proof-of-
progress leftover) and prints from a source `w`. -/
structure Biparser (w v : Type) where
  parse : (input : List Char) → Option (v × RightSublist input)
  print : w → v × List Char

/-- The single-character leaf. Parsing consumes exactly the matched head (so the
leftover is a genuine `RightSublist`); printing emits `[c]`. -/
def char (c : Char) : Biparser Unit Char where
  parse input := match input with
    | [] => none
    | c' :: rest => if c = c' then some (c, RightSublist.cons c' rest) else none
  print _ := (c, [c])

/-- Sequential composition: run `bw1`, then `bw2` on its leftover, pairing the
values and composing the two progress witnesses via `RightSublist.trans`.
Printing concatenates the two emitted strings (both driven by the same source).
No `pure` needed — the result type is the *product* `a × b`, built from two
consuming parsers. -/
def seq {w a b : Type} (bw1 : Biparser w a) (bw2 : Biparser w b) : Biparser w (a × b) where
  parse input :=
    (bw1.parse input).bind fun r1 =>
      (bw2.parse r1.2.list).map fun r2 => ((r1.1, r2.1), r1.2.trans r2.2)
  print src :=
    (((bw1.print src).1, (bw2.print src).1), (bw1.print src).2 ++ (bw2.print src).2)

/-! ## The round-trip law -/

/-- **Print-then-parse round trip.** Whatever `print` emits from a source `src`,
`parse` recovers exactly, and the returned leftover is precisely the trailing
`rest`. The `∀ rest` is load-bearing: it is what makes the law compose through
`seq`. -/
def RoundTrips {w v : Type} (bp : Biparser w v) : Prop :=
  ∀ (src : w) (rest : List Char),
    ∃ s : RightSublist ((bp.print src).2 ++ rest),
      s.list = rest ∧ bp.parse ((bp.print src).2 ++ rest) = some ((bp.print src).1, s)

/-- Rewriting a `parse` result along an equality of the input, transporting the
leftover with `RightSublist.cast`. Used to reconcile `bw2`'s law (stated at
`c2 ++ rest`) with `seq`, which feeds `bw2` the leftover `s1.list`. -/
theorem parse_congr {w v : Type} {bp : Biparser w v} {l l' : List Char}
    (h : l = l') {x : v} {s : RightSublist l} :
    bp.parse l = some (x, s) → bp.parse l' = some (x, s.cast h) := by
  subst h; exact id

/-! ## Preservation lemmas -/

/-- The `char` leaf round-trips: it prints `[c]` and parse peels exactly that off. -/
theorem RoundTrips_char (c : Char) : RoundTrips (char c) := by
  intro _ rest
  refine ⟨RightSublist.cons c rest, rfl, ?_⟩
  simp [char]

/-- `seq` **preserves** round-tripping: threads `bw1`'s guarantee at the suffix
`c2 ++ rest`, then `bw2`'s at `rest`, and composes the leftovers with `trans`. -/
theorem RoundTrips_seq {w a b : Type} (bw1 : Biparser w a) (bw2 : Biparser w b)
    (h1 : RoundTrips bw1) (h2 : RoundTrips bw2) : RoundTrips (seq bw1 bw2) := by
  intro src rest
  -- Expose `seq`'s printed string as the concrete concatenation `c1 ++ c2` so the
  -- reassociation below can see the `(_ ++ _) ++ _` pattern through `.print`.
  show ∃ s : RightSublist (((bw1.print src).2 ++ (bw2.print src).2) ++ rest),
      s.list = rest ∧
        (seq bw1 bw2).parse (((bw1.print src).2 ++ (bw2.print src).2) ++ rest)
          = some (((bw1.print src).1, (bw2.print src).1), s)
  -- `seq`'s print concatenates left-assoc `(c1 ++ c2) ++ rest`; the recursion peels
  -- `c1` leaving `c1 ++ (c2 ++ rest)`. Reassociate the whole goal so the indices line up.
  rw [List.append_assoc]
  obtain ⟨s1, hs1L, hs1P⟩ := h1 src ((bw2.print src).2 ++ rest)
  obtain ⟨s2, hs2L, hs2P⟩ := h2 src rest
  -- `bw2`'s parse, re-indexed from `c2 ++ rest` to the actual leftover `s1.list`.
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

/-! ## The proof-carrying biparser -/

/-- A biparser bundled with a proof that it round-trips. `extends` inlines the
`Biparser` (projected as `toBiparser`, with direct `.parse`/`.print` access). -/
structure LawfulBiparser (w v : Type) extends Biparser w v where
  ok : RoundTrips toBiparser

/-- The `char` leaf, packaged with its proof. -/
def lchar (c : Char) : LawfulBiparser Unit Char := ⟨char c, RoundTrips_char c⟩

/-- Proof-carrying sequential composition — the `seq` analogue of a monadic bind.
The round-trip proof of the whole is assembled from the parts by `RoundTrips_seq`,
so callers never re-prove it. This is what `do` did in the `List`-leftover version;
here composition is explicit because there is no `pure`. -/
def lseq {w a b : Type} (x : LawfulBiparser w a) (y : LawfulBiparser w b) :
    LawfulBiparser w (a × b) :=
  ⟨seq x.toBiparser y.toBiparser, RoundTrips_seq _ _ x.ok y.ok⟩

/-! ## Demonstration -/

/-- Built by explicit `lseq` (no `do`). `× ` is right-associative, so this is a
`Char × Char × Char`. -/
def abc : LawfulBiparser Unit (Char × Char × Char) :=
  lseq (lchar 'a') (lseq (lchar 'b') (lchar 'c'))

-- The proof exists, for free — assembled by `lseq`/`RoundTrips_seq`:
#check (abc.ok : RoundTrips abc.toBiparser)

#eval (abc.parse "abcd".toList).map (fun r => (r.1, r.2.list))
  -- some (('a', 'b', 'c'), ['d'])
#eval abc.print ()
  -- (('a', 'b', 'c'), ['a', 'b', 'c'])

end LambdaLab.Biparser
