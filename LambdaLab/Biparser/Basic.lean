import LambdaLab.Biparser.RightSublist

/-!
# A profunctor biparser that returns proper right sublists — core types

This is the `Playground/LawfulBiparser.lean` construction re-homed here, with the
parser's leftover strengthened from a bare `List Char` to a `RightSublist input`
— a *proof of progress* carried in the return type (`length_lt`, and the leftover
is a genuine tail of the input).

This file has only the core: the `Biparser` structure, the round-trip law
`RoundTrips`, and the proof-carrying wrapper `LawfulBiparser`. The leaves and
combinators (`char`, `seq`, `map`, the `Bind`/`Functor`/`Seq` instances, and the
proof-carrying smart constructors) live in `Combinators.lean`.

## The `pure` wall

The strict leftover costs us `pure`: it would have to return the input unchanged
as the leftover, but a `RightSublist` demands a non-empty dropped prefix, so no
such value exists. Hence **no lawful `pure`, no `Monad`, no `do`-with-`return`**.
But `Bind`, `Functor`, and `Seq` are all fine (they only ever *consume*), so
composition — and even `<$>`/`<*>` notation — is available; see `Combinators.lean`.
-/

namespace LambdaLab.Biparser

/-- A biparser over the alphabet `Char`: parses into `v` (returning a proof-of-
progress leftover) and prints from a source `w`. -/
structure Biparser (w v : Type) where
  parse : (input : List Char) → Option (v × RightSublist input)
  print : w → v × List Char

/-- **Print-then-parse round trip.** Whatever `print` emits from a source `src`,
`parse` recovers exactly, and the returned leftover is precisely the trailing
`rest`. The `∀ rest` is load-bearing: it is what makes the law compose through
`seq`. -/
def RoundTrips {w v : Type} (bp : Biparser w v) : Prop :=
  ∀ (src : w) (rest : List Char),
    ∃ s : RightSublist ((bp.print src).2 ++ rest),
      s.list = rest ∧ bp.parse ((bp.print src).2 ++ rest) = some ((bp.print src).1, s)

/-- A biparser bundled with a proof that it round-trips. `extends` inlines the
`Biparser` (projected as `toBiparser`, with direct `.parse`/`.print` access). -/
structure LawfulBiparser (w v : Type) extends Biparser w v where
  ok : RoundTrips toBiparser

end LambdaLab.Biparser
