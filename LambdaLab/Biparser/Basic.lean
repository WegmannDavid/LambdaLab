/-!
# A profunctor biparser — core types (deterministic, monadic)

A `Biparser α w v` bundles a **parser** and a **printer** over the alphabet `α`:
`parse` reads a `List α` deterministically (at most one result), `print` emits a
`List α` from a source `w`. The leftover after a parse is a plain `List α`.

Unlike a `RightSublist`-indexed leftover, the plain leftover imposes no
progress-proof obligation — so `pure` is definable (it consumes nothing), and the
whole thing is a **monad**: `do`-notation, `<$>`, `<*>` all work. Progress (needed
for terminating recursive parsers) becomes a *beside* lemma, proved only where a
recursion actually needs it.

The round-trip law `RoundTrips` lives beside the structure; `LawfulBiparser`
bundles a biparser with its proof and is itself a monad, so a grammar written with
`do` comes out proof-carrying automatically. Leaves and combinators are in
`Combinators.lean`.
-/

namespace LambdaLab.Biparser

/-- A biparser over the alphabet `α`: a deterministic parser `List α → Option (v ×
List α)` and a printer `w → v × List α`. -/
structure Biparser (α w v : Type) where
  parse : List α → Option (v × List α)
  print : w → v × List α

/-- **Print-then-parse round trip.** Whatever `print` emits from a source `src`,
`parse` recovers exactly, leaving any trailing `rest` untouched. The `∀ rest` is
load-bearing: it makes the law compose through `bind`/`seq`. -/
def RoundTrips {α w v : Type} (bp : Biparser α w v) : Prop :=
  ∀ (src : w) (rest : List α),
    bp.parse ((bp.print src).2 ++ rest) = some ((bp.print src).1, rest)

/-- A biparser bundled with a proof that it round-trips. `extends` inlines the
`Biparser` (projected as `toBiparser`, with direct `.parse`/`.print` access). -/
structure LawfulBiparser (α w v : Type) extends Biparser α w v where
  ok : RoundTrips toBiparser

end LambdaLab.Biparser
