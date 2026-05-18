/-!
# Parsers and printers

A `Parser β` consumes some prefix of a token list and produces a `β`.
Its round-trip companion is a `Printer β` — given a `β`, return the
tokens that the parser would re-consume to produce that value.

The user-facing intent is that for any sub-parser-printer pair, the
round-trip law
`∀ b ts, parser.run (printer b ++ ts) = some (b, ts)` holds.
-/

namespace LambdaLab.Parser

/-- A token-list printer: the round-trip companion of a `Parser β`. -/
abbrev Printer (β : Type) := β → List String

/-- A token-list parser producing values of type `β`. Bundled with its
round-trip companion printer. -/
structure Parser (β : Type) where
  run : List String → Option (β × List String)
  printer : Printer β

end LambdaLab.Parser
