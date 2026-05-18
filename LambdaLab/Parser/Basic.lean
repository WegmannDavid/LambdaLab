/-!
# Parsers and printers

A `Parser S β` consumes some prefix of a token list and produces a `β`,
threading a parser state of type `S`. Its round-trip companion is a
`Printer β` — given a `β`, return the tokens that the parser would
re-consume to produce that value. The printer is stateless: state is a
parsing-time-only artifact (e.g. a fresh-mvar counter).

For a stateless sub-parser use `Parser Unit β`. For one that needs to
hand out fresh names or counters, use `Parser Nat β` (or any other
state type).

The user-facing intent is that for any *stateless* sub-parser-printer
pair, the round-trip law
`∀ b s ts, parser.run s (printer b ++ ts) = some (s, b, ts)` holds.
Stateful sub-parsers obey a weaker law (state delta exists but isn't
required to be zero).
-/

namespace LambdaLab.Parser

/-- A token-list printer: the round-trip companion of a `Parser S β`. -/
abbrev Printer (β : Type) := β → List String

/-- A token-list parser producing values of type `β`, threading a
parser state of type `S`. Bundled with its round-trip companion printer. -/
structure Parser (S β : Type) where
  run : S → List String → Option (S × β × List String)
  printer : Printer β

/-- A stateless parser. -/
abbrev StatelessParser (β : Type) := Parser Unit β

end LambdaLab.Parser
