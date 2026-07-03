import LambdaLab.Stlc.Named.Syntax.Truncate
import LambdaLab.Parser.Basic

/-!
# The STLC term parser as a `TruncatingParser`

`termParser : TruncatingParser Token Term` bundles the front end into the
pipeline-stage interface:

* `parse`  — parse losslessly into `Expr` (`stlc.toLosslessParser`), then
  `truncate` each result to a `Term`.
* `render` — a canonical pretty-printer (`Term → List Token`) that fully
  parenthesizes applications and lambdas, so its output re-parses unambiguously.
* `complete` — the print→parse round-trip, for terms the parser produces.

`Term` is richer than the surface (it carries type annotations and admits any
identifier string), so `render` is a right inverse of `parse` only on the
*parse-produced* terms — exactly what `TruncatingParser.complete` requires.
-/

namespace LambdaLab.Stlc.Named.Syntax

open LambdaLab.Parser
open LambdaLab.Parser.Mixfix

/-- Canonical pretty-printer: variables bare, applications and lambdas fully
parenthesized (so every compound is unambiguously delimited and re-parses). The
`lam` type annotation is dropped — the surface has none. -/
def render : Term → List Token
  | .var x        => [x]
  | .app f a      => ["("] ++ render f ++ render a ++ [")"]
  | .lam x _ body => ["(", "\\lambda", x, "."] ++ render body ++ [")"]

/-- Token-level parse into `Term`: lossless mixfix parse into `Expr`, then
`truncate` each result. -/
def termParse : Parser Token Term :=
  fun tkns => (stlc.toLosslessParser.parse tkns).map (fun p => (truncate p.1, p.2))

/-- The STLC term parser as a `TruncatingParser`. -/
def termParser : TruncatingParser Token Term where
  parse := termParse
  render := render
  complete := by
    -- The print→parse round-trip: for `(b, s) ∈ parse input`, `render b`
    -- re-parses to `b`. Since `b = truncate e` for some lossless parse `e`,
    -- this reduces to: `render (truncate e)` mixfix-parses to some `e'` with
    -- `truncate e' = truncate e`. A structural induction on the rendered tree;
    -- deferred.
    sorry

/-! ### The round-trip, empirically (on parse-produced terms) -/

/-- Source → `Term` (first parse), `Term` → canonical source, then back to `Term`. -/
private def roundTrip (s : String) : Option (Term × List Token × List Term) :=
  (parse s).head?.map fun e =>
    let t := truncate e
    (t, render t, (termParse (render t)).map (·.1))

#eval roundTrip "( \\lambda x . x ) y"
#eval roundTrip "\\lambda f . ( \\lambda x . f x )"

end LambdaLab.Stlc.Named.Syntax
