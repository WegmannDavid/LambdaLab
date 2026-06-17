import LambdaLab.Parser.Tokenizer.ListLemmas
import LambdaLab.Parser.Tokenizer.Basic
import LambdaLab.Parser.Tokenizer.Renders
import LambdaLab.Parser.Tokenizer.Verified

/-!
# A whitespace-separated tokenizer

The first stage of the verification pipeline

    file (String) ──tokenize──▶ tokens (List Token) ──parse──▶ Expr ──truncate──▶ …

`tokenize` splits a source string into tokens at whitespace, Agda-style: tokens
are maximal whitespace-free runs, and adjacent tokens *must* be separated by at
least one whitespace character (no maximal-munch lexing of `n+n` into three
tokens — that is the parser's job once a richer lexer lands).

## Fitting the pipeline

Every stage is a **relation** whose forward map is a function (or an all-results
enumeration) and whose reverse is non-unique. Here the forward map `tokenize` is
deterministic, and the non-uniqueness is on the reverse side: a token list can be
rendered back to source with *redundant whitespace*. We name that reverse relation
`Renders` and characterize the forward map by it, exactly mirroring the parser's

    mem_parse_iff : e ∈ parse tkns ↔ e.flatten = tkns

with

    tokenize_eq_iff : tokenize s = ts ↔ Renders ts s.

Composing the two biconditionals (substitute `ts := e.flatten`) gives the front
half of the pipeline as a single relation, `e ∈ parse (tokenize s) ↔ Renders e.flatten s`.

## Module layout

* `Tokenizer.ListLemmas` — alphabet-agnostic `takeWhile`/`dropWhile` facts.
* `Tokenizer.Basic` — `isTokChar`/`word`/`afterWord`/`skipWS`, `tok`, `tokenize`,
  and the `tok_nil`/`tok_cons` unfolding lemmas.
* `Tokenizer.Renders` — the reverse relation (`IsWS`/`IsWord`/`RendersCore`/
  `Renders`), `tok_ws_prepend`, and the inversion helpers.
* `Tokenizer.Verified` — `tok_renders`, `rendersCore_tok`, and the headline
  `tok_eq_iff` / `tokenize_eq_iff`.
-/
