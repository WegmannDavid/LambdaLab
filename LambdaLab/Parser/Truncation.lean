import LambdaLab.Parser.LossyParser.Basic

/-!
# Truncation — an `IsoParser` chained into a `LossyParser` over a custom type

The mixfix parser is an iso parser: its trees still contain the parentheses (and any other
purely-surface structure). The type a language actually wants usually doesn't. `truncate` is the
chain from one to the other:

* the user supplies a **projection** `f : v → c'` into their own type — in practice a recursive
  map with one clause per operator (`( e ) ↦ e`, everything else structural) — and an
  **injection** `g : c' → v` sectioning it (`sect`), the canonical tree builder (re-inserting
  parens exactly where structure demands them);
* the annotation family is **derived automatically as the fiber of `f`**:
  `fun x => { t : v // f t = x }` — every tree spelling `x`. So the lossy round-trip law covers
  *every* way the same truncated AST can be generated, and `default = ⟨g x, sect x⟩` makes
  `realize ∘ default` the canonical printer.

`toLossyParserUnit` (in `LossyParser/Basic.lean`) is the degenerate case `f = g = id`.

Nobody writes the three arguments by hand for a mixfix grammar any more. `Parser/Truncation/Mixfix.lean`
generalizes them: a language states a `Rules` bundle — one clause per operator each way, plus which
operator is the parenthesis — and the fold (`truncExpr`), the paren-inserting injection (`injC`) and
the section law (`trunc_inj`) are all *derived*, packaged as `Rules.truncateParser`. The worked
instance is `Arith/Pipeline.lean`'s `aRules` over `ATm` (parens-free terms), plugged into
`arithLanguage` so `((((a))))` parses to `a` and re-renders as `a`; `Stlc/Named/Pipeline.lean` does
the same for `Term VName`. This file stays the general chain the derived one is built on.
-/

-- `p.truncate` dot-notation forces the declaration under `LambdaLab.Parser.IsoParser.IsoParser`.
-- Mathlib's `linter.dupNamespace` was silenced here until Mathlib left the executables' cone.

namespace LambdaLab.Parser

open LambdaLab.Parser.IsoParser (IsoParser HeadIn run_eq_some)
open LambdaLab.Parser.LossyParser (LossyParser)

variable {α : Type} {fst fol : α → Prop} {v c' : Type}

/-- **Truncation**: chain an aligned, echoing `IsoParser` with a projection `f` into the type the
user actually wants (dropping parens, sugar, …), plus an injection `g` sectioning it (`sect` —
e.g. re-inserting parens around compound operands). The result is a `LossyParser` whose
annotation over `x` is **the fiber of `f`** — every tree spelling `x` — derived automatically,
so the lossy round-trip covers every spelling and `default = g` is the canonical one. -/
def IsoParser.IsoParser.truncate
    (p : IsoParser α fst fol v v) (echo : ∀ a : v, (p.print a).1 = a)
    (f : v → c') (g : c' → v) (sect : ∀ x, f (g x) = x) :
    LossyParser α fst fol c' (fun x => { t : v // f t = x }) where
  parse input := (p.parse input).map (fun z => (f z.1, z.2))
  print ann := (p.print ann.1).2
  default {x} := ⟨g x, sect x⟩
  firstOk c rest hc := by
    show ((p.parse (c :: rest)).map _) = none
    rw [p.firstOk c rest hc]
    rfl
  ok x ann rest h := by
    obtain ⟨r, hp, hv⟩ := run_eq_some (p.ok ann.1 rest h)
    show (((p.parse ((p.print ann.1).2 ++ rest)).map _).map _) = some (x, rest)
    rw [hp]
    simp only [Option.map_some]
    rw [hv, echo ann.1, ann.2]

end LambdaLab.Parser
