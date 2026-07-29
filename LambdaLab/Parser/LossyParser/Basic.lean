import LambdaLab.Parser.IsoParser.Basic
import LambdaLab.Abstraction.Basic

/-!
# `LossyParser` — a consuming parser with an annotation family, the bridge to `Abs`

The general parser shape that **canonically yields an `Abstraction` morphism**. It is
`IsoParser`'s split source/value model with the source type `w` replaced by an *indexed annotation
family* `Ann : V → Type` (plus a `default` annotation). That one change repairs all three gaps the
split model's own header documents:

* *"the law pins only the printed value, never connecting it to the source"* — here `print` is
  indexed by the value, so `ok` pins the index: parsing a printed annotation recovers **its** value.
* *"exactness is not even stateable"* — it is now (`Exact`): whatever the parser consumed is the
  print of *some* annotation of the result.
* *"there is no annotation family, so only canonical-form languages are genuine isos"* — the
  family is the whole point: `Ann v` holds every surface spelling of `v` (redundant parens,
  whitespace, sugar), and `default` is the canonical one.

## The chain

```
IsoParser  ─toLossyParser─▶  LossyParser  ─toAbstraction─▶  Abstraction
```

* `IsoParser.toLossyParser`: the annotation family is the **fiber of `print`** — over `b : v` sit
  all sources printing to `b`. The split model deliberately stores no value→source section, so the
  functor asks for one (`canon`/`hcanon`) to serve as `default`; for an **aligned** parser whose
  printer echoes its source (`w = v`, `(print a).1 = a` — e.g. the mixfix parser) it is free
  (`toLossyParserAligned`).
* `LossyParser.toAbstraction`: whole-input use — `abstract` runs the parser and demands an empty
  leftover, `realize` is `print`, and `abstract_realize` is the terminal round-trip (`rest = []`,
  where the FOLLOW guard is vacuous). No side conditions.
* `Exact` transfers to `Lossless` (`Exact.lossless`): a parser that consumes only printable
  material yields a reconstruction-complete abstraction. Like `Lossless`, `Exact` is a
  *predicate*, not a field — proving it is the per-parser exactness induction (the `exact_all`
  pattern), and elaborator-like stages won't have it.

FIRST/FOLLOW and progress-in-the-type are kept verbatim from `IsoParser`, so the free theorems
(`run_nil`, `print_ne_nil`) and the combinator style port unchanged; a combinator layer over
`LossyParser` (the `parens`-style lossy combinators, generically) can come later.

(On the name: `LossyParser` is provisional — `AnnotatedParser` would also fit. Renaming is
mechanical; nothing downstream depends on the word.)
-/

-- `p.toLossyParser` dot-notation forces declarations under `LambdaLab.Parser.IsoParser.IsoParser`,
-- which this linter dislikes; the repetition is inherited from IsoParser's own naming.
set_option linter.dupNamespace false

namespace LambdaLab.Parser.LossyParser

open LambdaLab.Parser.IsoParser (HeadIn HeadIn_nil IsoParser run_eq_some)
open LambdaLab.Abstraction (Abstraction)

variable {α : Type} {fst fol : α → Prop} {w v V : Type} {Ann : V → Type}

/-- A consuming parser that may *forget* surface detail: parse a value with a strictly-shorter
leftover; print any **annotated** value — the annotation `Ann v` selects which surface spelling of
`v` to emit, `default` the canonical one. The round-trip law `ok` is indexed: printing an
annotation of `v` and reparsing recovers `v` itself. -/
structure LossyParser (α : Type) (fst fol : α → Prop) (V : Type) (Ann : V → Type) where
  /-- Parse a prefix into a value and a strictly shorter leftover. -/
  parse : (input : List α) → Option (V × { r : List α // r.length < input.length })
  /-- Print one surface spelling of `v`, chosen by the annotation. -/
  print : ∀ {v : V}, Ann v → List α
  /-- The canonical spelling. -/
  default : ∀ {v : V}, Ann v
  /-- FIRST is sound: outside it, the parse fails. -/
  firstOk : ∀ c rest, ¬ fst c → parse (c :: rest) = none
  /-- **The law**, in erased form: print any annotation of `v`, parse with a FOLLOW-admissible
  continuation — recover `v`, continuation untouched. -/
  ok : ∀ (v : V) (ann : Ann v) (rest : List α), HeadIn fol rest →
    (parse (print ann ++ rest)).map (fun z => (z.1, z.2.val)) = some (v, rest)

namespace LossyParser

/-- The parse result with the progress proof erased. -/
def run (p : LossyParser α fst fol V Ann) (input : List α) : Option (V × List α) :=
  (p.parse input).map (fun z => (z.1, z.2.val))

/-- **The terminal round-trip** — at end of input the FOLLOW guard is vacuous. -/
theorem roundtrip (p : LossyParser α fst fol V Ann) (v : V) (ann : Ann v) :
    p.run (p.print ann) = some (v, []) := by
  have h := p.ok v ann [] (HeadIn_nil _)
  rw [List.append_nil] at h
  exact h

/-! ## `LossyParser → Abstraction` -/

/-- Whole-input use of a lossy parser: the canonical `Abs` morphism. `abstract` demands an empty
leftover; `realize` is `print`; the law is the terminal round-trip. -/
def toAbstraction (p : LossyParser α fst fol V Ann) : Abstraction (List α) V Ann where
  abstract cs := (p.run cs).bind fun z => if z.2.isEmpty then some z.1 else none
  realize := p.print
  default := p.default
  abstract_realize v ann := by
    show (p.run (p.print ann)).bind (fun z => if z.2.isEmpty then some z.1 else none) = some v
    rw [p.roundtrip v ann]
    rfl

/-! ## Exactness, and its transfer to `Lossless` -/

/-- The parser consumes only printable material: whatever `run` accepted is the print of some
annotation of the result. The parser-level counterpart of `Abstraction.Lossless` — and like it, a
*property*, not structure. -/
def Exact (p : LossyParser α fst fol V Ann) : Prop :=
  ∀ (cs : List α) (v : V) (rest : List α),
    p.run cs = some (v, rest) → ∃ ann : Ann v, p.print ann ++ rest = cs

/-- An exact lossy parser yields a lossless abstraction. -/
theorem Exact.lossless {p : LossyParser α fst fol V Ann} (hp : p.Exact) :
    p.toAbstraction.Lossless := by
  intro cs v h
  have h' : (p.run cs).bind (fun z => if z.2.isEmpty then some z.1 else none) = some v := h
  cases hrun : p.run cs with
  | none => rw [hrun] at h'; simp at h'
  | some z =>
      obtain ⟨v', rest⟩ := z
      rw [hrun] at h'
      have h'' : (if rest.isEmpty then some v' else none) = some v := h'
      split at h''
      · next hemp =>
          have hrest : rest = [] := by simpa using hemp
          subst hrest
          have hv : v' = v := Option.some.inj h''
          obtain ⟨ann, hann⟩ := hp cs v' [] hrun
          exact hv ▸ (⟨ann, by simpa using hann⟩ :
            ∃ ann : Ann v', p.toAbstraction.realize ann = cs)
      · exact absurd h'' (by simp)

/-- A `LossyParser` as an `IsoParser` whose source is the **annotated values** `Σ v, Ann v`.
`print₁` is the index — definitionally — which is what makes `echo` proofs of composites built
from converted parsers reduce to `rfl`/eta. Round trip with `toLossyParserSigma` to run the
existing `IsoParser` combinators (`gdo`, `many1`, …) over lossy components. -/
def toIsoParser (p : LossyParser α fst fol V Ann) :
    IsoParser α fst fol (Σ v : V, Ann v) V where
  parse := p.parse
  print s := (s.1, p.print s.2)
  firstOk := p.firstOk
  ok s rest h := p.ok s.1 s.2 rest h

end LossyParser

/-! ## `IsoParser → LossyParser` -/

/-- Convert back from a `Σ`-source `IsoParser` (the shape `toIsoParser` and combinators over it
produce): if the printed value is the index (`echo`), the family is a genuine annotation family.
This keeps the *pretty* family — unlike the fiber of `toLossyParser`. -/
def _root_.LambdaLab.Parser.IsoParser.IsoParser.toLossyParserSigma {Ann : V → Type}
    (p : IsoParser α fst fol (Σ v : V, Ann v) V) (dflt : ∀ {v : V}, Ann v)
    (echo : ∀ s : Σ v : V, Ann v, (p.print s).1 = s.1) :
    LossyParser α fst fol V Ann where
  parse := p.parse
  print {v} ann := (p.print ⟨v, ann⟩).2
  default := dflt
  firstOk := p.firstOk
  ok v ann rest h := by
    have hk := p.ok ⟨v, ann⟩ rest h
    rwa [echo ⟨v, ann⟩] at hk

/-- An aligned parser whose printer echoes its source, as a `LossyParser` with **trivial**
annotation — the embedding of canonical-form-only (lossless) languages into the lossy interface.
(The generalization to a *lossy* projection into a custom type is `IsoParser.truncate`, in
`Parser/Truncation.lean`.) -/
def _root_.LambdaLab.Parser.IsoParser.IsoParser.toLossyParserUnit (p : IsoParser α fst fol v v)
    (echo : ∀ a : v, (p.print a).1 = a) :
    LossyParser α fst fol v (fun _ => Unit) where
  parse := p.parse
  print {b} _ := (p.print b).2
  default := ()
  firstOk := p.firstOk
  ok b _ rest h := by
    have hk := p.ok b rest h
    rwa [echo b] at hk

/-- An `IsoParser` as a `LossyParser`: the annotation family over `b` is the **fiber of `print`**
— every source that prints to `b`. The split model stores no value→source section, so the
canonical annotation is the one datum to supply: `canon` with `hcanon`. -/
def _root_.LambdaLab.Parser.IsoParser.IsoParser.toLossyParser (p : IsoParser α fst fol w v)
    (canon : v → w) (hcanon : ∀ b : v, (p.print (canon b)).1 = b) :
    LossyParser α fst fol v (fun b => { a : w // (p.print a).1 = b }) where
  parse := p.parse
  print ann := (p.print ann.1).2
  default {b} := ⟨canon b, hcanon b⟩
  firstOk := p.firstOk
  ok := fun b ann rest hrest => by
    have h := p.ok ann.1 rest hrest
    rw [ann.2] at h
    exact h

/-- The aligned case (`w = v`, printer echoes its source — e.g. mixfix): the section is `id`,
so the `LossyParser` is free. -/
def _root_.LambdaLab.Parser.IsoParser.IsoParser.toLossyParserAligned (p : IsoParser α fst fol v v)
    (echo : ∀ a : v, (p.print a).1 = a) :
    LossyParser α fst fol v (fun b => { a : v // (p.print a).1 = b }) :=
  p.toLossyParser id echo

end LambdaLab.Parser.LossyParser
