import LambdaLab.Abstraction2.Basic
import LambdaLab.CBiparser.Basic

/-!
# Every `CBiparser` is a morphism of `Abs`

A `CBiparser α w v` carries `print : w → v × List α` — a source `s : w` prints to a token string
`(print s).2`. That printing is a total map `w → List α`, and it is *lossy*: it forgets the grouping
/ structure of `s`, keeping only the flat token sequence. So it is an `Abs` `abstract` map, and the
annotation over a token string is **the sources that print to it** (the parse trees).

Concretely, both the tokenizer and any parser abstract **down to a token string**:

```
    List Char  ──tokens──▶  List Token  ◀──print──  w  (Expr, …)
     (gaps)                                        (grouping)
```

`abstract = (print ·).2`, `realize` hands back the source, and `default` is a canonical source for a
token string — *the* one when printing is injective (an unambiguous grammar), so `realize` is then a
bijection onto its image.

The abstract objects are the **printable** token strings (`∃ s, (print s).2 = t`), which is exactly
what makes `default` total: a token string that is no source's printout has no annotation. That is
the partiality of parsing, pushed honestly into the abstract type.
-/

namespace LambdaLab.Abstraction2

open Classical LambdaLab.CBiparser

/-- The abstraction induced by any flattening `flatten : Tree → List Tok`: the annotation over a
token sequence is the fibre of `flatten` (its parse trees). -/
noncomputable def flattenAbstraction {Tree Tok : Type} (flatten : Tree → List Tok) :
    Abstraction Tree { bs : List Tok // ∃ t, flatten t = bs }
      (fun s => { t : Tree // flatten t = s.val }) where
  abstract := fun t => ⟨flatten t, t, rfl⟩
  realize := fun x => x.val
  default := fun {s} => ⟨choose s.2, choose_spec s.2⟩
  abstract_realize := fun _ x => Subtype.ext x.2
  realize_complete := fun t => ⟨⟨t, rfl⟩, rfl⟩

/-- **Every `CBiparser` is an `Abs` morphism.** Its `print`-token map `s ↦ (print s).2` is the
lossy `abstract`; the annotation over a token string is the sources that print to it. -/
noncomputable def _root_.LambdaLab.CBiparser.CBiparser.toAbstraction
    {α w v : Type} (p : CBiparser α w v) :
    Abstraction w { t : List α // ∃ s, (p.print s).2 = t }
      (fun t => { s : w // (p.print s).2 = t.val }) :=
  flattenAbstraction (fun s => (p.print s).2)

end LambdaLab.Abstraction2
